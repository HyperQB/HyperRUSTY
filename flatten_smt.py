#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# Flatten a Yosys SMT-LIBv2 file by:
#   1) Removing the state datatype usage (no record-typed 'state').
#   2) Declaring constants for each state field.
#   3) Defining ONE transition function per state field, fully inlined
#      (all helper define-funs F(state) are inlined into the next functions).
#   4) Defining zero-arity |init <FIELD>| functions ONLY for fields constrained
#      by |<top>_i|, with the exact literal extracted (e.g., #b1, #b0101).
#   5) No helper constants and NO (assert ...) are emitted.
#
# Usage:
#   python yosys_smt2_flatten_inline.py input.smt2 output.smt2

import sys
from typing import List, Tuple, Dict, Any, Optional, Set
from dataclasses import dataclass, field as dataclass_field
from pathlib import Path

Token = str
SExpr = Any  # Union[str, List['SExpr']]

# ------------------ basic SMT-LIB parsing ------------------

def strip_comments(text: str) -> str:
    out_lines = []
    for line in text.splitlines():
        if ';' in line:
            line = line.split(';', 1)[0]
        out_lines.append(line)
    return "\n".join(out_lines)

def tokenize(text: str) -> List[Token]:
    tokens: List[str] = []
    i = 0
    n = len(text)
    WS = " \t\r\n"
    while i < n:
        c = text[i]
        if c in WS:
            i += 1; continue
        if c in "()":
            tokens.append(c); i += 1; continue
        if c == '|':
            j = i + 1
            while j < n and text[j] != '|':
                j += 1
            if j >= n:
                raise ValueError("Unterminated |...| symbol")
            tokens.append(text[i:j+1]); i = j + 1; continue
        j = i
        while j < n and text[j] not in WS + '()':
            j += 1
        tokens.append(text[i:j]); i = j
    return tokens

def parse_sexprs(tokens: List[Token]) -> List[SExpr]:
    i = 0
    def parse_one() -> SExpr:
        nonlocal i
        if i >= len(tokens):
            raise ValueError("Unexpected EOF")
        t = tokens[i]; i += 1
        if t == '(':
            lst: List[SExpr] = []
            while True:
                if i >= len(tokens):
                    raise ValueError("Unmatched '('")
                if tokens[i] == ')':
                    i += 1; break
                lst.append(parse_one())
            return lst
        if t == ')':
            raise ValueError("Unexpected ')'")
        return t
    out: List[SExpr] = []
    while i < len(tokens):
        out.append(parse_one())
    return out

def sexpr_to_str(x: SExpr) -> str:
    if isinstance(x, list):
        return "(" + " ".join(sexpr_to_str(e) for e in x) + ")"
    return x

# ------------------ small IR ------------------

@dataclass
class Sort:
    ast: SExpr
    def __str__(self) -> str:
        return sexpr_to_str(self.ast)

@dataclass
class FunDef:
    name: str
    params: List[Tuple[str, Sort]]
    ret: Sort
    body: SExpr

@dataclass
class ModuleState:
    sort_symbol: str
    ctor: str
    fields: List[Tuple[str, Sort]]   # [(field_name, Sort), ...]

@dataclass
class ModelIR:
    module: Optional[ModuleState] = None
    funs: Dict[str, FunDef] = dataclass_field(default_factory=dict)

# ------------------ parse helpers ------------------

def parse_sort(ast: SExpr) -> Sort:
    return Sort(ast=ast)

def parse_fun_def(ast: SExpr) -> FunDef:
    assert isinstance(ast, list) and len(ast) >= 5 and ast[0] == 'define-fun'
    name = ast[1]
    params_ast = ast[2]
    ret_sort_ast = ast[3]
    body = ast[4]
    params: List[Tuple[str, Sort]] = []
    for p in params_ast:
        assert isinstance(p, list) and len(p) == 2
        params.append((p[0], parse_sort(p[1])))
    return FunDef(name=name, params=params, ret=parse_sort(ret_sort_ast), body=body)

def parse_declare_datatype(ast: SExpr) -> ModuleState:
    assert isinstance(ast, list) and ast[0] == 'declare-datatype'
    sort_symbol = ast[1]
    ctors = ast[2]
    assert isinstance(ctors, list) and len(ctors) == 1
    ctor = ctors[0]
    ctor_name = ctor[0]
    fields_raw = ctor[1:]
    fields: List[Tuple[str, Sort]] = []
    for f in fields_raw:
        assert isinstance(f, list) and len(f) == 2
        fields.append((f[0], parse_sort(f[1])))
    return ModuleState(sort_symbol=sort_symbol, ctor=ctor_name, fields=fields)

def load_model_ir(text: str) -> ModelIR:
    stripped = strip_comments(text)
    tokens = tokenize(stripped)
    sexprs = parse_sexprs(tokens)
    ir = ModelIR()
    for node in sexprs:
        if isinstance(node, list) and node:
            tag = node[0]
            if tag == 'declare-datatype':
                ir.module = parse_declare_datatype(node)
            elif tag == 'define-fun':
                fdef = parse_fun_def(node)
                ir.funs[fdef.name] = fdef
    return ir

# ------------------ transform core ------------------

def find_transition_fun(ir: ModelIR) -> Optional[FunDef]:
    if not ir.module:
        return None
    state_sort = ir.module.sort_symbol
    for f in ir.funs.values():
        if f.name.endswith('_t') and len(f.params) == 2:
            if f.params[0][1].ast == state_sort and f.params[1][1].ast == state_sort:
                return f
    for f in ir.funs.values():
        if len(f.params) == 2 and f.params[0][1].ast == state_sort and f.params[1][1].ast == state_sort:
            return f
    return None

def find_init_fun(ir: ModelIR) -> Optional[FunDef]:
    if not ir.module:
        return None
    state_sort = ir.module.sort_symbol
    for f in ir.funs.values():
        if f.name.endswith('_i|') and len(f.params) == 1 and f.params[0][1].ast == state_sort:
            return f
    return None

def flatten_and(expr: SExpr) -> List[SExpr]:
    if isinstance(expr, list) and expr and expr[0] == 'and':
        out: List[SExpr] = []
        for e in expr[1:]:
            out.extend(flatten_and(e))
        return out
    return [expr]

def collect_assignments_from_t(f_t: FunDef, module: ModuleState) -> Dict[str, SExpr]:
    """Extract equalities of the form (= <lhs_expr state> (|FIELD| next_state))."""
    next_var = f_t.params[1][0]
    body = f_t.body
    conjuncts = flatten_and(body)
    rhs_selectors = {f for (f, _) in module.fields}
    mapping: Dict[str, SExpr] = {}
    for c in conjuncts:
        if isinstance(c, list) and len(c) == 3 and c[0] == '=':
            lhs, rhs = c[1], c[2]
            if isinstance(rhs, list) and len(rhs) == 2 and isinstance(rhs[0], str) and rhs[0] in rhs_selectors and rhs[1] == next_var:
                mapping[rhs[0]] = lhs
    return mapping

def rewrite_expr_inline(ir: ModelIR, module: ModuleState, expr: SExpr, state_var: str) -> SExpr:
    """
    Fully inline (F state) where F is a helper define-fun with exactly one (state) param,
    and replace (|FIELD| state) with |FIELD|.
    """
    selector_names = {f for (f, _) in module.fields}
    helpers = {name: f for name, f in ir.funs.items()
               if len(f.params) == 1 and f.params[0][1].ast == module.sort_symbol}
    cache: Dict[str, SExpr] = {}

    def rewrite_with_state(e: SExpr, s_var: str) -> SExpr:
        if isinstance(e, list):
            # (|FIELD| s_var) -> |FIELD|
            if len(e) == 2 and isinstance(e[0], str) and e[0] in selector_names and e[1] == s_var:
                return e[0]
            # (F s_var) -> inline body
            if len(e) == 2 and isinstance(e[0], str) and e[0] in helpers and e[1] == s_var:
                fname = e[0]
                if fname in cache:
                    return cache[fname]
                fdef = helpers[fname]
                param_name = fdef.params[0][0]
                inlined = rewrite_with_state(fdef.body, param_name)
                cache[fname] = inlined
                return inlined
            return [rewrite_with_state(a, s_var) for a in e]
        return e

    return rewrite_with_state(expr, state_var)

def render_sort(s: Sort) -> str:
    return str(s)

def render_decl_const(name: str, sort: Sort) -> str:
    return f"(declare-const {name} {render_sort(sort)})"

def render_define_fun(name: str, params: List[Tuple[str, Sort]], ret: Sort, body: SExpr) -> str:
    ps = " ".join(f"({pn} {render_sort(psort)})" for pn, psort in params)
    return f"(define-fun {name} ({ps}) {render_sort(ret)} {sexpr_to_str(body)})"

# ---------- init extraction ----------

def sort_is_bv1(s: Sort) -> bool:
    return isinstance(s.ast, list) and len(s.ast) == 3 and s.ast[0] == '_' and s.ast[1] == 'BitVec' and s.ast[2] == '1'

def _is_true(x: SExpr) -> bool:  return x == 'true'
def _is_false(x: SExpr) -> bool: return x == 'false'

def _as_eq(x: SExpr) -> Optional[Tuple[SExpr, SExpr]]:
    return (x[1], x[2]) if (isinstance(x, list) and len(x) == 3 and x[0] == '=') else None

def _extract00_field(term: SExpr) -> Optional[str]:
    """
    Match ((_ extract 0 0) |FIELD|) after inlining selectors.
    Our parser produces: [ ['(_','extract','0','0'], '|FIELD|' ]
    """
    if not (isinstance(term, list) and len(term) == 2):
        return None
    head, arg = term[0], term[1]
    if not (isinstance(head, list) and len(head) >= 4 and (head[0] == '(_' or head[0] == '_') and head[1] == 'extract'
            and head[2] == '0' and head[3] == '0'):
        return None
    return arg if isinstance(arg, str) else None

def _bv1_from_bool_constraint(inner_eq: SExpr, truth: bool) -> Optional[Tuple[str, str]]:
    """
    inner_eq is (= ((extract 0 0) FIELD) #b1)  or swapped (#b0/#b1).
    'truth' is True for (= inner_eq true), False for (= inner_eq false).
    Returns (FIELD, '#b1' or '#b0'), the actual bit value implied for FIELD.
    """
    pair = _as_eq(inner_eq)
    if not pair:
        return None
    a, b = pair

    field, bit = None, None
    # Case 1: (= ((_ extract 0 0) FIELD) #b{0,1})
    if _extract00_field(a) is not None and isinstance(b, str) and b in ('#b0', '#b1'):
        field, bit = _extract00_field(a), b
    # Case 2: (= #b{0,1} ((_ extract 0 0) FIELD))
    elif _extract00_field(b) is not None and isinstance(a, str) and a in ('#b0', '#b1'):
        field, bit = _extract00_field(b), a
    else:
        return None

    want_one = (bit == '#b1')
    final = '#b1' if (want_one == truth) else '#b0'
    return (field, final)

def extract_init_values(ir: ModelIR, module: ModuleState, init_fun: FunDef) -> Dict[str, SExpr]:
    """
    Extract literals for each field from |<top>_i|.
    Handles:
      - (= (|FIELD| state) LIT) and (= LIT (|FIELD| state))
      - (= (= ((_ extract 0 0) (|FIELD| state)) #b{0,1}) true/false) and all swaps
    """
    state_var = init_fun.params[0][0]
    # 1) inline helpers + selectors so (|FIELD| state) -> |FIELD|
    inlined = rewrite_expr_inline(ir, module, init_fun.body, state_var)

    # 2) flatten (and ...)
    def _flatten_and(e: SExpr) -> List[SExpr]:
        if isinstance(e, list) and e and e[0] == 'and':
            out: List[SExpr] = []
            for sub in e[1:]:
                out.extend(_flatten_and(sub))
            return out
        return [e]
    conjuncts = _flatten_and(inlined)

    field_sorts: Dict[str, Sort] = {fname: s for (fname, s) in module.fields}
    def _is_bv1(s: Sort) -> bool:
        return isinstance(s.ast, list) and len(s.ast) == 3 and s.ast[0] == '_' and s.ast[1] == 'BitVec' and s.ast[2] == '1'

    values: Dict[str, SExpr] = {}

    for c in conjuncts:
        eq = _as_eq(c)
        if not eq:
            continue
        a, b = eq

        # Direct equalities: (= |FIELD| LIT) or swapped
        if isinstance(a, str) and a in field_sorts:
            values.setdefault(a, b)
            continue
        if isinstance(b, str) and b in field_sorts:
            values.setdefault(b, a)
            continue

        # Booleanized BV1: (= ( (= ((_ extract 0 0) |FIELD|) #b1/#b0) ) true/false) or swapped
        # Normalize to (inner_eq, truth_bool)
        inner, truth_bool = None, None
        if _is_true(a) or _is_false(a):
            inner, truth_bool = b, _is_true(a)
        elif _is_true(b) or _is_false(b):
            inner, truth_bool = a, _is_true(b)

        if inner is not None:
            decoded = _bv1_from_bool_constraint(inner, truth_bool)
            if decoded is not None:
                fld, lit = decoded
                if fld in field_sorts and _is_bv1(field_sorts[fld]):
                    values.setdefault(fld, lit)

    return values


# ------------------ main transform ------------------

def transform(text: str) -> str:
    ir = load_model_ir(text)
    if not ir.module:
        raise ValueError("No module/state datatype found.")
    module = ir.module
    f_t = find_transition_fun(ir)
    if not f_t:
        raise ValueError("No transition function with (state next_state) params found.")

    next_map = collect_assignments_from_t(f_t, module)
    state_param_name = f_t.params[0][0]

    f_i = find_init_fun(ir)
    init_values: Dict[str, SExpr] = {}
    if f_i is not None:
        init_values = extract_init_values(ir, module, f_i)

    out_lines: List[str] = []
    out_lines.append("; Flattened SMT-LIB (inline mode): no helper consts and no assertions.")
    out_lines.append("; Declares base state consts, defines per-field next functions (inline),")
    out_lines.append("; and per-field init functions inferred from |<top>_i| where possible.\n")

    # State field constants
    out_lines.append("; --- State field constants ---")
    for (fname, sort) in module.fields:
        out_lines.append(render_decl_const(fname, sort))
    out_lines.append("")

    # Per-field next functions
    params_all = [(fname, sort) for (fname, sort) in module.fields]
    out_lines.append("; --- Per-field transition functions (fully inlined) ---")
    for (field_name, field_sort) in module.fields:
        if field_name not in next_map:
            continue
        raw_expr = next_map[field_name]
        inlined = rewrite_expr_inline(ir, module, raw_expr, state_param_name)
        fun_name = f"|next {field_name.strip('|')}|" if field_name.startswith('|') else f"next_{field_name}"
        out_lines.append(render_define_fun(fun_name, params_all, field_sort, inlined))
    out_lines.append("")

    # Per-field init functions (only when determinable)
    out_lines.append("; --- Per-field initial value functions (only for constrained fields) ---")
    for (field_name, field_sort) in module.fields:
        if field_name in init_values:
            fname = f"|init {field_name.strip('|')}|" if field_name.startswith('|') else f"init_{field_name}"
            body = init_values[field_name]
            out_lines.append(render_define_fun(fname, [], field_sort, body))
    out_lines.append("")

    return "\n".join(out_lines)

# ------------------ CLI ------------------

def flatten_file(in_path: Path, out_path: Path):
    text = in_path.read_text()
    out = transform(text)
    out_path.write_text(out)

def main():
    #if len(sys.argv) != 2 and len(sys.argv) != 3:
        #print("Usage: python yosys_smt2_flatten_inline.py input.smt2 [output.smt2]")
        #sys.exit(2)
    #in_path = Path(sys.argv[1])
    #out_path = Path(sys.argv[2]) if len(sys.argv) == 3 else in_path.with_suffix(".flattened.smt2")
    in_path = Path("fpu_small_tb_unrolled.smt2")
    out_path = Path("python_test.smt2")
    flatten_file(in_path, out_path)
    print(f"Wrote {out_path}")

if __name__ == "__main__":
    main()
