import re
import sys
from pathlib import Path

src = Path(sys.argv[1]).read_text()

# --- helpers --------------------------------------------------------------

def strip_comments(s):
    # remove “-- ...” to end of line (keep code layout)
    return re.sub(r'--.*$', '', s, flags=re.MULTILINE)

def find_module(name, text):
    pat = re.compile(rf'(?ms)MODULE\s+{re.escape(name)}\s*\((.*?)\)\s*(.*?)\n(?=MODULE|\Z)')
    m = pat.search(text)
    if not m:
        # try module without parameter list
        pat2 = re.compile(rf'(?ms)MODULE\s+{re.escape(name)}\s*(.*?)\n(?=MODULE|\Z)')
        m2 = pat2.search(text)
        if not m2:
            raise ValueError(f"Module {name} not found.")
        return [], m2.group(1)
    params = [p.strip() for p in m.group(1).split(',')] if m.group(1).strip() else []
    body = m.group(2)
    return params, body

def extract_block(tag, body):
    # Extracts a top-level TAG block (VAR/ASSIGN/DEFINE) with balanced "case ... esac;"
    rgx = re.compile(rf'(?ms)^{tag}\s*(.*?)(?=^\w|\Z)', re.MULTILINE)
    m = rgx.search(body)
    return (m.group(1).strip() if m else "")

def parse_instance(line):
    # e.g.  proc1: programs(ID_one, SCHEDULE, LOCKED, in_HIGH, 1);
    m = re.search(r'^\s*(\w+)\s*:\s*(\w+)\s*\((.*?)\)\s*;', line)
    if not m: return None
    inst, mod, arglist = m.group(1), m.group(2), m.group(3)
    args = [a.strip() for a in split_args(arglist)]
    return inst, mod, args

def split_args(s):
    # split by commas not inside braces
    out, cur, depth = [], [], 0
    for ch in s:
        if ch == '{': depth += 1
        elif ch == '}': depth = max(0, depth-1)
        if ch == ',' and depth == 0:
            out.append(''.join(cur).strip()); cur=[]
        else:
            cur.append(ch)
    if cur: out.append(''.join(cur).strip())
    return out

def prefix_locals(var_block, prefix):
    # rename "name : type;" to "prefix_name : type;"
    def repl(m):
        name, typ = m.group(1), m.group(2)
        return f"    {prefix}{name} : {typ};"
    return re.sub(r'(?m)^\s*([\w\[\].]+)\s*:\s*([^;]+);', repl, var_block)

def rewrite_assign_block(assign_block, prefix, param_map):
    # 1) prefix LHS variables from this module
    # 2) substitute parameters on RHS
    # 3) prefix module-local names on RHS too
    b = assign_block

    # detect all local identifiers from the (already prefixed) VAR names we’ll feed later
    # but here we just prefix LHS "init(name)" / "next(name)"
    def lhs_pref(m):
        kind, name, rest = m.group(1), m.group(2), m.group(3)
        return f"{kind}({prefix}{name}){rest}"
    b = re.sub(r'\b(init|next)\s*\(\s*([\w\[\].]+)\s*\)(\s*:?=)', lhs_pref, b)

    # parameter substitution (tokens only)
    for p, a in param_map.items():
        # replace whole-word p with a (avoid touching prefixed names)
        b = re.sub(rf'\b{re.escape(p)}\b', a, b)

    # prefix bare local names on RHS (heuristic: names that appeared as local vars)
    # We will collect local names from VAR block outside and pass in
    return b

def tokenize_var_names(var_block):
    return [m.group(1) for m in re.finditer(r'(?m)^\s*([\w\[\].]+)\s*:\s*[^;]+;', var_block)]

def prefix_rhs_locals(text, local_names, prefix):
    # Prefix occurrences of local names in RHS (avoid LHS 'init(next(prefix...' we already did)
    # We’ll match as whole-word tokens not followed by '(' after init/next.
    for name in sorted(local_names, key=len, reverse=True):
        text = re.sub(rf'(?<!\w){re.escape(name)}(?![\w\[])', f'{prefix}{name}', text)
    return text

def replace_proc_refs_in_main(main_text):
    # Replace "proc1.x" -> "proc1_x" etc. in the entire main module
    main_text = re.sub(r'\bproc1\.([A-Za-z_]\w*)', r'proc1_\1', main_text)
    main_text = re.sub(r'\bproc2\.([A-Za-z_]\w*)', r'proc2_\1', main_text)
    return main_text

# --- find main and instances ---------------------------------------------

clean = strip_comments(src)

m_main = re.search(r'(?ms)MODULE\s+main\s*(.*?)\n(?=MODULE|\Z)', clean)
if not m_main:
    print(src)  # just pass through
    sys.exit(0)

main_body = m_main.group(1)

# find instance lines inside main VAR block
main_var_block = extract_block("VAR", main_body)
inst_lines = [ln for ln in main_var_block.splitlines() if ':' in ln and '(' in ln and ')' in ln and ';' in ln]

instances = []
for ln in inst_lines:
    parsed = parse_instance(ln)
    if parsed:
        instances.append(parsed)

# Expect two: proc1 and proc2
insts = {inst: (mod, args) for inst, mod, args in instances if inst in ("proc1","proc2")}
if not insts:
    print(src)  # nothing to do
    sys.exit(0)

# Choose module name from the instances
modname = list(insts.values())[0][0]
params, mod_body = find_module(modname, clean)
var_block   = extract_block("VAR",    mod_body)
assign_block= extract_block("ASSIGN", mod_body)
define_block= extract_block("DEFINE", mod_body)

local_names = tokenize_var_names(var_block)

# Build flattened declarations for each instance
flat_decl = []
flat_assign = []
flat_define = []

for inst in ("proc1","proc2"):
    mod, args = insts[inst]
    prefix = f"{inst}_"

    if len(args) != len(params):
        # Parameter arity mismatch; we’ll still try positional mapping
        pass
    param_map = {p: args[i] for i, p in enumerate(params)}

    # Declarations
    vb_pref = prefix_locals(var_block, prefix)
    flat_decl.append(f"    -- {inst}: {modname}({', '.join(args)})\n" + vb_pref)

    # Assign
    ab = assign_block
    # LHS prefixing + parameter substitution
    ab = rewrite_assign_block(ab, prefix, param_map)
    # RHS local prefixing
    ab = prefix_rhs_locals(ab, local_names, prefix)
    # Cosmetic indentation
    ab = re.sub(r'(?m)^(?=\S)', '    ', ab)
    flat_assign.append(f"    -- {inst}\n{ab}")

    # DEFINE
    if define_block:
        db = define_block
        for p,a in param_map.items():
            db = re.sub(rf'\b{re.escape(p)}\b', a, db)
        db = prefix_rhs_locals(db, local_names, prefix)
        db = re.sub(r'(?m)^\s*([\w\[\].]+)\s*:=', rf'    {prefix}\1 :=', db)
        flat_define.append(f"    -- {inst}\n{db.strip()}")

# Rebuild main: remove instance lines, insert prefixed VARs
main_var_noinst = []
for ln in main_var_block.splitlines():
    if parse_instance(ln):  # skip instance line
        continue
    main_var_noinst.append(ln)
main_var_new = "\n".join(main_var_noinst + [""] + flat_decl)

# Replace blocks inside main body
def replace_block(tag, body, newblock):
    pat = re.compile(rf'(?ms)^{tag}\s*(.*?)(?=^\w|\Z)', re.MULTILINE)
    return pat.sub(f"{tag}\n{newblock}\n", body, count=1) if pat.search(body) else body + f"\n{tag}\n{newblock}\n"

main_new = replace_block("VAR",    main_body, main_var_new)
main_new = replace_block("ASSIGN", main_new,  "\n\n".join(flat_assign))
if define_block:
    main_new = replace_block("DEFINE", main_new, "\n".join(flat_define))

# Replace proc1.x/ proc2.x references in the rest of main
main_new = replace_proc_refs_in_main(main_new)

# Stitch the whole file back: replace old main with new main
out = clean.replace(main_body, main_new)

print(out)