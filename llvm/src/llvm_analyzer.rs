use llvm_ir::Module;
use indexmap::IndexMap;
use llvm_ir::instruction::Instruction;
use llvm_ir::types::Type;
use llvm_ir::constant::Constant;
use llvm_ir::operand::Operand;
use llvm_ir::terminator::Terminator;
use llvm_ir::predicates::IntPredicate;
use llvm_ir::name::Name;
use llvm_ir::Name::Number;
use std::collections::{BTreeMap, BTreeSet};
use ir;
use std::fs;
use std::path::Path;

// Variables reference type
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub enum TypeRef {
    IntegerType(u32), // Only integers are supported for now
    BoolType(u32), // The width of operands being compared
}

// Variable definition
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct VarRef {
    pub name: String,
    pub type_ref: TypeRef,
    pub initial: Option<u64> // Generally Incorrect
}

// UpdateType of the transition
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub enum UpdateType {
    ConstantUpdate(u64),
    VariableUpdate(String),
    ComparisonUpdate {
        operator: String,
        lhs: String,
        rhs: String,
    }
}

/// A single per-variable transition from one program counter (pc) to another.
/// - `from_pc` and `to_pc` are instruction indices (0..n)
/// - `var` is the variable name
/// - `upd` is the update expression of the variable
#[derive(Debug, Clone)]
pub struct VarTransition {
    pub from_pc: usize,
    pub to_pc: usize,
    pub var: String,
    pub cond: Option<(String, bool)>, // This could generally yield wrong results
    pub upd: UpdateType,
}

pub fn name_to_string(n: &Name) -> String {
    format!("{}", n) // Name implements Display
}

pub fn operand_to_string(op: &Operand) -> String {
    format!("{}", op)
}

/// Parse IR from a file path and return the llvm_ir::Module.
pub fn load_module_from_path<P: AsRef<Path>>(p: P) -> Result<Module, String> {
    Module::from_ir_path(p).map_err(|e| format!("failed to parse IR: {}", e))
}

/// Build a flattened list of (function, basic block, instruction or terminator)
/// and assign a consecutive PC index to each instruction and each terminator.
///
/// Returns:
///  - instr_list: Vec<(func_name, bb_name, is_terminator, instr_display_string)>
///  - map_bb_start_pc: map from (func_name, bb_name) -> pc of block entry (first instr's pc)
pub fn flatten_instructions(m: &Module) -> (
    Vec<(String, String, bool, String)>,
    BTreeMap<(String, String), usize>,
) {
    let mut instr_list = Vec::new();
    let mut map_bb_start_pc = BTreeMap::new();

    for func in &m.functions {
        let fname = func.name.clone();
        for bb in &func.basic_blocks {
            let bbname = format!("{}", bb.name);

            // record start pc as soon as first instruction (non-terminator) is encountered
            let mut first_seen = None;
            for inst in &bb.instrs {
                let display = format!("{}", inst);
                if first_seen.is_none() {
                    first_seen = Some(instr_list.len());
                    map_bb_start_pc.insert((fname.clone(), bbname.clone()), instr_list.len());
                }
                instr_list.push((fname.clone(), bbname.clone(), false, display));
            }
            // term is always present; give it a PC too
            let term_display = format!("{}", bb.term);
            if first_seen.is_none() {
                // block had zero non-terminator instructions: block entry is the terminator PC
                map_bb_start_pc.insert((fname.clone(), bbname.clone()), instr_list.len());
            }
            instr_list.push((fname.clone(), bbname.clone(), true, term_display));
        }
    }
    (instr_list, map_bb_start_pc)
}

/// Collect variables conservatively:
pub fn collect_vars(m: &Module) -> IndexMap<String, VarRef> {
    let mut vars = IndexMap::new();
    let mut var_initialized : IndexMap<String, bool> = IndexMap::new();

    for func in &m.functions {
        for bb in &func.basic_blocks {
            // non-terminators
            for inst in &bb.instrs {
                // If the variable returns a result, the result is a new variable
                // iterate operands by formatting (conservative) but better to match structured operands:
                match inst {
                    Instruction::Alloca(a) => {
                        // Variable name is in dest
                        let var_name = name_to_string(&a.dest);
                        // Type is specified by allocated_type
                        let var_type : TypeRef = match &a.allocated_type.as_ref() {
                            Type::IntegerType {bits} => TypeRef::IntegerType(*bits),
                            other => panic!("Encountered invalid datatype at: {}", inst),
                        };
                        // Register the variable
                        vars.insert(var_name.clone(), VarRef {name: var_name.clone(), type_ref: var_type, initial: None});
                        // Register it in the initialization mapping
                        var_initialized.insert(var_name, false);
                    }
                    Instruction::Load(l) => {
                        // Load usually results in a Number dest
                        let var_name = name_to_string(&l.dest);
                        // Type is specified by loaded_ty
                        let var_type : TypeRef = match &l.loaded_ty.as_ref() {
                            Type::IntegerType {bits} => TypeRef::IntegerType(*bits),
                            other => panic!("Encountered invalid datatype at: {:#?}", l),
                        };
                        // Register the variable
                        vars.insert(var_name.clone(), VarRef {name: var_name.clone(), type_ref: var_type, initial: None});
                        // Register it in the initialization mapping
                        var_initialized.insert(var_name, false);
                    }
                    Instruction::Store(s) => {
                        // We could be setting the initial state
                        if let Operand::LocalOperand {name, .. } = &s.address {
                            // Get the name as String
                            let var_name = name_to_string(name);
                            // Is it setting the initial state?
                            if !var_initialized[&var_name] {
                                if let Operand::ConstantOperand(const_ref) = &s.value {
                                    // TODO: Allows only for constant updates, do for variables as well
                                    match &**const_ref {
                                        Constant::Int {value, ..} => {
                                            // Set the initial value
                                            let var = vars.get_mut(&var_name).unwrap();
                                            var.initial = Some(*value);
                                            // Set initialized to true
                                            var_initialized.insert(var_name, true);
                                        },
                                        _ => panic!("Expected Constant::Int, got: {}", const_ref),
                                    }
                                }
                            }
                        }else {
                            panic!("Store(s) panicked: {:#?}", s);
                        }
                    }
                    Instruction::ICmp(c) => {
                        // Variable name is in dest
                        let var_name = name_to_string(&c.dest);
                        if let Operand::LocalOperand {ty, ..} = &c.operand0 {
                            if let Operand::LocalOperand {..} = &c.operand1 {
                                let var_type = match ty.as_ref() {
                                    Type::IntegerType {bits} => TypeRef::BoolType(*bits),
                                    other => panic!("Encountered IComp(c) with operand type {:#?}", ty),
                                };
                                // Register the Boolean
                                vars.insert(var_name.clone(), VarRef {name: var_name.clone(), type_ref: var_type, initial: None});
                                var_initialized.insert(var_name, false);
                            }else {
                                panic!("Icmp(c) does not have both of its operands as LocalOperand: {:#?}", c);
                            }
                        }else {
                            panic!("Icmp(c) does not have both of its operands as LocalOperand: {:#?}", c);
                        }
                    }
                    _ => {
                        panic!("Unhandled instruction in collect_vars: {:#?}", inst);
                    }
                }
            }
        }
    }

    // also include module-level global vars (names)
    for gv in &m.global_vars {
        // vars.insert(Var(format!("@{}", gv.name)));
    }

    vars
}

/// Determine successor PCs for each instruction PC.
/// For non-terminators successor is next instruction in same function (pc+1) except if end-of-function.
/// For terminators, examine the Terminator value and map basic-block destination names to their entry PCs
pub fn compute_successors(
    m: &Module,
    instr_list: &Vec<(String, String, bool, String)>,
    map_bb_start_pc: &BTreeMap<(String, String), usize>,
) -> Vec<Vec<usize>> {
    // We'll need a helper map: for each function, the list of pcs (indices into instr_list) belonging to it,
    // in order; and for each (func, bb), the range of indices.
    let mut succs: Vec<Vec<usize>> = vec![Vec::new(); instr_list.len()];

    // Create map from (func, bb, pc_index_within_instr_list) to global pc index is just position.

    // Build map from (func,bb) -> Vec<pc indices in order>
    let mut func_bb_pcs: BTreeMap<(String, String), Vec<usize>> = BTreeMap::new();
    for (pc, (f, b, _, _)) in instr_list.iter().enumerate() {
        func_bb_pcs
            .entry((f.clone(), b.clone()))
            .or_default()
            .push(pc);
    }

    // Build index range for each function's linear list to find next-in-function
    // Also build map func -> sorted vector of pcs in function order:
    let mut func_pcs: BTreeMap<String, Vec<usize>> = BTreeMap::new();
    for (pc, (f, _, _, _)) in instr_list.iter().enumerate() {
        func_pcs.entry(f.clone()).or_default().push(pc);
    }

    // For quick lookup of next pc in same function, map pc -> position index in func_pcs[f]
    let mut pc_pos_in_func: BTreeMap<usize, usize> = BTreeMap::new();
    for (fname, vec_pcs) in &func_pcs {
        for (i, &pc) in vec_pcs.iter().enumerate() {
            pc_pos_in_func.insert(pc, i);
        }
    }

    // Now compute successors
    for (pc, (f, b, is_term, inst_text)) in instr_list.iter().enumerate() {
        if !*is_term {
            // successor is the next instruction in the same function, if any
            if let Some(&pos) = pc_pos_in_func.get(&pc) {
                let func_vec = &func_pcs[f];
                if pos + 1 < func_vec.len() {
                    succs[pc].push(func_vec[pos + 1]);
                } else {
                    // no successor (end of function) -> no successor
                }
            }
        } else {
            // parse the terminator text using the structured form by re-parsing the module:
            // We must find the actual Terminator object: but we don't have direct access here;
            // instead, reconstruct by locating the same basic block in the module and reading its terminator.
            // Find the function and basic block in the module m:
            if let Some(func) = m.get_func_by_name(&f) {
                if let Some(bb) = func.basic_blocks.iter().find(|bbx| format!("{}", bbx.name) == *b) {
                    use llvm_ir::terminator::Terminator;
                    match &bb.term {
                        Terminator::Br(br) => {
                            // Unconditional br has a single dest name
                            let dest = format!("{}", br.dest);
                            if let Some(&dest_pc) = map_bb_start_pc.get(&(f.clone(), dest.clone())) {
                                succs[pc].push(dest_pc);
                            }
                        }
                        Terminator::CondBr(cb) => {
                            let true_name = format!("{}", cb.true_dest);
                            let false_name = format!("{}", cb.false_dest);
                            if let Some(&tpc) = map_bb_start_pc.get(&(f.clone(), true_name.clone())) {
                                succs[pc].push(tpc);
                            }
                            if let Some(&fpc) = map_bb_start_pc.get(&(f.clone(), false_name.clone())) {
                                succs[pc].push(*map_bb_start_pc.get(&(f.clone(), false_name.clone())).unwrap());
                            }
                        }
                        Terminator::Ret(_) => {
                            // returns: no successor
                        }
                        Terminator::Switch(sw) => {
                            // switch has a default dest and potentially other dests
                            let default = format!("{}", sw.default_dest);
                            if let Some(&dpc) = map_bb_start_pc.get(&(f.clone(), default.clone())) {
                                succs[pc].push(dpc);
                            }
                            for (_val, dest) in &sw.dests {
                                let dname = format!("{}", dest);
                                if let Some(&dpc) = map_bb_start_pc.get(&(f.clone(), dname.clone())) {
                                    if !succs[pc].contains(&dpc) {
                                        succs[pc].push(dpc);
                                    }
                                }
                            }
                        }
                        _ => {
                            // For other terminator kinds (invoke, indirectbr, etc.) conservatively
                            // we do nothing or could attempt more precise extraction. No successors -> end.
                        }
                    }
                }
            }
        }
    }
    succs
}

/// Build the per-variable transitions according to the rules described
pub fn build_transitions(
    m: &Module,
    instr_list: &Vec<(String, String, bool, String)>,
    vars: &IndexMap<String, VarRef>,
    succs: &Vec<Vec<usize>>,
    map_bb_start_pc: &BTreeMap<(String, String), usize>,
) -> Vec<VarTransition> {
    let mut transitions = Vec::new();
    let mut global_pc = 0usize;
    // Tracking which variables are initialized
    let mut var_initialized : IndexMap<String, bool> = IndexMap::new();
    // Populate it with variable names
    for (name, _) in vars.iter() {
        var_initialized.insert(name.to_string(), false);
    }

    for func in &m.functions {
        let fname = &func.name;
        for bb in &func.basic_blocks {
            // non-terminator instructions
            for inst in &bb.instrs {
                let pc = global_pc;
                // determine successors
                let targets = succs.get(pc).cloned().unwrap_or_default();
                // which variable(s) are updated by this inst?
                let mut written_vars: Vec<(String, UpdateType)> = Vec::new();

                match inst {
                    Instruction::Store(s) => {
                        // We could be setting the initial state
                        if let Operand::LocalOperand {name, .. } = &s.address {
                            // Get the name as String
                            let assigned_var = name_to_string(name);
                            // Have we already assigned to it?
                            if !var_initialized[&assigned_var] {
                                // It is an initialization, pass
                                var_initialized.insert(assigned_var, true);
                            }else {
                                match &s.value {
                                    Operand::ConstantOperand(const_ref) => {
                                        match &**const_ref {
                                            Constant::Int {value, ..} => {
                                                written_vars.push((assigned_var, UpdateType::ConstantUpdate(*value)));
                                            },
                                            _ => panic!("Expected Constant::Int, got: {}", const_ref),
                                        }
                                    }
                                    Operand::LocalOperand {name, ..} => {
                                        let assignee = name_to_string(name);
                                        written_vars.push((assigned_var, UpdateType::VariableUpdate(assignee)));
                                    }
                                    _ => panic!("Unsupported operand for Store(s): {:#?}", s),
                                }
                            }
                        }else {
                            panic!("Store(s) panicked: {:#?}", s);
                        }
                    }
                    Instruction::Load(l) => {
                        // Load usually results in a Number dest
                        let assigned_var = name_to_string(&l.dest);
                        match &l.address {
                            Operand::LocalOperand {name, ..} => {
                                let assignee = name_to_string(name);
                                written_vars.push((assigned_var, UpdateType::VariableUpdate(assignee)));
                            }
                            _ => panic!("Invalid Operand for load: {:#?}", l),
                        }
                    }
                    Instruction::ICmp(c) => {
                        // Assigned variable name is in dest
                        let assigned_var = name_to_string(&c.dest);
                        if let Operand::LocalOperand {name: lhs_name, ..} = &c.operand0 {
                            if let Operand::LocalOperand {name: rhs_name, ..} = &c.operand1 {
                                let predicate = match &c.predicate {
                                    IntPredicate::EQ  => "EQ",
                                    IntPredicate::NE  => "NE",
                                    IntPredicate::UGT => "UGT",
                                    IntPredicate::UGE => "UGE",
                                    IntPredicate::ULT => "ULT",
                                    IntPredicate::ULE => "ULE",
                                    IntPredicate::SGT => "SGT",
                                    IntPredicate::SGE => "SGE",
                                    IntPredicate::SLT => "SLT",
                                    IntPredicate::SLE => "SLE",
                                };
                                written_vars.push((
                                    assigned_var,
                                    UpdateType::ComparisonUpdate {
                                        operator: String::from(predicate),
                                        lhs: name_to_string(lhs_name),
                                        rhs: name_to_string(rhs_name),
                                    }
                                ));
                                // Register the Boolean
                            }else {
                                panic!("Icmp(c) does not have both of its operands as LocalOperand: {:#?}", c);
                            }
                        }else {
                            panic!("Icmp(c) does not have both of its operands as LocalOperand: {:#?}", c);
                        }
                    }
                    _ => {}
                }

                // For each successor target pc produce a set of per-variable transitions
                let target_pcs = if !targets.is_empty() {
                    targets
                } else {
                    // non-terminator with no successor -> no outgoing transitions
                    Vec::new()
                };

                if target_pcs.is_empty() {
                    // we still want to report per-variable transitions to a self-loop (optional).
                    // For safety, if no explicit successor, we produce no transitions (end-of-function).
                    // This makes the transition system finite and explicit.
                } else {
                    for &tpc in &target_pcs {
                        // For fast membership test:
                        let mut written_map = BTreeMap::new();
                        for (name, upd_type) in &written_vars {
                            written_map.insert(name.clone(), upd_type.clone());
                        }
                        for (name, _) in vars.iter() {
                            if let Some(upd_type) = written_map.get(name) {
                                transitions.push(VarTransition {
                                    from_pc: pc,
                                    to_pc: tpc,
                                    var: name.clone(),
                                    cond: None,
                                    upd: upd_type.clone(),
                                });
                            }
                        }
                    }
                }
                global_pc += 1;
            }

            // handle terminator
            match &bb.term {
                Terminator::CondBr(cb) => {
                    let pc = global_pc;
                    let targets = succs.get(pc).cloned().unwrap_or_default();
                    let true_name = name_to_string(&cb.true_dest);
                    let false_name = name_to_string(&cb.false_dest);
                    let cond_var = match &cb.condition {
                        Operand::LocalOperand { name, .. } => name_to_string(name),
                        _ => panic!("Terminator operand is not a LocalOperand: {:#?}", cb),
                    };
                    // Locate the start-PCs of the true and false basic blocks by scanning map_bb_start_pc.
                    // Assume it always exists
                    let true_pc = map_bb_start_pc.get(&(fname.clone(), true_name.clone())).unwrap();
                    let false_pc = map_bb_start_pc.get(&(fname.clone(), false_name.clone())).unwrap();

                    //Create the transition for PC
                    // true branch
                    transitions.push(VarTransition {
                        from_pc: pc,
                        to_pc: *true_pc,
                        var: String::from("%__pc"),
                        cond: Some((cond_var.clone(), true)),
                        upd: UpdateType::ConstantUpdate(*true_pc as u64),
                    });
                    // false branch
                    transitions.push(VarTransition {
                        from_pc: pc,
                        to_pc: *false_pc,
                        var: String::from("%__pc"),
                        cond: Some((cond_var.clone(), false)),
                        upd: UpdateType::ConstantUpdate(*false_pc as u64),
                    });
                }
                _ => (),
            }
            global_pc += 1;
        }
    }
    transitions
}