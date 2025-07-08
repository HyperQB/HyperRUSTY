/// Type of a state variable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VarType {
    Bool,
    BitVec(usize),
}

/// Holds everything about one state‐register:
/// - its clean name (“high”, “PC”, …)
/// - its type/width
/// - the SMT2 `define-fun` S-expression for its next-state logic
#[derive(Debug)]
pub struct RegisterInfo {
    pub name:    String,
    pub var_type: VarType,
    pub next_fn: String,
}

/// The overall result: a list of all state-variables in the design.
#[derive(Debug)]
pub struct Model {
    pub variables: Vec<RegisterInfo>,
}
