#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VarType {
    Bool,
    BitVec(usize),
}

#[derive(Debug)]
pub struct RegisterInfo {
    pub name:    String,
    pub var_type: VarType,
    pub next_fn: String,
}

#[derive(Debug)]
pub struct Model {
    pub variables: Vec<RegisterInfo>,
}
