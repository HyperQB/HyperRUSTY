mod error;
mod yosys;
mod parser;
mod model;

pub use error::ExtractError;
pub use model::{Model, RegisterInfo, VarType};

use std::path::Path;
use std::collections::HashMap;

pub fn unroll_from_smt_build(
    _build_file_path: &Path,
    top_module_name: &str,
    smt_path: &Path,
    bound: usize,
    trace_id: &str,
    filter: Option<&Vec<String>>,
) -> Result<(String, Vec<String>, HashMap<String, String>), ExtractError> {
    yosys::run_yosys_with_build(_build_file_path)?;
    let smt_text = std::fs::read_to_string(&smt_path)?;
    parser::unroll_in_place(&smt_text, top_module_name, bound, trace_id, filter.cloned())
}

// deprecated
pub fn unroll_from_verilog(
    verilog_path: &Path,
    top_module_name: &str,
    bound: usize,
    trace_id: &str,
) -> Result<(String, Vec<String>, HashMap<String, String>), ExtractError> {
    // 1) temp SMT file path
    let smt2_path = verilog_path.with_extension("smt2");
    // 2) run yosys
    yosys::run_yosys(verilog_path, &smt2_path, top_module_name)?;
    // 3) read back and parse
    let smt_text = std::fs::read_to_string(&smt2_path)?;
    parser::unroll_in_place(&smt_text, top_module_name, bound, trace_id, None)
}
