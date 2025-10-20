mod error;
mod yosys;
mod parser;
mod model;
mod smt_preprocess;
mod ir_parser;

pub use error::ExtractError;
pub use model::{Model, RegisterInfo, VarType};

use z3::{ast::{Ast, Bool, Dynamic, Int, BV}, Context};

use std::path::Path;
use std::collections::HashMap;

use ir::{SMVEnv}; // adjust path: crate::ir::<...>

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
    let id_to_name = parser::parse_variables(&smt_text, top_module_name)?;
    let restored_smt2 = parser::restore_variable_names(&smt_text, &id_to_name);

    // Preprocess the SMT to simplify it
    let transformed_smt = smt_preprocess::transform(&restored_smt2);
    //write to file for debugging
    let transformed_path = smt_path.with_file_name(format!("{}_transformed.smt2", top_module_name));
    std::fs::write(&transformed_path, &transformed_smt)
        .map_err(|e| ExtractError::Io(std::io::Error::new(std::io::ErrorKind::Other, format!("Failed to write transformed SMT2 to {}: {}", transformed_path.display(), e))))?;

    // Build IR
    //let env = ir_parser::build_env_from_flat_smt()

    parser::unroll_in_place(&smt_text, top_module_name, bound, trace_id, filter.cloned())
}

pub fn build_smvenv_from_verilog<'ctx>(
    _build_file_path: &Path,
    top_module_name: &str,
    smt_path: &Path,
    context: &'ctx Context
) -> Result<SMVEnv<'ctx>, ExtractError> {

    yosys::run_yosys_with_build(_build_file_path)?;
    let smt_text = std::fs::read_to_string(&smt_path)?;
    let id_to_name = parser::parse_variables(&smt_text, top_module_name)?;
    let restored_smt2 = parser::restore_variable_names(&smt_text, &id_to_name);

    let transformed_smt = smt_preprocess::transform(&restored_smt2);

    let transformed_path = smt_path.with_file_name(format!("{}_transformed.smt2", top_module_name));
    std::fs::write(&transformed_path, &transformed_smt)
        .map_err(|e| ExtractError::Io(std::io::Error::new(
            std::io::ErrorKind::Other,
            format!("Failed to write transformed SMT2 to {}: {}", transformed_path.display(), e),
        )))?;

    // Convert String -> ExtractError here:
    let env = ir_parser::build_env_from_flat_smt(context, &transformed_smt)
        .map_err(|e| ExtractError::Parse(format!("IR parse error: {e}")))?;  // <-- Pick the right variant name

    Ok(env)
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
