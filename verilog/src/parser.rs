use regex::Regex;
use std::collections::HashMap;
use crate::error::ExtractError;

#[derive(Debug, Clone)]
pub struct StateVariable {
    pub original_name: String,
    pub yosys_name: String,
}

/// Unrolls the design in-place, modifying the SMT2 string to include unrolling constraints.
/// Returns the modified SMT2 string, a list of states' names, and the mapping of the getters
pub fn unroll_in_place(smt2: &str, mod_name: &str, bound: u32, trace_id: &str) -> Result<(String, Vec<String>, HashMap<String, String>), ExtractError> {
    // Parse the variables to get their names
    let id_to_name = parse_variables(smt2, mod_name)?;
    println!("Parsed variables: {:#?}", id_to_name);
    // Restore variable names in the SMT2 string
    let restored_smt2 = restore_variable_names(smt2, &id_to_name);
    let getter_map = map_variables(mod_name, &id_to_name);
    println!("Restored original variables!");
    // Augment the SMT2 with unrolling logic
    let (unrolled_smt, state_names) = add_unrolling_constraints(&restored_smt2, mod_name, bound, trace_id);
    println!("Added unrolling constraints!");
    // Write to file
    let output_path = format!("{}_unrolled.smt2", mod_name);
    std::fs::write(&output_path, &unrolled_smt)
        .map_err(|e| ExtractError::Io(std::io::Error::new(std::io::ErrorKind::Other, format!("Failed to write unrolled SMT2 to {}: {}", output_path, e))))?;
    Ok((unrolled_smt, state_names, getter_map))
}

fn parse_variables(smt2: &str, mod_name: &str) -> Result<Vec<StateVariable>, ExtractError> {
    let re = Regex::new(&format!(r"\s*\(\|({}#\d+)\|.*(Bool|BitVec).*;\s*\\(\S*)", mod_name)).unwrap();
    let mut variables = Vec::new();
    for cap in re.captures_iter(smt2) {
        let yosys_name = cap[1].to_string();
        let original_name = cap[3].to_string();
        variables.push(StateVariable {
            original_name: original_name.clone(),
            yosys_name,
        });
    }
    if variables.is_empty() {
        println!("{:#?}", smt2);
        return Err(ExtractError::Parse(format!("No variables found for module {}", mod_name)));
    }
    Ok(variables)
}

fn restore_variable_names(smt2: &str, vars: &Vec<StateVariable>) -> String {
    let mut result = smt2.to_string();
    for var in vars {
        let re = Regex::new(&format!(r"\|{}\|", var.yosys_name)).unwrap();
        result = re.replace_all(&result, format!("|{}|", var.original_name)).to_string();
    }
    result
}

// Maps each state variable's original name to its getter function name
// e.g. "PC" -> "|main_n PC|"
fn map_variables(mod_name: &str, variable_names: &Vec<StateVariable>) -> HashMap<String, String> {
    let mut getter_map = HashMap::new();
    for var in variable_names {
        let getter_name = format!("|{}_n {}|", mod_name, var.original_name);
        getter_map.insert(var.original_name.clone(), getter_name);
    }
    getter_map
}

// Augments the SMT2 string with unrolling constraints
// Returns the modified SMT2 string and a list of states' names
fn add_unrolling_constraints(smt2: &str, mod_name: &str, bound: u32, trace_id: &str) -> (String, Vec<String>) {
    let mut result = smt2.to_string();
    // Add constraints for unrolling
    //Add contants for each step
    result.push_str(&format!(
        "\n; Unrolled states\n"
    ));
    let mut state_names = Vec::new();
    for i in 0..bound+1 {
        result.push_str(&format!(
            "(declare-const |s_{}_{}| |{}_s|)\n",
            trace_id,
            i,
            mod_name
        ));
        state_names.push(format!("|s_{}_{}|", trace_id, i));
    }
    // Add next-state constraints
    result.push_str(&format!(
        "\n; Initial and Next-state constraints\n"
    ));

    result.push_str(&format!(
        "(assert (and (|{}_i| |s_{}_0|) ",
        mod_name,
        trace_id 
    ));

    for i in 0..(bound) {
        result.push_str(&format!(
            "(|{}_t| s_{}_{} s_{}_{}) ",
            mod_name,
            trace_id,
            i,
            trace_id,
            i + 1
        ));
    }
    result.push_str("))\n");

    result.push_str(&format!(
        "; End of unrolling constraints\n"
    ));
    (result, state_names)
}