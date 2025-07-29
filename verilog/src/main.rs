use std::{path::PathBuf, process};
use hqb_verilog::{unroll_from_smt_build, unroll_from_verilog};
use clap::{arg, value_parser, ArgGroup, Command};


fn main() {
    //clap setup
    let cli = Command::new("hqb-verilog")
        .arg(
            arg!(
                -v --verilog <FILE> "Input file"
            )
            .required(false)
            .value_parser(value_parser!(PathBuf)),
        )
        .arg(
            arg!(
                -t --top <TOP_MODULE> "Top module name (default: main)"
            )
            .required(true)
            .default_value("main")
            .value_parser(value_parser!(String)),
        )
        .arg(
            arg!(
                -s --smt2_path <SMT2_FILE> "Location of SMT2 file if using a build file"
            )
            .required(false)
            .value_parser(value_parser!(PathBuf)),
        )
        .arg(
            arg!(
                -b --build <BUILD_FILE> "Yosys build file"
            )
            .required(false)
            .value_parser(value_parser!(PathBuf)),
        )
        .arg(
            arg!(
                -u --unroll <BOUND> "Unroll the design directly from the smt2 file up to bound"
            )
            .value_parser(value_parser!(u32))
            .required(true)  
        )
        .arg(
            arg!(
                -i --trace_id <TRACE_ID> "Trace ID for unrolling"
            )
            .value_parser(value_parser!(String))
            .required(true)
        )
        .group(ArgGroup::new("input")
            .args(["verilog", "build"])
            .required(true)
        );
    
    let matches = cli.get_matches();
    
    // Get the top module name
    let top_module_name = matches.get_one::<String>("top").unwrap();
    // If a build file is specified, use it
    if let Some(build_path) = matches.get_one::<PathBuf>("build") {
        // If an SMT2 file is specified, use it
        if let Some(smt2_path) = matches.get_one::<PathBuf>("smt2_path") {
            // Get unroll bound
            if let Some(bound) = matches.get_one::<u32>("unroll") {
                // Unroll from SMT2 file
                match unroll_from_smt_build(build_path, top_module_name, smt2_path, *bound, matches.get_one::<String>("trace_id").unwrap()) {
                    Ok((_unrolled, states, getters)) => println!("Unrolled design!\nStates: {:?}\nGetters: {:?}", states, getters),
                    Err(e) => eprintln!("Error during unrolling: {}", e),
                }
            } else {
                eprintln!("Unroll bound is required when using a build file.");
                process::exit(1);
            }
        } else {
            // Failed to find SMT2 file
            eprintln!("SMT2 file is required when using a build file.");
            process::exit(1);
        }
    } else if let Some(verilog_path) = matches.get_one::<PathBuf>("verilog") {
        if let Some(bound) = matches.get_one::<u32>("unroll") {
            // Unroll from Verilog file
            match unroll_from_verilog(verilog_path, top_module_name, *bound, matches.get_one::<String>("trace_id").unwrap()) {
                Ok((_unrolled, states, getters)) => println!("Unrolled design!\nStates: {:?}\nGetters: {:?}", states, getters),
                Err(e) => eprintln!("Error during unrolling: {}", e),
            }
        } else {
            eprintln!("Unroll bound is required when using a Verilog file.");
            process::exit(1);
        }
    } else {
        // No input file provided
        eprintln!("Either a Verilog file or a build file must be provided.");
        process::exit(1);   
    }

}
