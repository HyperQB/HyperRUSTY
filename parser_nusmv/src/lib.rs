pub mod main; // or whatever your module file is
// pub mod flattener;

pub use main::parse_smv; // <- this line makes `parse_model` accessible from the root