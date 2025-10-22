use colored::*;
use std::process::exit;

#[derive(Clone, Copy)]
pub struct Logger {
    level: i8,
    debug: bool,
}

impl Logger {
    pub fn new(debug: bool, level: i32) -> Logger {
        Logger {
            level: level as i8,
            debug,
        }
    }

    /// Applies the formatting to the string based on the level
    fn apply_level(&self, string: &str, level: i8) -> ColoredString {
        match level {
            1 => ("info: ".to_owned() + string).bright_cyan(),
            2 => ("Completed: ".to_owned() + string).bright_green(),
            3 => ("warning: ".to_owned() + string).bright_yellow(),
            4 => ("error: ".to_owned() + string).bright_red(),
            5 => ("fatal error: ".to_owned() + string).red().bold(),
            _ => string.red().bold().italic(),

        }
    }
    /// Raises an error and exits the program
    ///
    /// # Arguments
    ///
    /// * `error` - A string slice that holds the error message
    /// * `level` - The error level, higher means more severe
    pub fn raise_error(&self, error: &str, level: i8) {
        eprintln!("{}", self.apply_level(&error, level));
        if level>3 {
            exit(1);
        }
    }

    pub fn log(&self, message: &str, level: i8) {
        if level >3 {
            self.raise_error(message, level);
        }
        if (level >= self.level) & self.debug {
            // println!("{}", self.apply_level(&message, level));
        }

    }

    /// Returns the current mode
    /// # Returns
    /// * The current mode where true is debug and false is not debug
    pub fn get_mode(&self)-> bool {
        return self.debug;
    }
}