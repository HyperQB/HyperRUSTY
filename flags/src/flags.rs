use gflags::*;
use lazy_static::lazy_static;
use logging::raise_error;
use logging::Logger;

define! {
    /// The number of layers you want to unroll
    /// # Possible values
    /// * `n in Z+` - Any positive integer
    -k, --layers: i32 = 2
}
define!{
    /// The semantics you want to use
    /// # Possible values
    /// * `OPT` - Optimistic, it will return true if it never finds a fail condition
    /// * `PES` - Pessimistic, it will return false if it never finds a success condition
    -s, --semantics : &str = "PES"
}
define!{
    /// The help command
    -h, --help : bool = false
}
define! {
    /// The debug command
    /// # Possible values
    /// * `0` - No debug
    /// * `1` - Debug
    -d, --debug : i32 = 0
}
define! {
    /// The level of debug you want
    /// # Possible values
    /// * `1` - Prints everything
    /// * `2` - Does not print when a task is completed
    /// * `3` - Does not print when task is completed or general info
    /// * `4` - Does not print when task is completed, general info, or warnings
    /// * `5` - Will only print errors
    --debug_level: i32 = 1
}
define! {
    /// For backwards compatability. If you still need to use the .bool files please use this flag
    /// Using this flag will change the input file structure from the .smv to I and R files
    --legacy: bool = false
}

define! {
    /// If new encoding or not
    -e, --encoding: bool = false
}
define! {
    /// The model you want to use the encoding on. exclude to provide encoding on all models
    /// NOTE: only use in combination with -e
    -m, --model: &str = ""
}



pub struct Flags{
    pub layers: i32,
    pub sem: String,
    pub help: bool,
    pub debug: bool,
    pub debug_level: i32,
    pub legacy: bool,
    pub encoding: bool,
    pub model: String
}

lazy_static! {
    pub static ref FLAGS: Flags = Flags{
        layers: LAYERS.flag,
        sem: SEMANTICS.flag.to_string(),
        help: HELP.flag,
        debug: DEBUG.flag != 0,
        debug_level: DEBUG_LEVEL.flag,
        legacy: LEGACY.flag,
        encoding: ENCODING.flag,
        model: MODEL.flag.to_string()
    };
}

pub fn parse_flags() -> Logger{
    let args = parse();
    let logger = Logger::new(FLAGS.debug, FLAGS.debug_level);
    // println!("The model flag is: {}", MODEL.flag);

    if HELP.flag {
        // print the doc string of each flag
        print_help_and_exit(0);
    }

    if !MODEL.flag.is_empty() & (!ENCODING.flag){
        logger.log("You can only use model flag if you also use encoding flag",5);
    }

    if FLAGS.layers < 1 {
        raise_error("The number of layers must be greater than 0", 5);
    }
    logger.log(&*format!("The number of layers is: {}", FLAGS.layers), 1);
    logger.log(&*format!("The semantics is: {}", FLAGS.sem), 1);
    logger.log(&*format!("The debug is: {}", FLAGS.debug), 1);
    logger.log(&*format!("The debug level is: {}", FLAGS.debug_level), 1);
    logger.log(&*format!("The args are: {:?}",args), 1);
    logger.log(&*format!("The layers are: {}", LAYERS.flag), 1);
    logger.log(&*format!("New encoding bool is: {}", ENCODING.flag), 1);

    if FLAGS.debug & (DEBUG_LEVEL.flag < 1 || DEBUG_LEVEL.flag > 5) {
        logger.log("The debug level must be between 1 and 5", 5);
    }

    if !["OPT", "PES"].contains(&SEMANTICS.flag) {
        logger.log("The semantics must be either OPT or PES", 5);
    }
    logger.log("Flag Parsing",2);
    return logger;
}