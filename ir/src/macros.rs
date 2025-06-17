
// Imagine using a macro to generate the following macros :))

#[macro_export]
macro_rules! bool_var {
    ($state:expr, $name:expr) => {
        $state.get($name).unwrap().as_bool().unwrap()
    };
}

#[macro_export]
macro_rules! int_var {
    ($state:expr, $name:expr) => {
        $state.get($name).unwrap().as_int().unwrap()
    };
}

#[macro_export]
macro_rules! bv_var {
    ($state:expr, $name:expr) => {
        $state.get($name).unwrap().as_bv().unwrap()
    };
}

#[macro_export]
macro_rules! to_dyn {
    ($node:expr) => {
        Dynamic::from_ast(&$node)
    };
}

#[macro_export]
macro_rules! choice {
    (Bool, $( $x:expr ),+ ) => {
        {
            let mut tmp_vec = Vec::<bool>::new();
            $(
                tmp_vec.push($x);
            )+
            ReturnType::Bool(tmp_vec)
        }
    };

    (Node, $node:expr ) => {
        ReturnType::DynAst(to_dyn!($node))
    };

    (Int, $( $x:expr ),+ ) => {
        {
            let mut tmp_vec = Vec::<i64>::new();
            $(
                tmp_vec.push($x);
            )+
            ReturnType::Int(tmp_vec)
        }
    };

    (BVector, $( ($value:expr, $size:expr) ),+ ) => {
        {
            let mut tmp_vec = Vec::<(i64, u32)>::new();
            $(
                tmp_vec.push(($value, $size));
            )+
            ReturnType::BVector(tmp_vec)
        }
    };
}

#[macro_export]
macro_rules! exact {
    ( Bool, $value:expr ) => {
        choice!(Bool, $value)
    };
    ( Int, $value:expr ) => {
        choice!(Int, $value)
    };
    ( Node, $value:expr ) => {
        choice!(Node, $value)
    };
    ( BVector, $value:expr ) => {
        choice!(BVector, $value)
    };

}