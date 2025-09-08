macro_rules! display_arm {
    ($f:ident, ($fmt_str:literal $(, $arg:expr )* $(,)? ) ) => {
        write!($f, $fmt_str $(, $arg )*)
    };
    ($f:ident, $fmt_str:literal) => {
        write!($f, $fmt_str)
    };
    ($f:ident, $arg:ident => $body:expr) => {
        {
            let $arg = $f;
            $body
        }
    };
}

macro_rules! impl_from_str {
    ($name:ident, $($variant:ident : $str:literal),*) => {
        impl std::str::FromStr for $name {
            type Err = String;
            fn from_str(s: &str) -> Result<Self, Self::Err> {
                match s {
                    $($str => Ok($name::$variant),)*
                    _ => Err(format!("invalid {} value: {}", stringify!($name), s))
                }
            }
        }
    };
    ($name:ident, $($variant:ident $( ( $($field:ident),* ) )? : $fmt:tt $( => $fmt_body:expr)?),*) => {};
}

/// A macro to define enums with automatic Display implementation.
macro_rules! displayable_enum {
    (
        $(#[$attr:meta])*
        $vis:vis enum $name:ident {
            $(
                $variant:ident $( ( $( $field:ident : $ty:ty ),* $(,)? ) )? : $fmt:tt $( => $fmt_body:expr)?
            ),* $(,)? 
        }
    ) => {
        $(#[$attr])*
        $vis enum $name {
            $(
                $variant $( ( $( $ty ),* ) )?
            ),*
        }

        impl std::fmt::Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                #[allow(dead_code)]
                fn format(
                    f: &mut std::fmt::Formatter<'_>,
                    formatter: impl FnOnce(&mut std::fmt::Formatter<'_>) -> std::fmt::Result
                ) -> std::fmt::Result {
                    formatter(f)
                }
                match self {
                    $(
                        #[allow(unused_variables)]
                        $name::$variant $( ( $( $field ),* ) )? => display_arm!(f, $fmt $( => $fmt_body )? )
                    ),*
                }
            }
        }

        impl_from_str!($name, $($variant $( ( $( $field ),* ) )? : $fmt $( => $fmt_body )?),*);
    };
}