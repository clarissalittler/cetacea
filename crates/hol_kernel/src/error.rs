//! Kernel errors. Every rejected rule application or definitional
//! principle reports which rule rejected it and why.

use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KernelError {
    pub rule: &'static str,
    pub message: String,
}

impl KernelError {
    pub fn new(rule: &'static str, message: impl Into<String>) -> KernelError {
        KernelError {
            rule,
            message: message.into(),
        }
    }
}

impl fmt::Display for KernelError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.rule, self.message)
    }
}

impl std::error::Error for KernelError {}

pub type Result<T> = std::result::Result<T, KernelError>;

macro_rules! bail {
    ($rule:expr, $($arg:tt)*) => {
        return Err($crate::error::KernelError::new($rule, format!($($arg)*)))
    };
}

pub(crate) use bail;
