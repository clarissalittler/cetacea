//! Elaboration diagnostics: a message anchored to a span, with optional
//! notes and a repair suggestion.

use hol_syntax::Span;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    pub span: Span,
    pub message: String,
    pub notes: Vec<String>,
    /// A concrete replacement or addition the student can try.
    pub suggestion: Option<String>,
}

impl Diagnostic {
    pub fn new(span: Span, message: impl Into<String>) -> Diagnostic {
        Diagnostic {
            span,
            message: message.into(),
            notes: Vec::new(),
            suggestion: None,
        }
    }

    pub fn note(mut self, note: impl Into<String>) -> Diagnostic {
        self.notes.push(note.into());
        self
    }

    pub fn suggest(mut self, suggestion: impl Into<String>) -> Diagnostic {
        self.suggestion = Some(suggestion.into());
        self
    }

    pub fn with_span(mut self, span: Span) -> Diagnostic {
        self.span = span;
        self
    }
}

impl From<hol_kernel::KernelError> for Diagnostic {
    fn from(err: hol_kernel::KernelError) -> Diagnostic {
        Diagnostic::new(
            Span::default(),
            format!("kernel rejected the step: {}", err.message),
        )
    }
}

pub type Result<T> = std::result::Result<T, Diagnostic>;

macro_rules! fail {
    ($span:expr, $($arg:tt)*) => {
        return Err($crate::diag::Diagnostic::new($span, format!($($arg)*)))
    };
}

pub(crate) use fail;
