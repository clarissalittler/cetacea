//! Tokens and the lexer.
//!
//! Every token carries a [`Span`] with 1-based line and column numbers.
//! Comments start with `--` and run to the end of the line. Unicode
//! aliases for the connectives and quantifiers lex to the same tokens as
//! their ASCII spellings.

use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Span {
    pub line: u32,
    pub col: u32,
    pub end_line: u32,
    pub end_col: u32,
}

impl Span {
    pub fn point(line: u32, col: u32) -> Span {
        Span {
            line,
            col,
            end_line: line,
            end_col: col + 1,
        }
    }

    /// The smallest span covering both.
    pub fn to(self, other: Span) -> Span {
        let (line, col) = if (self.line, self.col) <= (other.line, other.col) {
            (self.line, self.col)
        } else {
            (other.line, other.col)
        };
        let (end_line, end_col) =
            if (self.end_line, self.end_col) >= (other.end_line, other.end_col) {
                (self.end_line, self.end_col)
            } else {
                (other.end_line, other.end_col)
            };
        Span {
            line,
            col,
            end_line,
            end_col,
        }
    }

    pub fn whole_line(line: u32, len: usize) -> Span {
        Span {
            line,
            col: 1,
            end_line: line,
            end_col: len as u32 + 1,
        }
    }
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Tok {
    Ident(String),
    Num(u64),
    /// An import path: everything after `import` up to whitespace.
    Path(String),
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Comma,
    Colon,
    Semi,
    Bar,
    Dot,
    Star,
    /// `=>`
    FatArrow,
    /// `:=`
    Define,
    /// `->`
    Arrow,
    /// `<-`
    LeftArrow,
    /// `<->`
    Iff,
    /// `/\`
    And,
    /// `\/`
    Or,
    /// `=`
    Eq,
    /// `+`
    Plus,
    /// `-`
    Minus,
    /// `<=`
    Le,
    /// `<`
    Lt,
}

impl fmt::Display for Tok {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let text = match self {
            Tok::Ident(name) => return write!(f, "`{name}`"),
            Tok::Num(n) => return write!(f, "`{n}`"),
            Tok::Path(p) => return write!(f, "`{p}`"),
            Tok::LParen => "(",
            Tok::RParen => ")",
            Tok::LBrace => "{",
            Tok::RBrace => "}",
            Tok::LBracket => "[",
            Tok::RBracket => "]",
            Tok::Comma => ",",
            Tok::Colon => ":",
            Tok::Semi => ";",
            Tok::Bar => "|",
            Tok::Dot => ".",
            Tok::Star => "*",
            Tok::FatArrow => "=>",
            Tok::Define => ":=",
            Tok::Arrow => "->",
            Tok::LeftArrow => "<-",
            Tok::Iff => "<->",
            Tok::And => "/\\",
            Tok::Or => "\\/",
            Tok::Eq => "=",
            Tok::Plus => "+",
            Tok::Minus => "-",
            Tok::Le => "<=",
            Tok::Lt => "<",
        };
        write!(f, "`{text}`")
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Token {
    pub tok: Tok,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LexError {
    pub span: Span,
    pub message: String,
}

/// A source line with its indentation and tokens. Blank and comment-only
/// lines are dropped by [`lex_lines`].
#[derive(Clone, Debug)]
pub struct Line {
    pub number: u32,
    pub indent: u32,
    pub tokens: Vec<Token>,
    pub text: String,
}

/// Strips a trailing `-- comment`, respecting nothing else (there are no
/// string literals in the language).
fn strip_comment(text: &str) -> &str {
    match text.find("--") {
        Some(index) => &text[..index],
        None => text,
    }
}

fn is_ident_start(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_'
}

fn is_ident_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_' || c == '\'' || c == '.'
}

/// Lexes one line. `line` is 1-based. Columns are 1-based character
/// offsets.
pub fn lex_line(number: u32, text: &str) -> Result<Vec<Token>, LexError> {
    let code = strip_comment(text);
    let chars: Vec<char> = code.chars().collect();
    let mut tokens = Vec::new();
    let mut i = 0;
    let after_import = |tokens: &Vec<Token>| {
        tokens.len() == 1 && matches!(&tokens[0].tok, Tok::Ident(name) if name == "import")
    };
    while i < chars.len() {
        let c = chars[i];
        let col = i as u32 + 1;
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        if after_import(&tokens) {
            let start = i;
            while i < chars.len() && !chars[i].is_whitespace() {
                i += 1;
            }
            let path: String = chars[start..i].iter().collect();
            tokens.push(Token {
                tok: Tok::Path(path),
                span: Span {
                    line: number,
                    col,
                    end_line: number,
                    end_col: i as u32 + 1,
                },
            });
            continue;
        }
        if is_ident_start(c) {
            let start = i;
            while i < chars.len() && is_ident_char(chars[i]) {
                i += 1;
            }
            // A trailing dot belongs to what follows (`x.` never ends a name).
            while i > start + 1 && chars[i - 1] == '.' {
                i -= 1;
            }
            let name: String = chars[start..i].iter().collect();
            tokens.push(Token {
                tok: Tok::Ident(name),
                span: Span {
                    line: number,
                    col,
                    end_line: number,
                    end_col: i as u32 + 1,
                },
            });
            continue;
        }
        if c.is_ascii_digit() {
            let start = i;
            while i < chars.len() && chars[i].is_ascii_digit() {
                i += 1;
            }
            let digits: String = chars[start..i].iter().collect();
            let value = digits.parse::<u64>().map_err(|_| LexError {
                span: Span::point(number, col),
                message: format!("numeral `{digits}` is too large"),
            })?;
            tokens.push(Token {
                tok: Tok::Num(value),
                span: Span {
                    line: number,
                    col,
                    end_line: number,
                    end_col: i as u32 + 1,
                },
            });
            continue;
        }
        let rest: String = chars[i..].iter().take(3).collect();
        let (tok, len) = if rest.starts_with("<->") {
            (Tok::Iff, 3)
        } else if rest.starts_with(":=") {
            (Tok::Define, 2)
        } else if rest.starts_with("=>") {
            (Tok::FatArrow, 2)
        } else if rest.starts_with("->") {
            (Tok::Arrow, 2)
        } else if rest.starts_with("<-") {
            (Tok::LeftArrow, 2)
        } else if rest.starts_with("<=") {
            (Tok::Le, 2)
        } else if rest.starts_with("/\\") {
            (Tok::And, 2)
        } else if rest.starts_with("\\/") {
            (Tok::Or, 2)
        } else {
            let single = match c {
                '(' => Tok::LParen,
                ')' => Tok::RParen,
                '{' => Tok::LBrace,
                '}' => Tok::RBrace,
                '[' => Tok::LBracket,
                ']' => Tok::RBracket,
                ',' => Tok::Comma,
                ':' => Tok::Colon,
                ';' => Tok::Semi,
                '|' => Tok::Bar,
                '.' => Tok::Dot,
                '*' => Tok::Star,
                '=' => Tok::Eq,
                '+' => Tok::Plus,
                '-' => Tok::Minus,
                '<' => Tok::Lt,
                '∧' => Tok::And,
                '∨' => Tok::Or,
                '→' => Tok::Arrow,
                '↔' => Tok::Iff,
                '¬' => Tok::Ident("not".to_string()),
                '∀' => Tok::Ident("forall".to_string()),
                '∃' => Tok::Ident("exists".to_string()),
                '∈' => Tok::Ident("in".to_string()),
                '⊆' => Tok::Ident("subset".to_string()),
                'λ' => Tok::Ident("fun".to_string()),
                '≠' => {
                    return Err(LexError {
                        span: Span::point(number, col),
                        message: "`≠` is not supported; write `not (a = b)`".to_string(),
                    })
                }
                other => {
                    return Err(LexError {
                        span: Span::point(number, col),
                        message: if other.is_ascii() {
                            format!("unexpected character `{other}`")
                        } else {
                            format!(
                                "unexpected character `{other}`; only the connective and quantifier symbols are accepted as Unicode aliases"
                            )
                        },
                    })
                }
            };
            (single, 1)
        };
        tokens.push(Token {
            tok,
            span: Span {
                line: number,
                col,
                end_line: number,
                end_col: col + len as u32,
            },
        });
        i += len;
    }
    Ok(tokens)
}

/// Lexes a whole source into non-blank lines with indentation.
pub fn lex_lines(source: &str) -> Result<Vec<Line>, LexError> {
    let mut lines = Vec::new();
    for (index, raw) in source.lines().enumerate() {
        let number = index as u32 + 1;
        let text = raw.trim_end_matches('\r');
        let indent = text.chars().take_while(|c| c.is_whitespace()).count() as u32;
        let tokens = lex_line(number, text)?;
        if tokens.is_empty() {
            continue;
        }
        lines.push(Line {
            number,
            indent,
            tokens,
            text: text.to_string(),
        });
    }
    Ok(lines)
}
