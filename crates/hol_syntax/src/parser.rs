//! The parser.
//!
//! Commands start at column zero; their continuation lines are indented.
//! A theorem's tactic block is the indented lines after `:= by`, and
//! tactic structure (`cases ... with` arms, `have ... := by` blocks)
//! follows indentation. Expressions, types, parameters, and proof
//! expressions are parsed from token streams by [`Parser`].

use crate::ast::*;
use crate::lexer::{lex_lines, LexError, Line, Span, Tok, Token};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseError {
    pub span: Span,
    pub message: String,
}

impl From<LexError> for ParseError {
    fn from(err: LexError) -> ParseError {
        ParseError {
            span: err.span,
            message: err.message,
        }
    }
}

type Result<T> = std::result::Result<T, ParseError>;

fn err<T>(span: Span, message: impl Into<String>) -> Result<T> {
    Err(ParseError {
        span,
        message: message.into(),
    })
}

/// The result of parsing a file: the commands that parsed and the
/// errors for those that did not. A failed command is skipped so later
/// commands still get checked.
#[derive(Clone, Debug, Default)]
pub struct ParseOutput {
    pub file: File,
    pub errors: Vec<ParseError>,
}

pub fn parse_file(source: &str) -> ParseOutput {
    let lines = match lex_lines(source) {
        Ok(lines) => lines,
        Err(err) => {
            return ParseOutput {
                file: File::default(),
                errors: vec![err.into()],
            }
        }
    };
    let mut output = ParseOutput::default();
    let mut i = 0;
    while i < lines.len() {
        if lines[i].indent > 0 {
            output.errors.push(ParseError {
                span: lines[i].tokens[0].span,
                message: "unexpected indented line; commands start at the left margin".to_string(),
            });
            i += 1;
            continue;
        }
        let start = i;
        i += 1;
        // Continuation lines are indented; `| ...` lines at the margin
        // continue a `data` or `defrec` declaration.
        while i < lines.len() && (lines[i].indent > 0 || is_bar_line(&lines[i])) {
            i += 1;
        }
        match parse_command(&lines[start..i]) {
            Ok(command) => output.file.commands.push(command),
            Err(error) => output.errors.push(error),
        }
    }
    output
}

fn group_span(lines: &[Line]) -> Span {
    let first = lines[0].tokens[0].span;
    let last = lines[lines.len() - 1]
        .tokens
        .last()
        .map(|t| t.span)
        .unwrap_or(first);
    first.to(last)
}

fn joined_tokens(lines: &[Line]) -> Vec<Token> {
    lines
        .iter()
        .flat_map(|line| line.tokens.iter().cloned())
        .collect()
}

fn is_bar_line(line: &Line) -> bool {
    matches!(line.tokens[0].tok, Tok::Bar)
}

fn parse_command(lines: &[Line]) -> Result<Command> {
    let head = &lines[0].tokens[0];
    let Tok::Ident(keyword) = &head.tok else {
        return err(
            head.span,
            format!("expected a command keyword, found {}", head.tok),
        );
    };
    let span = group_span(lines);
    match keyword.as_str() {
        "import" => parse_import(lines, span),
        "mode" => {
            let tokens = joined_tokens(lines);
            let mut p = Parser::new(&tokens[1..], span);
            let name = p.ident("a mode name")?;
            let mode = match name.name.as_str() {
                "constructive" => Mode::Constructive,
                "classical" => Mode::Classical,
                other => return err(name.span, format!("unknown mode `{other}`; expected `constructive` or `classical`")),
            };
            p.finish()?;
            Ok(Command::Mode(mode, span))
        }
        "logic" | "tier" => {
            let tokens = joined_tokens(lines);
            let mut p = Parser::new(&tokens[1..], span);
            let name = p.ident("a logic tier")?;
            let Some(tier) = Tier::parse(&name.name) else {
                return err(name.span, format!("unknown logic tier `{}`; expected `fol`, `fol_nat`, or `hol`", name.name));
            };
            p.finish()?;
            Ok(Command::Logic(tier, span))
        }
        "sort" => {
            let tokens = joined_tokens(lines);
            let mut p = Parser::new(&tokens[1..], span);
            let name = p.ident("a sort name")?;
            p.finish()?;
            Ok(Command::Sort(name, span))
        }
        "const" | "func" => {
            let tokens = joined_tokens(lines);
            let mut p = Parser::new(&tokens[1..], span);
            let name = p.ident("a name")?;
            p.expect(&Tok::Colon)?;
            let ty = p.parse_type()?;
            p.finish()?;
            Ok(if keyword == "const" {
                Command::Const { name, ty, span }
            } else {
                Command::Func { name, ty, span }
            })
        }
        "pred" => {
            let tokens = joined_tokens(lines);
            let mut p = Parser::new(&tokens[1..], span);
            let name = p.ident("a predicate name")?;
            let mut args = Vec::new();
            if p.eat(&Tok::LParen) {
                if !p.at(&Tok::RParen) {
                    loop {
                        args.push(p.parse_type()?);
                        if !p.eat(&Tok::Comma) {
                            break;
                        }
                    }
                }
                p.expect(&Tok::RParen)?;
            }
            p.finish()?;
            Ok(Command::Pred { name, args, span })
        }
        "def" => {
            let tokens = joined_tokens(lines);
            let mut p = Parser::new(&tokens[1..], span);
            let name = p.ident("a definition name")?;
            let params = p.parse_params()?;
            p.expect(&Tok::Colon)?;
            let result = p.parse_type()?;
            p.expect(&Tok::Define)?;
            let body = p.parse_expr()?;
            p.finish()?;
            Ok(Command::Def {
                name,
                params,
                result,
                body,
                span,
            })
        }
        "axiom" => {
            let tokens = joined_tokens(lines);
            let mut p = Parser::new(&tokens[1..], span);
            let name = p.ident("an axiom name")?;
            let params = p.parse_params()?;
            p.expect(&Tok::Colon)?;
            let statement = p.parse_expr()?;
            p.finish()?;
            Ok(Command::Axiom {
                name,
                params,
                statement,
                span,
            })
        }
        "theorem" | "lemma" => parse_theorem(lines, span),
        "data" => parse_data(lines, span),
        "defrec" => parse_defrec(lines, span),
        "namespace" | "end" => {
            let tokens = joined_tokens(lines);
            let mut p = Parser::new(&tokens[1..], span);
            let name = p.ident("a namespace name")?;
            p.finish()?;
            Ok(if keyword == "namespace" {
                Command::Namespace(name, span)
            } else {
                Command::End(name, span)
            })
        }
        other => err(
            head.span,
            format!("unknown command `{other}`; expected `theorem`, `def`, `sort`, `const`, `func`, `pred`, `axiom`, `data`, `defrec`, `import`, `mode`, or `logic`"),
        ),
    }
}

fn parse_import(lines: &[Line], span: Span) -> Result<Command> {
    let tokens = joined_tokens(lines);
    let mut p = Parser::new(&tokens[1..], span);
    let (path, path_span) = match p.next() {
        Some(Token {
            tok: Tok::Path(path),
            span,
        }) => (path.clone(), *span),
        Some(other) => return err(other.span, "expected an import path"),
        None => return err(span, "expected an import path after `import`"),
    };
    let _ = path_span;
    let mut alias = None;
    if p.eat_ident("as") {
        alias = Some(p.ident("an import alias")?);
    }
    p.finish()?;
    Ok(Command::Import { path, alias, span })
}

fn parse_theorem(lines: &[Line], span: Span) -> Result<Command> {
    // Find the line holding `:= by`.
    let mut header_end: Option<(usize, usize)> = None;
    'outer: for (li, line) in lines.iter().enumerate() {
        for (ti, token) in line.tokens.iter().enumerate() {
            if token.tok == Tok::Define {
                if let Some(next) = line.tokens.get(ti + 1) {
                    if matches!(&next.tok, Tok::Ident(name) if name == "by") {
                        header_end = Some((li, ti));
                        break 'outer;
                    }
                }
            }
        }
    }
    let Some((by_line, define_index)) = header_end else {
        return err(
            group_span(&lines[..1]),
            "expected `:= by` after the theorem statement",
        );
    };
    let mut header_tokens: Vec<Token> = lines[..by_line]
        .iter()
        .flat_map(|line| line.tokens.iter().cloned())
        .collect();
    header_tokens.extend(lines[by_line].tokens[..define_index].iter().cloned());
    let by_token = &lines[by_line].tokens[define_index + 1];
    let header_span = lines[0].tokens[0].span.to(by_token.span);
    if lines[by_line].tokens.len() > define_index + 2 {
        return err(
            lines[by_line].tokens[define_index + 2].span,
            "tactics start on the line after `by`, indented",
        );
    }
    let mut p = Parser::new(&header_tokens[1..], header_span);
    let name = p.ident("a theorem name")?;
    let params = p.parse_params()?;
    p.expect(&Tok::Colon)?;
    let statement = p.parse_expr()?;
    p.finish()?;

    let block = &lines[by_line + 1..];
    if block.is_empty() {
        return err(
            by_token.span,
            "the proof after `by` is empty; add at least one tactic",
        );
    }
    let base = block[0].indent;
    let (proof, next) = parse_block(block, 0, base)?;
    if next < block.len() {
        return err(
            block[next].tokens[0].span,
            "unexpected indentation; this line does not belong to the proof",
        );
    }
    Ok(Command::Theorem {
        name,
        params,
        statement,
        proof,
        span,
        header_span,
    })
}

fn parse_data(lines: &[Line], span: Span) -> Result<Command> {
    let mut header: Vec<Token> = Vec::new();
    let mut arm_tokens: Vec<Vec<Token>> = Vec::new();
    for line in lines {
        if is_bar_line(line) {
            arm_tokens.push(line.tokens.clone());
        } else if arm_tokens.is_empty() {
            header.extend(line.tokens.iter().cloned());
        } else {
            arm_tokens
                .last_mut()
                .unwrap()
                .extend(line.tokens.iter().cloned());
        }
    }
    // Constructors may also be written inline: `data Bit | off | on`.
    let mut inline: Vec<Vec<Token>> = Vec::new();
    let mut current: Vec<Token> = Vec::new();
    let mut real_header: Vec<Token> = Vec::new();
    let mut seen_bar = false;
    for token in header {
        if token.tok == Tok::Bar {
            if seen_bar {
                inline.push(std::mem::take(&mut current));
            }
            seen_bar = true;
            current.push(token);
        } else if seen_bar {
            current.push(token);
        } else {
            real_header.push(token);
        }
    }
    if seen_bar {
        inline.push(current);
    }
    inline.extend(arm_tokens);
    let mut p = Parser::new(&real_header[1..], span);
    let name = p.ident("a data type name")?;
    let mut params = Vec::new();
    while p.eat(&Tok::LParen) {
        let param = p.ident("a type parameter")?;
        p.expect(&Tok::Colon)?;
        let kind = p.ident("`Type`")?;
        if kind.name != "Type" {
            return err(kind.span, "data type parameters have kind `Type`");
        }
        p.expect(&Tok::RParen)?;
        params.push(param);
    }
    p.finish()?;
    let mut ctors = Vec::new();
    for tokens in inline {
        let arm_span = tokens[0].span.to(tokens[tokens.len() - 1].span);
        let mut p = Parser::new(&tokens[1..], arm_span);
        let ctor = p.ident("a constructor name")?;
        let mut args = Vec::new();
        if p.eat(&Tok::LParen) {
            loop {
                args.push(p.parse_type()?);
                if !p.eat(&Tok::Comma) {
                    break;
                }
            }
            p.expect(&Tok::RParen)?;
        }
        p.finish()?;
        ctors.push(CtorDecl {
            name: ctor,
            args,
            span: arm_span,
        });
    }
    if ctors.is_empty() {
        return err(span, "a data type needs at least one `| constructor` line");
    }
    Ok(Command::Data {
        name,
        params,
        ctors,
        span,
    })
}

fn parse_defrec(lines: &[Line], span: Span) -> Result<Command> {
    let mut header: Vec<Token> = Vec::new();
    let mut arm_tokens: Vec<Vec<Token>> = Vec::new();
    for line in lines {
        if is_bar_line(line) {
            arm_tokens.push(line.tokens.clone());
        } else if arm_tokens.is_empty() {
            header.extend(line.tokens.iter().cloned());
        } else {
            arm_tokens
                .last_mut()
                .unwrap()
                .extend(line.tokens.iter().cloned());
        }
    }
    let mut p = Parser::new(&header[1..], span);
    let name = p.ident("a function name")?;
    let params = p.parse_params()?;
    p.expect(&Tok::Colon)?;
    let result = p.parse_type()?;
    p.finish()?;
    let mut arms = Vec::new();
    for tokens in arm_tokens {
        let arm_span = tokens[0].span.to(tokens[tokens.len() - 1].span);
        let mut p = Parser::new(&tokens[1..], arm_span);
        let ctor = p.ident("a constructor name")?;
        let mut binders = Vec::new();
        while !p.at(&Tok::FatArrow) {
            binders.push(p.ident("a binder name or `=>`")?);
        }
        p.expect(&Tok::FatArrow)?;
        let body = p.parse_expr()?;
        p.finish()?;
        arms.push(RecArm {
            ctor,
            binders,
            body,
            span: arm_span,
        });
    }
    if arms.is_empty() {
        return err(
            span,
            "a `defrec` needs one `| constructor ... => body` line per constructor",
        );
    }
    Ok(Command::Defrec {
        name,
        params,
        result,
        arms,
        span,
    })
}

// ---------------------------------------------------------------------
// Tactic blocks
// ---------------------------------------------------------------------

fn ends_with_ident(tokens: &[Token], name: &str) -> bool {
    matches!(tokens.last(), Some(Token { tok: Tok::Ident(n), .. }) if n == name)
}

fn ends_with_define_by(tokens: &[Token]) -> bool {
    tokens.len() >= 2
        && tokens[tokens.len() - 2].tok == Tok::Define
        && ends_with_ident(tokens, "by")
}

/// Parses tactic lines at indentation `base` starting at `start`.
/// Returns the tactics and the index of the first line not consumed.
pub fn parse_block(lines: &[Line], start: usize, base: u32) -> Result<(Vec<Tactic>, usize)> {
    let mut tactics = Vec::new();
    let mut i = start;
    while i < lines.len() && lines[i].indent >= base {
        let line = &lines[i];
        if line.indent > base {
            return err(
                line.tokens[0].span,
                "unexpected indentation; tactics in one block start at the same column",
            );
        }
        if is_bar_line(line) {
            return err(
                line.tokens[0].span,
                "a `|` case arm must follow a `cases ... with` or `induction ... with` line",
            );
        }
        i += 1;
        let mut tokens = line.tokens.clone();
        // Plain continuation lines: deeper indentation, not an arm, and the
        // previous line did not open a block.
        let opens_block = ends_with_ident(&tokens, "with") || ends_with_define_by(&tokens);
        if !opens_block {
            while i < lines.len() && is_continuation(&lines[i], base) {
                tokens.extend(lines[i].tokens.iter().cloned());
                i += 1;
            }
        }
        let line_span = tokens[0].span.to(tokens[tokens.len() - 1].span);
        if ends_with_ident(&tokens, "with") {
            let mut arms = Vec::new();
            while i < lines.len() && lines[i].indent == base && is_bar_line(&lines[i]) {
                let arm_line = &lines[i];
                let header = &arm_line.tokens;
                let arm_span = header[0].span.to(header[header.len() - 1].span);
                let mut p = Parser::new(&header[1..], arm_span);
                let ctor = p.ident("a case name such as `left`, `right`, or `intro`")?;
                let mut binders = Vec::new();
                while !p.at(&Tok::FatArrow) {
                    binders.push(p.ident("a binder name or `=>`")?);
                }
                p.expect(&Tok::FatArrow)?;
                p.finish()?;
                i += 1;
                if i >= lines.len() || lines[i].indent <= base {
                    return err(
                        arm_span,
                        "this case arm has an empty body; indent at least one tactic under it",
                    );
                }
                let body_base = lines[i].indent;
                let (body, next) = parse_block(lines, i, body_base)?;
                i = next;
                let end_span = body.last().map(|t| t.span).unwrap_or(arm_span);
                arms.push(CaseArm {
                    ctor,
                    binders,
                    body,
                    span: arm_span.to(end_span),
                });
            }
            if arms.is_empty() {
                return err(line_span, "expected `| ... =>` case arms after `with`");
            }
            let kind = parse_with_tactic(&tokens, line_span, arms)?;
            let end = tactics_end_span(&kind).unwrap_or(line_span);
            tactics.push(Tactic {
                kind,
                span: line_span.to(end),
            });
            continue;
        }
        if ends_with_define_by(&tokens) {
            if i >= lines.len() || lines[i].indent <= base {
                return err(line_span, "expected an indented tactic block after `:= by`");
            }
            let body_base = lines[i].indent;
            let (body, next) = parse_block(lines, i, body_base)?;
            i = next;
            let end = body.last().map(|t| t.span).unwrap_or(line_span);
            let kind = parse_have_block(&tokens[..tokens.len() - 2], line_span, body)?;
            tactics.push(Tactic {
                kind,
                span: line_span.to(end),
            });
            continue;
        }
        let kind = parse_tactic_line(&tokens, line_span)?;
        tactics.push(Tactic {
            kind,
            span: line_span,
        });
    }
    Ok((tactics, i))
}

/// A deeper-indented line continues the tactic above it, as does a line
/// at the same indent that only closes a bracket opened above.
fn is_continuation(line: &Line, base: u32) -> bool {
    if is_bar_line(line) {
        return false;
    }
    if line.indent > base {
        return true;
    }
    line.indent == base
        && matches!(
            line.tokens[0].tok,
            Tok::RBrace | Tok::RParen | Tok::RBracket
        )
}

fn tactics_end_span(kind: &TacticKind) -> Option<Span> {
    match kind {
        TacticKind::Cases { arms, .. } | TacticKind::Induction { arms, .. } => {
            arms.last().map(|arm| arm.span)
        }
        _ => None,
    }
}

fn parse_with_tactic(tokens: &[Token], span: Span, arms: Vec<CaseArm>) -> Result<TacticKind> {
    let body = &tokens[..tokens.len() - 1];
    let mut p = Parser::new(body, span);
    let head = p.ident("a tactic")?;
    match head.name.as_str() {
        "cases" => {
            let scrutinee = p.parse_proof_expr()?;
            p.finish()?;
            Ok(TacticKind::Cases { scrutinee, arms })
        }
        "induction" => {
            let var = p.ident("a variable to induct on")?;
            let mut generalizing = Vec::new();
            if p.eat_ident("generalizing") {
                while !p.done() {
                    generalizing.push(p.ident("a variable name")?);
                }
            }
            p.finish()?;
            Ok(TacticKind::Induction {
                var,
                generalizing,
                arms,
            })
        }
        other => err(
            head.span,
            format!("`{other}` does not take `with` case arms"),
        ),
    }
}

fn parse_have_block(tokens: &[Token], span: Span, body: Vec<Tactic>) -> Result<TacticKind> {
    let mut p = Parser::new(tokens, span);
    let head = p.ident("`have`")?;
    if head.name != "have" {
        return err(head.span, "only `have name : P := by` takes a tactic block");
    }
    let name = p.ident("a hypothesis name")?;
    p.expect(&Tok::Colon)?;
    let stated = p.parse_expr()?;
    p.finish()?;
    Ok(TacticKind::Have {
        name,
        stated: Some(stated),
        proof: HaveProof::Block(body),
    })
}

fn parse_tactic_line(tokens: &[Token], span: Span) -> Result<TacticKind> {
    let mut p = Parser::new(tokens, span);
    let head = p.ident("a tactic")?;
    let kind = match head.name.as_str() {
        "intro" | "intros" => {
            let mut names = Vec::new();
            while !p.done() {
                names.push(p.ident("a hypothesis or variable name")?);
            }
            if names.is_empty() {
                return err(
                    head.span,
                    "`intro` needs a name for what it introduces, as in `intro h`",
                );
            }
            TacticKind::Intro(names)
        }
        "revert" => TacticKind::Revert(p.ident("a hypothesis name")?),
        "exact" => TacticKind::Exact(p.parse_proof_expr()?),
        "apply" => TacticKind::Apply(p.parse_proof_expr()?),
        "trivial" => TacticKind::Trivial,
        "assumption" => TacticKind::Assumption,
        "split" | "constructor" => TacticKind::Split,
        "left" => TacticKind::Left,
        "right" => TacticKind::Right,
        "exists" | "use" => TacticKind::Exists(p.parse_expr()?),
        "refl" | "rfl" => TacticKind::Refl,
        "rewrite" | "rw" => {
            let all = p.eat_ident("all");
            let dir = if p.eat(&Tok::LeftArrow) {
                RewriteDir::RightToLeft
            } else {
                p.eat(&Tok::Arrow);
                RewriteDir::LeftToRight
            };
            let proof = p.parse_proof_expr()?;
            let at = if p.eat_ident("at") {
                Some(p.ident("a hypothesis name")?)
            } else {
                None
            };
            TacticKind::Rewrite {
                dir,
                all,
                proof,
                at,
            }
        }
        "unfold" => {
            let name = p.ident("a definition name")?;
            let at = if p.eat_ident("at") {
                Some(p.ident("a hypothesis name")?)
            } else {
                None
            };
            TacticKind::Unfold(name, at)
        }
        "simp" => {
            let mut rules = Vec::new();
            if p.eat(&Tok::LBracket) {
                if !p.at(&Tok::RBracket) {
                    loop {
                        rules.push(p.parse_proof_expr()?);
                        if !p.eat(&Tok::Comma) {
                            break;
                        }
                    }
                }
                p.expect(&Tok::RBracket)?;
            }
            let target = if p.eat_ident("at") {
                if p.eat(&Tok::Star) {
                    SimpTarget::All
                } else {
                    SimpTarget::Hyp(p.ident("a hypothesis name or `*`")?)
                }
            } else {
                SimpTarget::Goal
            };
            TacticKind::Simp { rules, target }
        }
        "cases" | "induction" => {
            return err(
                span,
                format!(
                    "`{}` needs `with` and indented `| ... =>` case arms",
                    head.name
                ),
            )
        }
        "exfalso" => TacticKind::Exfalso,
        "contradiction" => TacticKind::Contradiction,
        "by_cases" => {
            let name = p.ident("a hypothesis name")?;
            p.expect(&Tok::Colon)?;
            let prop = p.parse_expr()?;
            TacticKind::ByCases { name, prop }
        }
        "by_contra" => TacticKind::ByContra(p.ident("a hypothesis name")?),
        "show_goal" | "print_state" => TacticKind::ShowGoal,
        "sorry" | "admit" => TacticKind::Sorry,
        "have" => {
            let name = p.ident("a hypothesis name")?;
            let stated = if p.eat(&Tok::Colon) {
                Some(p.parse_expr()?)
            } else {
                None
            };
            let proof = if p.eat(&Tok::Define) {
                if p.at_ident("by") {
                    return err(
                        span,
                        "`have ... := by` needs an indented tactic block on the following lines",
                    );
                }
                HaveProof::Expr(p.parse_proof_expr()?)
            } else {
                if stated.is_none() {
                    return err(
                        span,
                        "`have` needs a statement (`have h : P`) or a proof (`have h := expr`)",
                    );
                }
                HaveProof::Subgoal
            };
            TacticKind::Have {
                name,
                stated,
                proof,
            }
        }
        "show" => TacticKind::Show(p.parse_expr()?),
        "obtain" => {
            let mut names = Vec::new();
            while !p.at(&Tok::Define) {
                names.push(p.ident("a name or `:=`")?);
            }
            p.expect(&Tok::Define)?;
            let proof = p.parse_proof_expr()?;
            TacticKind::Obtain { names, proof }
        }
        other => return err(head.span, format!("unknown tactic `{other}`")),
    };
    p.finish()?;
    Ok(kind)
}

// ---------------------------------------------------------------------
// Token-level parser
// ---------------------------------------------------------------------

pub struct Parser<'a> {
    tokens: &'a [Token],
    pos: usize,
    span: Span,
}

impl<'a> Parser<'a> {
    pub fn new(tokens: &'a [Token], span: Span) -> Parser<'a> {
        Parser {
            tokens,
            pos: 0,
            span,
        }
    }

    fn peek(&self) -> Option<&'a Token> {
        self.tokens.get(self.pos)
    }

    fn peek_at(&self, offset: usize) -> Option<&'a Token> {
        self.tokens.get(self.pos + offset)
    }

    fn next(&mut self) -> Option<&'a Token> {
        let token = self.tokens.get(self.pos);
        if token.is_some() {
            self.pos += 1;
        }
        token
    }

    fn done(&self) -> bool {
        self.pos >= self.tokens.len()
    }

    fn end_span(&self) -> Span {
        match self.tokens.last() {
            Some(token) => Span::point(token.span.end_line, token.span.end_col),
            None => self.span,
        }
    }

    fn at(&self, tok: &Tok) -> bool {
        self.peek().map(|t| &t.tok == tok).unwrap_or(false)
    }

    fn at_ident(&self, name: &str) -> bool {
        matches!(self.peek(), Some(Token { tok: Tok::Ident(n), .. }) if n == name)
    }

    fn eat(&mut self, tok: &Tok) -> bool {
        if self.at(tok) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn eat_ident(&mut self, name: &str) -> bool {
        if self.at_ident(name) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn expect(&mut self, tok: &Tok) -> Result<Span> {
        match self.peek() {
            Some(token) if &token.tok == tok => {
                self.pos += 1;
                Ok(token.span)
            }
            Some(token) => err(token.span, format!("expected {tok}, found {}", token.tok)),
            None => err(self.end_span(), format!("expected {tok}")),
        }
    }

    fn ident(&mut self, what: &str) -> Result<Ident> {
        match self.peek() {
            Some(Token {
                tok: Tok::Ident(name),
                span,
            }) => {
                self.pos += 1;
                Ok(Ident::new(name, *span))
            }
            Some(token) => err(token.span, format!("expected {what}, found {}", token.tok)),
            None => err(self.end_span(), format!("expected {what}")),
        }
    }

    fn finish(&self) -> Result<()> {
        match self.peek() {
            None => Ok(()),
            Some(token) => err(token.span, format!("unexpected {}", token.tok)),
        }
    }

    // ---- types ----

    pub fn parse_type(&mut self) -> Result<TypeExpr> {
        let dom = self.parse_type_app()?;
        if self.eat(&Tok::Arrow) {
            let cod = self.parse_type()?;
            let span = dom.span().to(cod.span());
            return Ok(TypeExpr::Fun(Box::new(dom), Box::new(cod), span));
        }
        Ok(dom)
    }

    fn parse_type_app(&mut self) -> Result<TypeExpr> {
        let head = self.parse_type_atom()?;
        let TypeExpr::Named(name, mut args, mut span) = head else {
            return Ok(head);
        };
        while let Some(token) = self.peek() {
            match &token.tok {
                Tok::Ident(n) if !is_type_keyword_stop(n) => {
                    let arg = self.parse_type_atom()?;
                    span = span.to(arg.span());
                    args.push(arg);
                }
                Tok::LParen => {
                    let arg = self.parse_type_atom()?;
                    span = span.to(arg.span());
                    args.push(arg);
                }
                _ => break,
            }
        }
        Ok(TypeExpr::Named(name, args, span))
    }

    fn parse_type_atom(&mut self) -> Result<TypeExpr> {
        match self.next() {
            Some(Token {
                tok: Tok::Ident(name),
                span,
            }) => Ok(TypeExpr::Named(Ident::new(name, *span), vec![], *span)),
            Some(Token {
                tok: Tok::LParen,
                span,
            }) => {
                let inner = self.parse_type()?;
                let close = self.expect(&Tok::RParen)?;
                Ok(match inner {
                    TypeExpr::Named(name, args, _) => TypeExpr::Named(name, args, span.to(close)),
                    TypeExpr::Fun(a, b, _) => TypeExpr::Fun(a, b, span.to(close)),
                })
            }
            Some(token) => err(token.span, format!("expected a type, found {}", token.tok)),
            None => err(self.end_span(), "expected a type"),
        }
    }

    // ---- parameters ----

    pub fn parse_params(&mut self) -> Result<Vec<Param>> {
        let mut params = Vec::new();
        while self.at(&Tok::LParen) {
            let open = self.expect(&Tok::LParen)?;
            let mut names = Vec::new();
            while !self.at(&Tok::Colon) {
                names.push(self.ident("a parameter name or `:`")?);
            }
            if names.is_empty() {
                return err(open, "expected a parameter name before `:`");
            }
            self.expect(&Tok::Colon)?;
            let start = self.pos;
            let mut depth = 0usize;
            let mut end = start;
            while let Some(token) = self.tokens.get(end) {
                match token.tok {
                    Tok::LParen | Tok::LBrace | Tok::LBracket => depth += 1,
                    Tok::RParen | Tok::RBrace | Tok::RBracket => {
                        if depth == 0 {
                            break;
                        }
                        depth -= 1;
                    }
                    _ => {}
                }
                end += 1;
            }
            let annotation_tokens = &self.tokens[start..end];
            if annotation_tokens.is_empty() {
                return err(self.end_span(), "expected a type or formula after `:`");
            }
            let annotation_span = annotation_tokens[0]
                .span
                .to(annotation_tokens[annotation_tokens.len() - 1].span);
            let annotation = if annotation_tokens.len() == 1
                && matches!(&annotation_tokens[0].tok, Tok::Ident(n) if n == "Type")
            {
                Annotation::TypeKind(annotation_span)
            } else {
                let mut type_parser = Parser::new(annotation_tokens, annotation_span);
                let as_type = type_parser.parse_type().ok().filter(|_| type_parser.done());
                let mut expr_parser = Parser::new(annotation_tokens, annotation_span);
                let as_expr = expr_parser.parse_expr();
                let as_expr = match as_expr {
                    Ok(expr) if expr_parser.done() => Ok(expr),
                    Ok(_) => err(
                        expr_parser.peek().unwrap().span,
                        "unexpected token in parameter annotation",
                    ),
                    Err(e) => Err(e),
                };
                match (as_type, as_expr) {
                    (Some(ty), Ok(expr)) => Annotation::Type(ty, Some(expr)),
                    (Some(ty), Err(_)) => Annotation::Type(ty, None),
                    (None, Ok(expr)) => Annotation::Formula(expr),
                    (None, Err(e)) => return Err(e),
                }
            };
            self.pos = end;
            let close = self.expect(&Tok::RParen)?;
            params.push(Param {
                names,
                annotation,
                span: open.to(close),
            });
        }
        Ok(params)
    }

    // ---- expressions ----

    pub fn parse_expr(&mut self) -> Result<Expr> {
        self.parse_imp()
    }

    fn parse_imp(&mut self) -> Result<Expr> {
        let lhs = self.parse_iff()?;
        if self.eat(&Tok::Arrow) {
            let rhs = self.parse_imp()?;
            let span = lhs.span().to(rhs.span());
            return Ok(Expr::Binary(BinOp::Imp, Box::new(lhs), Box::new(rhs), span));
        }
        Ok(lhs)
    }

    fn parse_iff(&mut self) -> Result<Expr> {
        let lhs = self.parse_or()?;
        if self.eat(&Tok::Iff) {
            let rhs = self.parse_iff()?;
            let span = lhs.span().to(rhs.span());
            return Ok(Expr::Binary(BinOp::Iff, Box::new(lhs), Box::new(rhs), span));
        }
        Ok(lhs)
    }

    fn parse_or(&mut self) -> Result<Expr> {
        let lhs = self.parse_and()?;
        if self.eat(&Tok::Or) {
            let rhs = self.parse_or()?;
            let span = lhs.span().to(rhs.span());
            return Ok(Expr::Binary(BinOp::Or, Box::new(lhs), Box::new(rhs), span));
        }
        Ok(lhs)
    }

    fn parse_and(&mut self) -> Result<Expr> {
        let lhs = self.parse_not()?;
        if self.eat(&Tok::And) {
            let rhs = self.parse_and()?;
            let span = lhs.span().to(rhs.span());
            return Ok(Expr::Binary(BinOp::And, Box::new(lhs), Box::new(rhs), span));
        }
        Ok(lhs)
    }

    fn parse_not(&mut self) -> Result<Expr> {
        if let Some(Token {
            tok: Tok::Ident(name),
            span,
        }) = self.peek()
        {
            if name == "not" {
                let start = *span;
                self.pos += 1;
                let inner = self.parse_not()?;
                let span = start.to(inner.span());
                return Ok(Expr::Not(Box::new(inner), span));
            }
        }
        self.parse_rel()
    }

    fn parse_rel(&mut self) -> Result<Expr> {
        let lhs = self.parse_arith()?;
        let op = match self.peek() {
            Some(Token { tok: Tok::Eq, .. }) => Some(BinOp::Eq),
            Some(Token { tok: Tok::Le, .. }) => Some(BinOp::Le),
            Some(Token { tok: Tok::Lt, .. }) => Some(BinOp::Lt),
            Some(Token {
                tok: Tok::Ident(n), ..
            }) if n == "in" => Some(BinOp::Mem),
            Some(Token {
                tok: Tok::Ident(n), ..
            }) if n == "subset" => Some(BinOp::Subset),
            _ => None,
        };
        if let Some(op) = op {
            self.pos += 1;
            let rhs = self.parse_arith()?;
            let span = lhs.span().to(rhs.span());
            return Ok(Expr::Binary(op, Box::new(lhs), Box::new(rhs), span));
        }
        Ok(lhs)
    }

    fn parse_arith(&mut self) -> Result<Expr> {
        let mut lhs = self.parse_mul()?;
        loop {
            let op = match self.peek() {
                Some(Token { tok: Tok::Plus, .. }) => BinOp::Add,
                Some(Token {
                    tok: Tok::Minus, ..
                }) => BinOp::Sub,
                _ => break,
            };
            self.pos += 1;
            let rhs = self.parse_mul()?;
            let span = lhs.span().to(rhs.span());
            lhs = Expr::Binary(op, Box::new(lhs), Box::new(rhs), span);
        }
        Ok(lhs)
    }

    fn parse_mul(&mut self) -> Result<Expr> {
        let mut lhs = self.parse_app()?;
        while self.at(&Tok::Star) {
            self.pos += 1;
            let rhs = self.parse_app()?;
            let span = lhs.span().to(rhs.span());
            lhs = Expr::Binary(BinOp::Mul, Box::new(lhs), Box::new(rhs), span);
        }
        Ok(lhs)
    }

    /// Application: `f(a, b)`, possibly repeated.
    pub fn parse_app(&mut self) -> Result<Expr> {
        if let Some(Token {
            tok: Tok::Ident(name),
            span,
        }) = self.peek()
        {
            if (name == "empty" || name == "univ")
                && matches!(
                    self.peek_at(1),
                    Some(Token {
                        tok: Tok::LParen,
                        ..
                    })
                )
            {
                let ident = Ident::new(name, *span);
                self.pos += 2;
                let ty = self.parse_type()?;
                let close = self.expect(&Tok::RParen)?;
                return Ok(Expr::TypeApp(ident, ty, span.to(close)));
            }
        }
        let mut head = self.parse_atom()?;
        while self.at(&Tok::LParen) {
            self.pos += 1;
            let mut args = Vec::new();
            if !self.at(&Tok::RParen) {
                loop {
                    args.push(self.parse_expr()?);
                    if !self.eat(&Tok::Comma) {
                        break;
                    }
                }
            }
            let close = self.expect(&Tok::RParen)?;
            let span = head.span().to(close);
            head = Expr::App(Box::new(head), args, span);
        }
        Ok(head)
    }

    fn parse_atom(&mut self) -> Result<Expr> {
        let Some(token) = self.next() else {
            return err(self.end_span(), "expected an expression");
        };
        match &token.tok {
            Tok::Ident(name) => match name.as_str() {
                "True" => Ok(Expr::True(token.span)),
                "False" => Ok(Expr::False(token.span)),
                "forall" => self.parse_binder(BinderKind::Forall, token.span),
                "exists" => self.parse_binder(BinderKind::Exists, token.span),
                "fun" => self.parse_binder(BinderKind::Fun, token.span),
                "not" => {
                    let inner = self.parse_not()?;
                    let span = token.span.to(inner.span());
                    Ok(Expr::Not(Box::new(inner), span))
                }
                _ => Ok(Expr::Var(Ident::new(name, token.span))),
            },
            Tok::Num(n) => Ok(Expr::Num(*n, token.span)),
            Tok::LParen => {
                let inner = self.parse_expr()?;
                self.expect(&Tok::RParen)?;
                Ok(inner)
            }
            Tok::LBrace => self.parse_set(token.span),
            other => err(token.span, format!("expected an expression, found {other}")),
        }
    }

    fn parse_set(&mut self, open: Span) -> Result<Expr> {
        // `{ x : T | P }` or `{a, b, c}`.
        if let (
            Some(Token {
                tok: Tok::Ident(name),
                span,
            }),
            Some(Token {
                tok: Tok::Colon, ..
            }),
        ) = (self.peek(), self.peek_at(1))
        {
            let var = Ident::new(name, *span);
            self.pos += 2;
            let ty = self.parse_type()?;
            self.expect(&Tok::Bar)?;
            let body = self.parse_expr()?;
            let close = self.expect(&Tok::RBrace)?;
            return Ok(Expr::SetBuilder(var, ty, Box::new(body), open.to(close)));
        }
        if self.at(&Tok::RBrace) {
            return err(
                open,
                "an empty set literal has no element type; write `empty(T)` instead",
            );
        }
        let mut elems = Vec::new();
        loop {
            elems.push(self.parse_expr()?);
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        let close = self.expect(&Tok::RBrace)?;
        Ok(Expr::SetLit(elems, open.to(close)))
    }

    fn parse_binder(&mut self, kind: BinderKind, start: Span) -> Result<Expr> {
        let mut binders = Vec::new();
        let separator = match kind {
            BinderKind::Fun => Tok::FatArrow,
            _ => Tok::Comma,
        };
        loop {
            if self.at(&Tok::LParen) {
                self.pos += 1;
                let mut names = Vec::new();
                while !self.at(&Tok::Colon) {
                    names.push(self.ident("a binder name or `:`")?);
                }
                self.expect(&Tok::Colon)?;
                let ty = self.parse_type()?;
                self.expect(&Tok::RParen)?;
                binders.push(Binder {
                    names,
                    ty: Some(ty),
                });
                if self.at(&separator) {
                    break;
                }
                continue;
            }
            let mut names = Vec::new();
            while let Some(Token {
                tok: Tok::Ident(_), ..
            }) = self.peek()
            {
                names.push(self.ident("a binder name")?);
            }
            if names.is_empty() {
                return match self.peek() {
                    Some(token) => err(
                        token.span,
                        format!("expected a binder name, found {}", token.tok),
                    ),
                    None => err(self.end_span(), "expected a binder name"),
                };
            }
            let ty = if self.eat(&Tok::Colon) {
                Some(self.parse_type()?)
            } else {
                None
            };
            binders.push(Binder { names, ty });
            break;
        }
        match kind {
            BinderKind::Fun => {
                self.expect(&Tok::FatArrow)?;
            }
            _ => {
                if !self.eat(&Tok::Comma) {
                    return match self.peek() {
                        Some(token) => err(
                            token.span,
                            format!(
                                "expected `,` after the quantifier's binders, found {}",
                                token.tok
                            ),
                        ),
                        None => err(
                            self.end_span(),
                            "expected `,` after the quantifier's binders",
                        ),
                    };
                }
            }
        }
        let body = self.parse_expr()?;
        let span = start.to(body.span());
        Ok(Expr::Binder(kind, binders, Box::new(body), span))
    }

    // ---- proof expressions ----

    pub fn parse_proof_expr(&mut self) -> Result<ProofExpr> {
        let mut head = self.parse_proof_atom()?;
        if self.at(&Tok::LBrace) {
            let open = self.expect(&Tok::LBrace)?;
            let mut args = Vec::new();
            if !self.at(&Tok::RBrace) {
                loop {
                    args.push(self.parse_inst_arg()?);
                    if !self.eat(&Tok::Semi) {
                        break;
                    }
                }
            }
            let close = self.expect(&Tok::RBrace)?;
            let span = head.span().to(open.to(close));
            head = ProofExpr::Inst(Box::new(head), args, span);
        }
        let mut args = Vec::new();
        while self.starts_proof_atom() {
            args.push(self.parse_proof_atom()?);
        }
        if args.is_empty() {
            return Ok(head);
        }
        let span = head.span().to(args[args.len() - 1].span());
        Ok(ProofExpr::App(Box::new(head), args, span))
    }

    fn starts_proof_atom(&self) -> bool {
        matches!(
            self.peek().map(|t| &t.tok),
            Some(Tok::Ident(_) | Tok::Num(_) | Tok::LParen | Tok::LBrace)
        ) && !self.at_ident("at")
            && !self.at_ident("with")
    }

    fn parse_proof_atom(&mut self) -> Result<ProofExpr> {
        let Some(token) = self.peek() else {
            return err(self.end_span(), "expected a proof or a term");
        };
        let mut atom = match &token.tok {
            Tok::Ident(name) => {
                let is_term_keyword = matches!(
                    name.as_str(),
                    "True" | "False" | "fun" | "forall" | "exists" | "not"
                );
                let followed_by_paren = matches!(
                    self.peek_at(1),
                    Some(Token {
                        tok: Tok::LParen,
                        ..
                    })
                );
                if is_term_keyword || followed_by_paren {
                    ProofExpr::Term(self.parse_app()?)
                } else {
                    self.pos += 1;
                    split_projections(name, token.span)
                }
            }
            Tok::Num(_) | Tok::LBrace => ProofExpr::Term(self.parse_app()?),
            Tok::LParen => {
                // Try a parenthesized proof expression first, then fall
                // back to a term such as `(x = y)`.
                let start = self.pos;
                self.pos += 1;
                let as_proof = self
                    .parse_proof_expr()
                    .ok()
                    .filter(|_| self.at(&Tok::RParen));
                match as_proof {
                    Some(inner) => {
                        let close = self.expect(&Tok::RParen)?;
                        let span = token.span.to(close);
                        match inner {
                            ProofExpr::Term(expr) => ProofExpr::Term(expr),
                            other => ProofExpr::App(Box::new(other), vec![], span),
                        }
                    }
                    None => {
                        self.pos = start + 1;
                        let expr = self.parse_expr()?;
                        self.expect(&Tok::RParen)?;
                        ProofExpr::Term(expr)
                    }
                }
            }
            other => {
                return err(
                    token.span,
                    format!("expected a proof or a term, found {other}"),
                )
            }
        };
        // Postfix `.left` / `.right` after a parenthesized expression.
        while self.at(&Tok::Dot) {
            let Some(Token {
                tok: Tok::Ident(field),
                span: field_span,
            }) = self.peek_at(1)
            else {
                break;
            };
            let projection = match field.as_str() {
                "left" => Projection::Left,
                "right" => Projection::Right,
                _ => break,
            };
            self.pos += 2;
            let span = atom.span().to(*field_span);
            atom = ProofExpr::Proj(Box::new(atom), projection, span);
        }
        // Flatten `App(inner, [])` wrappers introduced for parentheses.
        Ok(match atom {
            ProofExpr::App(inner, args, _) if args.is_empty() => *inner,
            other => other,
        })
    }

    fn parse_inst_arg(&mut self) -> Result<InstArg> {
        let param = self.ident("a parameter name")?;
        self.expect(&Tok::Define)?;
        let start = self.pos;
        let mut depth = 0usize;
        let mut end = start;
        while let Some(token) = self.tokens.get(end) {
            match token.tok {
                Tok::LParen | Tok::LBrace | Tok::LBracket => depth += 1,
                Tok::RParen | Tok::RBrace | Tok::RBracket => {
                    if depth == 0 {
                        break;
                    }
                    depth -= 1;
                }
                Tok::Semi if depth == 0 => break,
                _ => {}
            }
            end += 1;
        }
        let tokens = &self.tokens[start..end];
        if tokens.is_empty() {
            return err(
                self.end_span(),
                format!("expected a value for `{}`", param.name),
            );
        }
        let span = tokens[0].span.to(tokens[tokens.len() - 1].span);
        let mut type_parser = Parser::new(tokens, span);
        let ty = type_parser.parse_type().ok().filter(|_| type_parser.done());
        let mut expr_parser = Parser::new(tokens, span);
        let expr = match expr_parser.parse_expr() {
            Ok(expr) if expr_parser.done() => Ok(expr),
            Ok(_) => err(
                expr_parser.peek().unwrap().span,
                "unexpected token in instantiation value",
            ),
            Err(e) => Err(e),
        };
        let expr = match (expr, &ty) {
            (Ok(expr), _) => Some(expr),
            (Err(_), Some(_)) => None,
            (Err(e), None) => return Err(e),
        };
        self.pos = end;
        Ok(InstArg {
            span: param.span.to(span),
            param,
            expr,
            ty,
        })
    }
}

fn is_type_keyword_stop(name: &str) -> bool {
    matches!(
        name,
        "in" | "subset" | "with" | "at" | "by" | "as" | "generalizing"
    )
}

/// Splits `h.left.right` into projections around the name `h`.
fn split_projections(name: &str, span: Span) -> ProofExpr {
    let mut parts: Vec<&str> = name.split('.').collect();
    let mut projections = Vec::new();
    while parts.len() > 1 {
        match parts[parts.len() - 1] {
            "left" => projections.push(Projection::Left),
            "right" => projections.push(Projection::Right),
            _ => break,
        }
        parts.pop();
    }
    let base = parts.join(".");
    let mut expr = ProofExpr::Name(Ident::new(&base, span));
    for projection in projections.into_iter().rev() {
        expr = ProofExpr::Proj(Box::new(expr), projection, span);
    }
    expr
}
