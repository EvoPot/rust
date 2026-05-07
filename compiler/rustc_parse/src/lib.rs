//! The main parser interface.

// tidy-alphabetical-start
#![cfg_attr(test, feature(iter_order_by))]
#![feature(box_patterns)]
#![feature(debug_closure_helpers)]
#![feature(default_field_values)]
#![feature(iter_intersperse)]
#![recursion_limit = "256"]
// tidy-alphabetical-end

use std::path::{Path, PathBuf};
use std::str::Utf8Error;
use std::sync::Arc;

use rustc_ast as ast;
use rustc_ast::token;
use rustc_ast::tokenstream::TokenStream;
use rustc_ast_pretty::pprust;
use rustc_errors::{Diag, EmissionGuarantee, FatalError, PResult, pluralize};
pub use rustc_lexer::UNICODE_VERSION;
use rustc_session::parse::ParseSess;
use rustc_span::source_map::SourceMap;
use rustc_span::{FileName, SourceFile, Span};

pub const MACRO_ARGUMENTS: Option<&str> = Some("macro arguments");

#[macro_use]
pub mod parser;
use parser::Parser;

use crate::lexer::StripTokens;

pub mod lexer;

mod errors;

// Make sure that the Unicode version of the dependencies is the same.
const _: () = {
    let rustc_lexer = rustc_lexer::UNICODE_VERSION;
    let rustc_span = rustc_span::UNICODE_VERSION;
    let normalization = unicode_normalization::UNICODE_VERSION;
    let width = unicode_width::UNICODE_VERSION;

    if rustc_lexer.0 != rustc_span.0
        || rustc_lexer.1 != rustc_span.1
        || rustc_lexer.2 != rustc_span.2
    {
        panic!(
            "rustc_lexer and rustc_span must use the same Unicode version, \
            `rustc_lexer::UNICODE_VERSION` and `rustc_span::UNICODE_VERSION` are \
            different."
        );
    }

    if rustc_lexer.0 != normalization.0
        || rustc_lexer.1 != normalization.1
        || rustc_lexer.2 != normalization.2
    {
        panic!(
            "rustc_lexer and unicode-normalization must use the same Unicode version, \
            `rustc_lexer::UNICODE_VERSION` and `unicode_normalization::UNICODE_VERSION` are \
            different."
        );
    }

    if rustc_lexer.0 != width.0 || rustc_lexer.1 != width.1 || rustc_lexer.2 != width.2 {
        panic!(
            "rustc_lexer and unicode-width must use the same Unicode version, \
            `rustc_lexer::UNICODE_VERSION` and `unicode_width::UNICODE_VERSION` are \
            different."
        );
    }
};

// Unwrap the result if `Ok`, otherwise emit the diagnostics and abort.
pub fn unwrap_or_emit_fatal<T>(expr: Result<T, Vec<Diag<'_>>>) -> T {
    match expr {
        Ok(expr) => expr,
        Err(errs) => {
            for err in errs {
                err.emit();
            }
            FatalError.raise()
        }
    }
}

/// Creates a new parser from a source string.
///
/// On failure, the errors must be consumed via `unwrap_or_emit_fatal`, `emit`, `cancel`,
/// etc., otherwise a panic will occur when they are dropped.
pub fn new_parser_from_source_str(
    psess: &ParseSess,
    name: FileName,
    source: String,
    strip_tokens: StripTokens,
) -> Result<Parser<'_>, Vec<Diag<'_>>> {
    let source_file = psess.source_map().new_source_file(name, source);
    new_parser_from_source_file(psess, source_file, strip_tokens)
}

/// Creates a new parser from a filename. On failure, the errors must be consumed via
/// `unwrap_or_emit_fatal`, `emit`, `cancel`, etc., otherwise a panic will occur when they are
/// dropped.
///
/// If a span is given, that is used on an error as the source of the problem.
pub fn new_parser_from_file<'a>(
    psess: &'a ParseSess,
    path: &Path,
    strip_tokens: StripTokens,
    sp: Option<Span>,
) -> Result<Parser<'a>, Vec<Diag<'a>>> {
    let sm = psess.source_map();
    let source_file = sm.load_file(path).unwrap_or_else(|e| {
        use std::io::ErrorKind;
        let mut msg = match e.kind() {
            ErrorKind::NotFound => format!("couldn't find file `{}`", path.display()),
            ErrorKind::PermissionDenied => {
                format!("insufficient permissions when opening file {}", path.display())
            }
            ErrorKind::IsADirectory => format!("{} is a directory", path.display()),
            fb => format!("couldn't read `{}`: {}", path.display(), fb),
        };

        if let Some(path_str) = path.as_os_str().to_str()
            && let Some(last_char) = path_str.chars().last()
            && std::path::is_separator(last_char)
            && !path.exists()
        {
            msg = format!("{} is a non existent directory", path.display());
        }

        let mut err = psess.dcx().struct_fatal(msg);
        parse_create_error_apply_suggestions(&mut err, path);
        if let Ok(contents) = std::fs::read(path)
            && let Err(utf8err) = std::str::from_utf8(&contents)
        {
            utf8_error(sm, &path.display().to_string(), sp, &mut err, utf8err, &contents);
        }
        if let Some(sp) = sp {
            err.span(sp);
        }
        err.emit()
    });
    new_parser_from_source_file(psess, source_file, strip_tokens)
}

fn parse_create_error_apply_suggestions<E: EmissionGuarantee>(err: &mut Diag<'_, E>, path: &Path) {
    let with_dot_rs = {
        let mut this = path.to_owned();
        this.set_extension("rs");
        this
    };

    if let Some(path_str) = path.as_os_str().to_str()
        && let Some(last_char) = path_str.chars().last()
        && std::path::is_separator(last_char)
        && with_dot_rs.exists()
        && with_dot_rs.is_file()
    {
        err.help(format!(
            "you might have meant to open `{}`: `rustc {}`",
            with_dot_rs.display(),
            with_dot_rs.display()
        ));
        return;
    }

    let prev_dir = path.ancestors().nth(1).unwrap_or(&Path::new(""));

    if let Ok(current_dir) = std::env::current_dir()
        && let Ok(read_dir) = current_dir.join(prev_dir).read_dir()
        && let Some(file_name) = path.file_name()
        && let Some(file_str) = file_name.to_str()
    {
        let mut best_lev = usize::MAX;
        let mut best_path = String::new();
        'inner: for dir_result in read_dir {
            if let Ok(dir) = dir_result
                && let Some(prev_dir_string) = prev_dir.to_str()
                && let Ok(dir_string) = dir.file_name().into_string()
            {
                let lev = lev(&dir_string, file_str);
                best_lev = std::cmp::min(lev, best_lev);
                if lev == best_lev && dir.path().extension() == Some(std::ffi::OsStr::new("rs")) {
                    let mut suggestion_string = prev_dir_string.to_owned();
                    if !prev_dir_string.is_empty() {
                        suggestion_string.push(std::path::MAIN_SEPARATOR);
                    }
                    suggestion_string.push_str(&dir_string);
                    best_path = suggestion_string;
                }
                if best_lev == 1 {
                    break 'inner;
                }
            }
        }

        if best_lev <= file_str.len() / 2
            && (file_str.len() as i128 - best_path.len() as i128).abs() <= 3
            && best_path.ends_with(".rs")
        {
            err.help(format!(
                "you might have meant to open `{}`: `rustc {}`",
                best_path, best_path
            ));
        }
    }

    /// Levenshtein distance algorithm : https://en.wikipedia.org/wiki/Levenshtein_distance
    fn lev(a: &str, b: &str) -> usize {
        if a.is_empty() || b.is_empty() {
            return std::cmp::max(a.len(), b.len());
        }
        let mut matrix = vec![vec![0; b.len()]; a.len()];
        for i in 1..a.len() {
            matrix[i][0] = i;
        }
        for i in 1..b.len() {
            matrix[0][i] = i;
        }
        for j in 1..b.len() {
            for i in 1..a.len() {
                let cost = if a.as_bytes()[i - 1] == b.as_bytes()[j - 1] { 0 } else { 1 };
                matrix[i][j] =
                    *[matrix[i - 1][j] + 1, matrix[i][j - 1] + 1, matrix[i - 1][j - 1] + cost]
                        .iter()
                        .min()
                        .unwrap_or(&0);
            }
        }
        matrix[a.len() - 1][b.len() - 1]
    }
}

pub fn utf8_error<E: EmissionGuarantee>(
    sm: &SourceMap,
    path: &str,
    sp: Option<Span>,
    err: &mut Diag<'_, E>,
    utf8err: Utf8Error,
    contents: &[u8],
) {
    // The file exists, but it wasn't valid UTF-8.
    let start = utf8err.valid_up_to();
    let note = format!("invalid utf-8 at byte `{start}`");
    let msg = if let Some(len) = utf8err.error_len() {
        format!(
            "byte{s} `{bytes}` {are} not valid utf-8",
            bytes = if len == 1 {
                format!("{:?}", contents[start])
            } else {
                format!("{:?}", &contents[start..start + len])
            },
            s = pluralize!(len),
            are = if len == 1 { "is" } else { "are" },
        )
    } else {
        note.clone()
    };
    let contents = String::from_utf8_lossy(contents).to_string();

    // We only emit this error for files in the current session
    // so the working directory can only be the current working directory
    let filename = FileName::Real(
        sm.path_mapping().to_real_filename(sm.working_dir(), PathBuf::from(path).as_path()),
    );
    let source = sm.new_source_file(filename, contents);

    // Avoid out-of-bounds span from lossy UTF-8 conversion.
    if start as u32 > source.normalized_source_len.0 {
        err.note(note);
        return;
    }

    let span = Span::with_root_ctxt(
        source.normalized_byte_pos(start as u32),
        source.normalized_byte_pos(start as u32),
    );
    if span.is_dummy() {
        err.note(note);
    } else {
        if sp.is_some() {
            err.span_note(span, msg);
        } else {
            err.span(span);
            err.span_label(span, msg);
        }
    }
}

/// Given a session and a `source_file`, return a parser. Returns any buffered errors from lexing
/// the initial token stream.
fn new_parser_from_source_file(
    psess: &ParseSess,
    source_file: Arc<SourceFile>,
    strip_tokens: StripTokens,
) -> Result<Parser<'_>, Vec<Diag<'_>>> {
    let end_pos = source_file.end_position();
    let stream = source_file_to_stream(psess, source_file, None, strip_tokens)?;
    let mut parser = Parser::new(psess, stream, None);
    if parser.token == token::Eof {
        parser.token.span = Span::new(end_pos, end_pos, parser.token.span.ctxt(), None);
    }
    Ok(parser)
}

/// Given a source string, produces a sequence of token trees.
///
/// NOTE: This only strips shebangs, not frontmatter!
pub fn source_str_to_stream(
    psess: &ParseSess,
    name: FileName,
    source: String,
    override_span: Option<Span>,
) -> Result<TokenStream, Vec<Diag<'_>>> {
    let source_file = psess.source_map().new_source_file(name, source);
    // FIXME(frontmatter): Consider stripping frontmatter in a future edition. We can't strip them
    // in the current edition since that would be breaking.
    // See also <https://github.com/rust-lang/rust/issues/145520>.
    // Alternatively, stop stripping shebangs here, too, if T-lang and crater approve.
    source_file_to_stream(psess, source_file, override_span, StripTokens::Shebang)
}

/// Given a source file, produces a sequence of token trees.
///
/// Returns any buffered errors from parsing the token stream.
fn source_file_to_stream<'psess>(
    psess: &'psess ParseSess,
    source_file: Arc<SourceFile>,
    override_span: Option<Span>,
    strip_tokens: StripTokens,
) -> Result<TokenStream, Vec<Diag<'psess>>> {
    let src = source_file.src.as_ref().unwrap_or_else(|| {
        psess.dcx().bug(format!(
            "cannot lex `source_file` without source: {}",
            psess.source_map().filename_for_diagnostics(&source_file.name)
        ));
    });

    lexer::lex_token_trees(psess, src.as_str(), source_file.start_pos, override_span, strip_tokens)
}

/// Runs the given subparser `f` on the tokens of the given `attr`'s item.
pub fn parse_in<'a, T>(
    psess: &'a ParseSess,
    tts: TokenStream,
    name: &'static str,
    mut f: impl FnMut(&mut Parser<'a>) -> PResult<'a, T>,
) -> PResult<'a, T> {
    let mut parser = Parser::new(psess, tts, Some(name));
    let result = f(&mut parser)?;
    if parser.token != token::Eof {
        parser.unexpected()?;
    }
    Ok(result)
}

pub fn fake_token_stream_for_item(psess: &ParseSess, item: &ast::Item) -> TokenStream {
    let source = pprust::item_to_string(item);
    let filename = FileName::macro_expansion_source_code(&source);
    unwrap_or_emit_fatal(source_str_to_stream(psess, filename, source, Some(item.span)))
}

pub fn fake_token_stream_for_foreign_item(
    psess: &ParseSess,
    item: &ast::ForeignItem,
) -> TokenStream {
    let source = pprust::foreign_item_to_string(item);
    let filename = FileName::macro_expansion_source_code(&source);
    unwrap_or_emit_fatal(source_str_to_stream(psess, filename, source, Some(item.span)))
}

pub fn fake_token_stream_for_crate(psess: &ParseSess, krate: &ast::Crate) -> TokenStream {
    let source = pprust::crate_to_string_for_macros(krate);
    let filename = FileName::macro_expansion_source_code(&source);
    unwrap_or_emit_fatal(source_str_to_stream(
        psess,
        filename,
        source,
        Some(krate.spans.inner_span),
    ))
}
