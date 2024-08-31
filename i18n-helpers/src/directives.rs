use regex::Regex;
use std::sync::OnceLock;

#[derive(Debug, PartialEq)]
pub enum Directive {
    Skip,
    Comment(String),
    Ctxt(String),
}

pub fn find(html: &str) -> Option<Directive> {
    static RE: OnceLock<Regex> = OnceLock::new();
    let re = RE.get_or_init(|| {
        let pattern = r"(?x)
              <!-{2,}\s*                  # the opening of the comment
              (?:i18n|mdbook-xgettext)    # the prefix
              \s*:                        # delimit between prefix and command
              (?<command>.*[^-])          # the command part of the prefix
              -{2,}>                      # the closing of the comment
        ";
        Regex::new(pattern).expect("well-formed regex")
    });

    let captures = re.captures(html.trim())?;

    let command = captures["command"].trim();
    match command.split(is_delimiter).next() {
        Some("skip") => Some(Directive::Skip),
        Some("comment") => {
            let start_of_comment_offset = std::cmp::min(
                command.find("comment").unwrap() + "comment".len() + 1,
                command.len(),
            );
            Some(Directive::Comment(
                command[start_of_comment_offset..].trim().into(),
            ))
        }
        Some("ctxt") => {
            let start_of_ctxt_offset = std::cmp::min(
                command.find("ctxt").unwrap() + "ctxt".len() + 1,
                command.len(),
            );
            Some(Directive::Ctxt(
                command[start_of_ctxt_offset..].trim().into(),
            ))
        }
        _ => None,
    }
}

fn is_delimiter(c: char) -> bool {
    c.is_whitespace() || c == ':' || c == '-'
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_comment_skip_directive_simple() {
        assert_eq!(find("<!-- i18n:skip -->"), Some(Directive::Skip));
    }

    #[test]
    fn test_is_comment_skip_directive_tolerates_spaces() {
        assert_eq!(find("<!-- i18n: skip -->"), Some(Directive::Skip));
    }

    #[test]
    fn test_is_comment_skip_directive_tolerates_dashes() {
        assert_eq!(find("<!--- i18n:skip ---->"), Some(Directive::Skip));
    }

    #[test]
    fn test_is_comment_skip_directive_needs_skip() {
        assert!(find("<!-- i18n: foo -->").is_none());
    }

    #[test]
    fn test_is_comment_skip_directive_needs_to_be_a_comment() {
        assert!(find("<div>i18: skip</div>").is_none());
    }

    #[test]
    fn test_different_prefix() {
        assert_eq!(find("<!-- mdbook-xgettext:skip -->"), Some(Directive::Skip));
    }

    #[test]
    fn test_comment() {
        assert_eq!(
            find("<!-- i18n:comment: hello world! -->"),
            Some(Directive::Comment("hello world!".into()))
        );
    }

    #[test]
    fn test_empty_comment_does_nothing() {
        assert_eq!(
            find("<!-- i18n:comment -->"),
            Some(Directive::Comment("".into()))
        );
    }

    #[test]
    fn test_ctxt() {
        assert_eq!(
            find("<!-- i18n:ctxt: hello world! -->"),
            Some(Directive::Ctxt("hello world!".into()))
        );
    }

    #[test]
    fn test_empty_ctxt_does_nothing() {
        assert_eq!(find("<!-- i18n:ctxt -->"), Some(Directive::Ctxt("".into())));
    }
}
