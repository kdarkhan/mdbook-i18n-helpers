// Copyright 2023 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Helpers for translating `mdbook` projects.
//!
//! The functions here are used to implement a robust
//! internationalization (i18n) workflow for `mdbook`. This allows you
//! to translate your books into other languages while also making it
//! easy to keep the translations up to date as you edit the original
//! source text.
//!
//! See <https://github.com/google/mdbook-i18n-helpers> for details on
//! how to use the supplied `mdbook` plugins.

use polib::catalog::Catalog;
use pulldown_cmark::{CodeBlockKind, Event, LinkType, Tag};
use pulldown_cmark_to_cmark::{
    calculate_code_block_token_count, cmark_resume_with_options, Options, State,
};
use std::sync::OnceLock;
use syntect::easy::ScopeRangeIterator;
use syntect::parsing::{ParseState, Scope, ScopeStack, SyntaxSet};

pub mod directives;
pub mod gettext;
pub mod normalize;
pub mod xgettext;

/// Re-wrap the sources field of a message.
///
/// This function tries to wrap the `file:lineno` pairs so they look
/// the same as what you get from `msgcat` or `msgmerge`.
pub fn wrap_sources(sources: &str) -> String {
    let options = textwrap::Options::new(76)
        .break_words(false)
        .word_splitter(textwrap::WordSplitter::NoHyphenation);
    textwrap::refill(sources, options)
}

/// Like `mdbook::utils::new_cmark_parser`, but also passes a
/// `BrokenLinkCallback`.
pub fn new_cmark_parser<'input, 'callback>(
    text: &'input str,
    broken_link_callback: pulldown_cmark::BrokenLinkCallback<'input, 'callback>,
) -> pulldown_cmark::Parser<'input, 'callback> {
    let mut options = pulldown_cmark::Options::empty();
    options.insert(pulldown_cmark::Options::ENABLE_TABLES);
    options.insert(pulldown_cmark::Options::ENABLE_FOOTNOTES);
    options.insert(pulldown_cmark::Options::ENABLE_STRIKETHROUGH);
    options.insert(pulldown_cmark::Options::ENABLE_TASKLISTS);
    options.insert(pulldown_cmark::Options::ENABLE_HEADING_ATTRIBUTES);
    pulldown_cmark::Parser::new_with_broken_link_callback(text, options, broken_link_callback)
}

/// Extract Markdown events from `text`.
///
/// The `state` can be used to give the parsing context. In
/// particular, if a code block has started, the text should be parsed
/// without interpreting special Markdown characters.
///
/// The events are labeled with the line number where they start in
/// the document.
///
/// # Examples
///
/// ```
/// use mdbook_i18n_helpers::extract_events;
/// use pulldown_cmark::{Event, Tag};
///
/// assert_eq!(
///     extract_events("Hello,\nworld!", None),
///     vec![
///         (1, Event::Start(Tag::Paragraph)),
///         (1, Event::Text("Hello,".into())),
///         (1, Event::Text(" ".into())),
///         (2, Event::Text("world!".into())),
///         (1, Event::End(Tag::Paragraph)),
///     ]
/// );
/// ```
pub fn extract_events<'a>(text: &'a str, state: Option<State<'static>>) -> Vec<(usize, Event<'a>)> {
    // Expand a `[foo]` style link into `[foo][foo]`.
    fn expand_shortcut_link(tag: Tag) -> Tag {
        match tag {
            Tag::Link(LinkType::Shortcut, reference, title) => {
                Tag::Link(LinkType::Reference, reference, title)
            }
            Tag::Image(LinkType::Shortcut, reference, title) => {
                Tag::Image(LinkType::Reference, reference, title)
            }
            _ => tag,
        }
    }

    // Offsets of each newline in the input, used to calculate line
    // numbers from byte offsets.
    let offsets = text
        .match_indices('\n')
        .map(|(offset, _)| offset)
        .collect::<Vec<_>>();

    match state {
        // If we're in a code block, we disable the normal parsing and
        // return lines of text. This matches the behavior of the
        // parser in this case.
        Some(state) if state.is_in_code_block => text
            .split_inclusive('\n')
            .enumerate()
            .map(|(idx, line)| (idx + 1, Event::Text(line.into())))
            .collect(),
        // Otherwise, we parse the text line normally.
        _ => new_cmark_parser(text, None)
            .into_offset_iter()
            .map(|(event, range)| {
                let lineno = offsets.partition_point(|&o| o < range.start) + 1;
                let event = match event {
                    Event::SoftBreak => Event::Text(" ".into()),
                    // Shortcut links like "[foo]" end up as "[foo]"
                    // in output. By changing them to a reference
                    // link, the link is expanded on the fly and the
                    // output becomes self-contained.
                    Event::Start(tag @ (Tag::Link(..) | Tag::Image(..))) => {
                        Event::Start(expand_shortcut_link(tag))
                    }
                    Event::End(tag @ (Tag::Link(..) | Tag::Image(..))) => {
                        Event::End(expand_shortcut_link(tag))
                    }
                    _ => event,
                };
                (lineno, event)
            })
            .collect(),
    }
}

/// Markdown events grouped by type.
#[derive(Debug, Clone, PartialEq)]
pub enum Group<'a> {
    /// Markdown events which should be translated.
    ///
    /// This includes `[Text("foo")]` as well as sequences with text
    /// such as `[Start(Emphasis), Text("foo") End(Emphasis)]`.
    Translate(Vec<(usize, Event<'a>)>),

    /// Markdown events which should be skipped when translating.
    ///
    /// This includes structural events such as `Start(Heading(H1,
    /// None, vec![]))`.
    Skip(Vec<(usize, Event<'a>)>),
}

/// Group Markdown events into translatable and skipped events.
///
/// This function will partition the input events into groups of
/// events which should be translated or skipped. Concatenating the
/// events in each group will give you back the original events.
///
/// # Examples
///
/// ```
/// use mdbook_i18n_helpers::{extract_events, group_events, Group};
/// use pulldown_cmark::{Event, Tag};
///
/// let events = extract_events("- A list item.", None);
/// assert_eq!(
///     events,
///     vec![
///         (1, Event::Start(Tag::List(None))),
///         (1, Event::Start(Tag::Item)),
///         (1, Event::Text("A list item.".into())),
///         (1, Event::End(Tag::Item)),
///         (1, Event::End(Tag::List(None))),
///     ],
/// );
///
/// let groups = group_events(&events);
/// assert_eq!(
///     groups,
///     vec![
///         Group::Skip(vec![
///             (1, Event::Start(Tag::List(None))),
///             (1, Event::Start(Tag::Item)),
///         ]),
///         Group::Translate(vec![
///             (1, Event::Text("A list item.".into())),
///         ]),
///         Group::Skip(vec![
///             (1, Event::End(Tag::Item)),
///             (1, Event::End(Tag::List(None))),
///         ]),
///     ]
/// );
/// ```
pub fn group_events<'a>(events: &'a [(usize, Event<'a>)]) -> Vec<Group<'a>> {
    #[derive(Debug)]
    struct GroupingContext {
        skip_next_group: bool,
        // TODO: this struct is planned to expand with translator
        // comments and message contexts.
    }
    impl GroupingContext {
        fn clear_skip_next_group(self) -> Self {
            Self {
                skip_next_group: false,
            }
        }
    }

    #[derive(Debug)]
    enum State {
        Translate(usize),
        Skip(usize),
    }

    impl State {
        /// Creates groups based on the capturing state and context.
        fn into_groups<'a>(
            self,
            idx: usize,
            events: &'a [(usize, Event<'a>)],
            ctx: GroupingContext,
        ) -> (Vec<Group<'a>>, GroupingContext) {
            match self {
                State::Translate(start) => {
                    if ctx.skip_next_group {
                        (
                            vec![Group::Skip(events[start..idx].into())],
                            ctx.clear_skip_next_group(),
                        )
                    } else if is_codeblock_group(&events[start..idx]) {
                        (parse_codeblock(&events[start..idx]), ctx)
                    } else {
                        (vec![Group::Translate(events[start..idx].into())], ctx)
                    }
                }
                State::Skip(start) => (vec![Group::Skip(events[start..idx].into())], ctx),
            }
        }
    }

    let mut groups = Vec::new();
    let mut state = State::Skip(0);
    let mut ctx = GroupingContext {
        skip_next_group: false,
    };

    for (idx, (_, event)) in events.iter().enumerate() {
        match event {
            // These block-level events force new groups. We do this
            // because we want to include these events in the group to
            // make the group self-contained.
            Event::Start(Tag::Paragraph | Tag::CodeBlock(..)) => {
                // A translatable group starts here.
                let mut next_groups;
                (next_groups, ctx) = state.into_groups(idx, events, ctx);
                groups.append(&mut next_groups);

                state = State::Translate(idx);
            }
            Event::End(Tag::Paragraph | Tag::CodeBlock(..)) => {
                // A translatable group ends after `idx`.
                let idx = idx + 1;
                let mut next_groups;
                (next_groups, ctx) = state.into_groups(idx, events, ctx);
                groups.append(&mut next_groups);

                state = State::Skip(idx);
            }

            // Inline events start or continue a translating group.
            Event::Start(
                Tag::Emphasis | Tag::Strong | Tag::Strikethrough | Tag::Link(..) | Tag::Image(..),
            )
            | Event::End(
                Tag::Emphasis | Tag::Strong | Tag::Strikethrough | Tag::Link(..) | Tag::Image(..),
            )
            | Event::Text(_)
            | Event::Code(_)
            | Event::FootnoteReference(_)
            | Event::SoftBreak
            | Event::HardBreak => {
                // If we're currently skipping, then a new
                // translatable group starts here.
                if let State::Skip(_) = state {
                    let mut next_groups;
                    (next_groups, ctx) = state.into_groups(idx, events, ctx);
                    groups.append(&mut next_groups);

                    state = State::Translate(idx);
                }
            }

            Event::Html(s) => {
                match directives::find(s) {
                    Some(directives::Directive::Skip) => {
                        // If in the middle of translation, finish it.
                        if let State::Translate(_) = state {
                            let mut next_groups;
                            (next_groups, ctx) = state.into_groups(idx, events, ctx);
                            groups.append(&mut next_groups);

                            // Restart translation: subtle but should be
                            // needed to handle the skipping of the rest of
                            // the inlined content.
                            state = State::Translate(idx);
                        }

                        ctx.skip_next_group = true;
                    }
                    // Otherwise, treat as a skipping group.
                    _ => {
                        if let State::Translate(_) = state {
                            let mut next_groups;
                            (next_groups, ctx) = state.into_groups(idx, events, ctx);
                            groups.append(&mut next_groups);

                            state = State::Skip(idx);
                        }
                    }
                }
            }

            // All other block-level events start or continue a
            // skipping group.
            _ => {
                if let State::Translate(_) = state {
                    let mut next_groups;
                    (next_groups, ctx) = state.into_groups(idx, events, ctx);
                    groups.append(&mut next_groups);

                    state = State::Skip(idx);
                }
            }
        }
    }

    match state {
        State::Translate(start) => groups.push(Group::Translate(events[start..].into())),
        State::Skip(start) => groups.push(Group::Skip(events[start..].into())),
    }

    groups
}

/// Returns true if the events appear to be a codeblock.
fn is_codeblock_group(events: &[(usize, Event)]) -> bool {
    matches!(
        events,
        [
            (_, Event::Start(Tag::CodeBlock(_))),
            ..,
            (_, Event::End(Tag::CodeBlock(_)))
        ]
    )
}

/// Returns true if the scope should be translated.
fn is_translate_scope(x: Scope) -> bool {
    static SCOPE_STRING: OnceLock<Scope> = OnceLock::new();
    static SCOPE_COMMENT: OnceLock<Scope> = OnceLock::new();

    let scope_string = SCOPE_STRING.get_or_init(|| Scope::new("string").unwrap());
    let scope_comment = SCOPE_COMMENT.get_or_init(|| Scope::new("comment").unwrap());
    scope_string.is_prefix_of(x) || scope_comment.is_prefix_of(x)
}

/// Creates groups by checking codeblock with heuristic way.
fn heuristic_codeblock<'a>(events: &'a [(usize, Event)]) -> Vec<Group<'a>> {
    let is_translate = match events {
        [(_, Event::Start(Tag::CodeBlock(_))), .., (_, Event::End(Tag::CodeBlock(_)))] => {
            let (codeblock_text, _) = reconstruct_markdown(events, None);
            // Heuristic to check whether the codeblock nether has a
            // literal string nor a line comment.  We may actually
            // want to use a lexer here to make this more robust.
            codeblock_text.contains('"') || codeblock_text.contains("//")
        }
        _ => true,
    };

    if is_translate {
        vec![Group::Translate(events.into())]
    } else {
        vec![Group::Skip(events.into())]
    }
}

/// Creates groups by parsing codeblock.
fn parse_codeblock<'a>(events: &'a [(usize, Event)]) -> Vec<Group<'a>> {
    // Language detection from language identifier of codeblock.
    static SYNTAX_SET: OnceLock<SyntaxSet> = OnceLock::new();
    let ss = SYNTAX_SET.get_or_init(SyntaxSet::load_defaults_newlines);

    let syntax = if let (_, Event::Start(Tag::CodeBlock(CodeBlockKind::Fenced(x)))) = &events[0] {
        ss.find_syntax_by_token(x.split(',').next().unwrap())
    } else {
        None
    };

    let Some(syntax) = syntax else {
        // If there is no language specifier, falling back to heuristic way.
        return heuristic_codeblock(events);
    };

    let mut ps = ParseState::new(syntax);
    let mut ret = vec![];

    for (idx, event) in events.iter().enumerate() {
        match event {
            (text_line, Event::Text(text)) => {
                let mut stack = ScopeStack::new();
                let mut stack_failure = false;

                let Ok(ops) = ps.parse_line(text, ss) else {
                    // If parse is failed, the text event should be translated.
                    ret.push(Group::Translate(events[idx..idx + 1].into()));
                    continue;
                };

                let mut translate_events = vec![];
                let mut groups = vec![];

                for (range, op) in ScopeRangeIterator::new(&ops, text) {
                    if stack.apply(op).is_err() {
                        stack_failure = true;
                        break;
                    }

                    if range.is_empty() {
                        continue;
                    }

                    // Calculate line number of the range
                    let range_line = if range.start == 0 {
                        *text_line
                    } else {
                        text_line + text[0..range.start].lines().count() - 1
                    };

                    let text = &text[range];

                    // Whitespaces between translate texts should be added to translate
                    // group.
                    // So all whitespaces are added to the translate events buffer temporary,
                    // and the trailing whitespaces will be remvoed finally.
                    let is_whitespace = text.trim_matches(&[' ', '\t'] as &[_]).is_empty();

                    let is_translate = stack.scopes.iter().any(|x| is_translate_scope(*x));

                    if is_translate || (is_whitespace && !translate_events.is_empty()) {
                        translate_events.push((range_line, Event::Text(text.into())));
                    } else {
                        let whitespace_events = extract_trailing_whitespaces(&mut translate_events);
                        groups.push(Group::Translate(std::mem::take(&mut translate_events)));
                        groups.push(Group::Skip(whitespace_events));
                        groups.push(Group::Skip(vec![(range_line, Event::Text(text.into()))]));
                    }
                }

                let whitespace_events = extract_trailing_whitespaces(&mut translate_events);
                groups.push(Group::Translate(std::mem::take(&mut translate_events)));
                groups.push(Group::Skip(whitespace_events));

                if stack_failure {
                    // If stack operation is failed, the text event should be translated.
                    ret.push(Group::Translate(events[idx..idx + 1].into()));
                } else {
                    ret.append(&mut groups);
                }
            }
            _ => {
                ret.push(Group::Skip(events[idx..idx + 1].into()));
            }
        }
    }
    ret
}

/// Extract trailing events which have whitespace only.
fn extract_trailing_whitespaces<'a>(buf: &mut Vec<(usize, Event<'a>)>) -> Vec<(usize, Event<'a>)> {
    let mut ret = vec![];

    while let Some(last) = buf.last() {
        match &last.1 {
            Event::Text(text) if text.as_ref().trim_matches(&[' ', '\t'] as &[_]).is_empty() => {
                let last = buf.pop().unwrap();
                ret.push(last);
            }
            _ => break,
        }
    }
    ret.reverse();
    ret
}

/// Render a slice of Markdown events back to Markdown.
///
/// # Examples
///
/// ```
/// use mdbook_i18n_helpers::{extract_events, reconstruct_markdown};
/// use pulldown_cmark::{Event, Tag};
///
/// let group = extract_events("Hello *world!*", None);
/// let (reconstructed, _) = reconstruct_markdown(&group, None);
/// assert_eq!(reconstructed, "Hello _world!_");
/// ```
///
/// Notice how this will normalize the Markdown to use `_` for
/// emphasis and `**` for strong emphasis. The style is chosen to
/// match the [Google developer documentation style
/// guide](https://developers.google.com/style/text-formatting).
pub fn reconstruct_markdown(
    group: &[(usize, Event)],
    state: Option<State<'static>>,
) -> (String, State<'static>) {
    let events = group.iter().map(|(_, event)| event);
    let code_block_token_count = calculate_code_block_token_count(events.clone()).unwrap_or(3);
    let mut markdown = String::new();
    let options = Options {
        code_block_token_count,
        list_token: '-',
        emphasis_token: '_',
        strong_token: "**",
        ..Options::default()
    };
    // Advance the true state, but throw away the rendered Markdown
    // since it can contain unwanted padding.
    let new_state = cmark_resume_with_options(
        events.clone(),
        String::new(),
        state.clone(),
        options.clone(),
    )
    .unwrap();

    // Block quotes and lists add padding to the state, which is
    // reflected in the rendered Markdown. We want to capture the
    // Markdown without the padding to remove the effect of these
    // structural elements. Similarly, we don't want extra newlines at
    // the start.
    let simplified_state = state.map(|state| State {
        newlines_before_start: 0,
        padding: Vec::new(),
        ..state
    });
    cmark_resume_with_options(events, &mut markdown, simplified_state, options).unwrap();
    // Even with `newlines_before_start` set to zero, we get a leading
    // `\n` for code blocks (since they must start on a new line). We
    // can safely trim this here since we know that we always
    // reconstruct Markdown for a self-contained group of events.
    (String::from(markdown.trim_start_matches('\n')), new_state)
}

/// Extract translatable strings from `document`.
///
/// # Examples
///
/// Structural markup like headings and lists are removed from the
/// messages:
///
/// ```
/// use mdbook_i18n_helpers::extract_messages;
///
/// assert_eq!(
///     extract_messages("# A heading"),
///     vec![(1, "A heading".into())],
/// );
/// assert_eq!(
///     extract_messages(
///         "1. First item\n\
///          2. Second item\n"
///     ),
///     vec![
///         (1, "First item".into()),
///         (2, "Second item".into()),
///     ],
/// );
/// ```
///
/// Indentation due to structural elements like block quotes and lists
/// is ignored:
///
/// ```
/// use mdbook_i18n_helpers::extract_messages;
///
/// let messages = extract_messages(
///     "> *   Hello, this is a\n\
///      >     list in a quote.\n\
///      >\n\
///      >     This is the second\n\
///      >     paragraph.\n"
/// );
/// assert_eq!(
///     messages,
///     vec![
///         (1, "Hello, this is a list in a quote.".into()),
///         (4, "This is the second paragraph.".into()),
///     ],
/// );
/// ```
pub fn extract_messages(document: &str) -> Vec<(usize, String)> {
    let events = extract_events(document, None);
    let mut messages = Vec::new();
    let mut state = None;

    for group in group_events(&events) {
        match group {
            Group::Translate(events) => {
                if let Some((lineno, _)) = events.first() {
                    let (text, new_state) = reconstruct_markdown(&events, state);
                    // Skip empty messages since they are special:
                    // they contains the PO file metadata.
                    if !text.trim().is_empty() {
                        messages.push((*lineno, text));
                    }
                    state = Some(new_state);
                }
            }
            Group::Skip(events) => {
                let (_, new_state) = reconstruct_markdown(&events, state);
                state = Some(new_state);
            }
        }
    }

    messages
}

/// Trim `new_events` if they're wrapped in an unwanted paragraph.
///
/// If `new_events` is wrapped in a paragraph and `old_events` isn't,
/// then the paragraph is removed. This is useful when a text event
/// has been wrapped in a paragraph:
///
/// ```
/// use pulldown_cmark::{Event, Tag};
/// use mdbook_i18n_helpers::{extract_events, reconstruct_markdown, trim_paragraph};
///
/// let old_events = vec![(1, Event::Text("A line of text".into()))];
/// let (markdown, _) = reconstruct_markdown(&old_events, None);
/// let new_events = extract_events(&markdown, None);
/// // The stand-alone text has been wrapped in an extra paragraph:
/// assert_eq!(
///     new_events,
///     &[
///         (1, Event::Start(Tag::Paragraph)),
///         (1, Event::Text("A line of text".into())),
///         (1, Event::End(Tag::Paragraph)),
///     ],
/// );
///
/// assert_eq!(
///     trim_paragraph(&new_events, &old_events),
///     &[(1, Event::Text("A line of text".into()))],
/// );
/// ```
pub fn trim_paragraph<'a, 'event>(
    new_events: &'a [(usize, Event<'event>)],
    old_events: &'a [(usize, Event<'event>)],
) -> &'a [(usize, Event<'event>)] {
    use pulldown_cmark::Event::{End, Start};
    use pulldown_cmark::Tag::Paragraph;
    match new_events {
        [(_, Start(Paragraph)), inner @ .., (_, End(Paragraph))] => match old_events {
            [(_, Start(Paragraph)), .., (_, End(Paragraph))] => new_events,
            [..] => inner,
        },
        [..] => new_events,
    }
}

/// Translate `events` using `catalog`.
pub fn translate_events<'a>(
    events: &'a [(usize, Event<'a>)],
    catalog: &'a Catalog,
) -> Vec<(usize, Event<'a>)> {
    let mut translated_events = Vec::new();
    let mut state = None;

    for group in group_events(events) {
        match group {
            Group::Translate(events) => {
                // Reconstruct the message.
                let (msgid, new_state) = reconstruct_markdown(&events, state.clone());
                let translated = catalog
                    .find_message(None, &msgid, None)
                    .filter(|msg| !msg.flags().is_fuzzy() && msg.is_translated())
                    .and_then(|msg| msg.msgstr().ok());
                match translated {
                    Some(msgstr) => {
                        // Generate new events for `msgstr`, taking
                        // care to trim away unwanted paragraphs.
                        translated_events.extend_from_slice(trim_paragraph(
                            &extract_events(msgstr, state),
                            &events,
                        ));
                    }
                    None => translated_events.extend_from_slice(&events),
                }
                // Advance the state.
                state = Some(new_state);
            }
            Group::Skip(events) => {
                // Copy the events unchanged to the output.
                translated_events.extend_from_slice(&events);
                // Advance the state.
                let (_, new_state) = reconstruct_markdown(&events, state);
                state = Some(new_state);
            }
        }
    }

    translated_events
}
