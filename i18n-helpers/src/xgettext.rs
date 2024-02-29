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

//! This file contains main logic used by the binary `mdbook-xgettext`.

use std::collections::HashMap;
use std::{io, path};

use super::{extract_events, extract_messages, reconstruct_markdown, wrap_sources};
use anyhow::{anyhow, Context};
use mdbook::renderer::RenderContext;
use mdbook::{book, BookItem};
use polib::catalog::Catalog;
use polib::message::{Message, MessageMutView, MessageView};
use polib::metadata::CatalogMetadata;
use pulldown_cmark::{Event, Tag};

/// Strip an optional link from a Markdown string.
fn strip_link(text: &str) -> String {
    let events = extract_events(text, None)
        .into_iter()
        .filter_map(|(_, event)| match event {
            Event::Start(Tag::Link(..)) => None,
            Event::End(Tag::Link(..)) => None,
            _ => Some((0, event)),
        })
        .collect::<Vec<_>>();
    let (without_link, _) = reconstruct_markdown(&events, None);
    without_link
}

fn add_message(catalog: &mut Catalog, msgid: &str, source: &str, comment: &str) {
    let sources = match catalog.find_message(None, msgid, None) {
        Some(msg) => format!("{}\n{}", msg.source(), source),
        None => String::from(source),
    };
    let message = Message::build_singular()
        .with_source(sources)
        .with_msgid(String::from(msgid))
        .with_comments(String::from(comment))
        .done();
    catalog.append_or_update(message);
}

/// Build a source line for a catalog message.
///
/// Use `granularity` to round `lineno`:
///
/// - Set `granularity` to `1` if you want no rounding.
/// - Set `granularity` to `0` if you want to line number at all.
/// - Set `granularity` to `n` if you want rounding down to the
///   nearest multiple of `n`. As an example, if you set it to `10`,
///   then you will get sources like `foo.md:1`, `foo.md:10`,
///   `foo.md:20`, etc.
///
/// This can help reduce number of updates to your PO files.
fn build_source<P: AsRef<path::Path>>(path: P, lineno: usize, granularity: usize) -> String {
    let path = path.as_ref();
    match granularity {
        0 => format!("{}", path.display()),
        1 => format!("{}:{}", path.display(), lineno),
        _ => format!(
            "{}:{}",
            path.display(),
            std::cmp::max(1, lineno - (lineno % granularity))
        ),
    }
}

fn dedup_sources(catalog: &mut Catalog) {
    for mut message in catalog.messages_mut() {
        let mut lines: Vec<&str> = message.source().lines().collect();
        lines.dedup();

        let wrapped_source = wrap_sources(&lines.join("\n"));
        *message.source_mut() = wrapped_source;
    }
}

/// Build CatalogMetadata from RenderContext
fn generate_catalog_metadata(ctx: &RenderContext) -> CatalogMetadata {
    let mut metadata = CatalogMetadata::new();
    if let Some(title) = &ctx.config.book.title {
        metadata.project_id_version = String::from(title);
    }
    if let Some(lang) = &ctx.config.book.language {
        metadata.language = String::from(lang);
    }
    let now = chrono::Local::now();
    metadata.pot_creation_date = now.to_rfc3339_opts(chrono::SecondsFormat::Secs, true);
    metadata.mime_version = String::from("1.0");
    metadata.content_type = String::from("text/plain; charset=UTF-8");
    metadata.content_transfer_encoding = String::from("8bit");
    metadata
}

/// Build catalog from RenderContext
///
/// The `summary_reader` is a closure which should return the
/// `SUMMARY.md` found at the given path.
pub fn create_catalogs<F>(
    ctx: &RenderContext,
    summary_reader: F,
) -> anyhow::Result<HashMap<path::PathBuf, Catalog>>
where
    F: Fn(path::PathBuf) -> io::Result<String>,
{
    let metadata = generate_catalog_metadata(ctx);
    let mut catalog = Catalog::new(metadata);

    // The line number granularity: we default to 1, but it can be
    // overridden as needed.
    let granularity = match ctx
        .config
        .get_renderer("xgettext")
        .and_then(|cfg| cfg.get("granularity"))
    {
        None => 1,
        Some(value) => value
            .as_integer()
            .and_then(|i| (i >= 0).then_some(i as usize))
            .ok_or_else(|| {
                anyhow!("Expected an unsigned integer for output.xgettext.granularity")
            })?,
    };

    // First, add all chapter names and part titles from SUMMARY.md.
    let summary_path = ctx.config.book.src.join("SUMMARY.md");
    let summary = summary_reader(ctx.root.join(&summary_path))
        .with_context(|| anyhow!("Failed to read {}", summary_path.display()))?;
    for (lineno, extracted_msg) in extract_messages(&summary) {
        let msgid = extracted_msg.message;
        let source = build_source(&summary_path, lineno, granularity);
        // The summary is mostly links like "[Foo *Bar*](foo-bar.md)".
        // We strip away the link to get "Foo *Bar*". The formatting
        // is stripped away by mdbook when it sends the book to
        // mdbook-gettext -- we keep the formatting here in case the
        // same text is used for the page title.
        add_message(
            &mut catalog,
            &strip_link(&msgid),
            &source,
            &extracted_msg.comment,
        );
    }

    let mut catalogs = HashMap::new();

    // The depth on which to split the output file. The default is to
    // include all messages into a single POT file (depth == 0).
    // Greater values will split POT files, digging into the
    // sub-chapters within each chapter.
    let depth = match ctx
        .config
        .get_renderer("xgettext")
        .and_then(|cfg| cfg.get("depth"))
    {
        None => 0,
        Some(value) => value
            .as_integer()
            .and_then(|i| (i >= 0).then_some(i as usize))
            .ok_or_else(|| anyhow!("Expected an unsigned integer for output.xgettext.depth"))?,
    };

    // The catalog from the summary data will exist in the single pot
    // file for a depth of 0, will exist in a top-level separate
    // `summary.pot` file for a depth of 1, or exist within in a
    // `summary.pot` file within the default directory for chapters
    // without a corresponding part title.
    let mut current_top_level = "summary".to_owned();
    let mut summary_destination = match depth {
        0 => path::PathBuf::from("messages"),
        1 => path::PathBuf::from("summary"),
        _ => path::PathBuf::from(&current_top_level).join("summary"),
    };
    let _: bool = summary_destination.set_extension("pot");
    catalogs.insert(summary_destination, catalog);

    // Next, we add the chapter contents.
    for item in &ctx.book.sections {
        if let BookItem::PartTitle(title) = item {
            // Iterating through the book in section-order, the
            // PartTitle represents the 'section' that each chapter
            // exists within.
            current_top_level = slug(title);
        } else if let BookItem::Chapter(chapter) = item {
            let path = match &chapter.path {
                Some(path) => ctx.config.book.src.join(path),
                None => continue,
            };
            let directory = match depth {
                0 => path::PathBuf::from("messages"),
                1 => path::PathBuf::from(current_top_level.clone()),
                // The current chapter is already at depth 2, so
                // append the chapter's name for depths greater than
                // 1.
                _ => path::PathBuf::from(current_top_level.clone()).join(slug(&chapter.name)),
            };

            // Add the (destination, catalog) to the map if it doesn't
            // yet exist, so messages can be appended to the catalog.
            let mut destination = directory.clone();
            let _: bool = destination.set_extension("pot");
            let catalog = catalogs
                .entry(destination.clone())
                .or_insert_with(|| Catalog::new(generate_catalog_metadata(ctx)));

            for (lineno, extracted) in extract_messages(&chapter.content) {
                let msgid = extracted.message;
                let source = build_source(&path, lineno, granularity);
                add_message(catalog, &strip_link(&msgid), &source, &extracted.comment);
            }

            // Add the contents for all of the sub-chapters within the
            // current chapter.
            for Chapter {
                content,
                source,
                mut destination,
            } in get_subcontent_for_chapter(chapter, directory, depth, 2)
            {
                let _: bool = destination.set_extension("pot");
                let catalog = catalogs
                    .entry(destination.clone())
                    .or_insert_with(|| Catalog::new(generate_catalog_metadata(ctx)));

                let source = ctx.config.book.src.join(&source);
                for (lineno, extracted) in extract_messages(&content) {
                    let msgid = extracted.message;
                    let source = format!("{}:{}", source.display(), lineno);
                    add_message(catalog, &strip_link(&msgid), &source, &extracted.comment);
                }
            }
        }
    }
    catalogs
        .iter_mut()
        .for_each(|(_key, catalog)| dedup_sources(catalog));
    Ok(catalogs)
}

/// A view into the relevant template information held by
/// `mdbook::book::Chapter` and a location to store the exported polib
/// messages.
struct Chapter {
    /// The chapter's content.
    content: String,
    /// The file where the content is sourced.
    source: path::PathBuf,
    /// The output destination for the polib template.
    destination: path::PathBuf,
}

// A recursive function to crawl a chapter's sub-items and get the
// relevant info to produce a set of po template files.
fn get_subcontent_for_chapter(
    c: &book::Chapter,
    provided_file_path: path::PathBuf,
    provided_depth: usize,
    depth: usize,
) -> Vec<Chapter> {
    if c.sub_items.is_empty() {
        return Vec::new();
    };

    // Iterate through sub-chapters and pull the chapter content,
    // path, and destination to store the template.
    c.sub_items
        .iter()
        .filter_map(|item| {
            let BookItem::Chapter(chapter) = item else {
                return None;
            };
            let (chapter_info, new_path) = match &chapter.path {
                Some(chapter_path) => {
                    // Append the chapter's name to the template's
                    // destination when the depth has not surpassed
                    // the provided value.
                    let destination = if depth < provided_depth {
                        provided_file_path.join(slug(&chapter.name))
                    } else {
                        provided_file_path.clone()
                    };

                    let info = Chapter {
                        content: chapter.content.clone(),
                        source: chapter_path.clone(),
                        destination: destination.clone(),
                    };
                    (Some(info), destination)
                }
                None => (None, provided_file_path.clone()),
            };

            // Recursively call to get sub-chapter contents.
            Some(chapter_info.into_iter().chain(get_subcontent_for_chapter(
                chapter,
                new_path,
                provided_depth,
                depth + 1,
            )))
        })
        .flatten()
        .collect()
}

// Trim a string slice to only contain alphanumeric characters and
// dashes.
fn slug(title: &str) -> String {
    // Specially handle "C++" to format it as "cpp" instead of "c".
    let title = title.to_lowercase().replace("c++", "cpp");
    title
        .split_whitespace()
        .map(|word| {
            word.chars()
                .filter(|&ch| ch == '-' || ch.is_ascii_alphanumeric())
                .collect::<String>()
        })
        .filter(|word| !word.is_empty())
        .collect::<Vec<_>>()
        .join("-")
}
