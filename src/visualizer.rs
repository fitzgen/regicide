//! Writing the register allocation visualization HTML.

mod function;
mod index;
pub(crate) mod schema;

use crate::{
    context::ContextInner,
    entity::{Block, EntityRepr, Inst, Region, Val, VisualizedEntity},
    events::{EVENT_SCHEMA, EventIndex, EventsLog},
    input::{Input, InputFunction},
    live_ranges::{LiveBundle, LiveSpan, Use},
    machine::{Reg, RegBank, RegClass, RegGroup, RegUnit},
    spill_slot_allocation::{SpillSlot, SpillSlotGroup},
};
use alloc::string::String;
use function::{FUNCTION_SCHEMA, FunctionInfo, MACHINE_SCHEMA, MachineInfo};
use index::{EventIndices, Histogram, Index};
use schema::SerializeTable;

const VERSION: u32 = 1;

const INDEX_HTML: &str = include_str!("../visualizer/index.html");
const MAIN_CSS: &str = include_str!("../visualizer/css/main.css");
const ENTITIES_JS: &str = include_str!("../visualizer/js/entities.js");
const MODEL_JS: &str = include_str!("../visualizer/js/model.js");
const WORKER_JS: &str = include_str!("../visualizer/js/worker.js");
const STATE_JS: &str = include_str!("../visualizer/js/state.js");
const ACTIONS_JS: &str = include_str!("../visualizer/js/actions.js");
const VIEW_JS: &str = include_str!("../visualizer/js/view.js");
const MAIN_JS: &str = include_str!("../visualizer/js/main.js");

const CSS_MARKER: &str = "/* REGICIDE_CSS */";
const WORKER_MARKER: &str = "/* REGICIDE_WORKER_JS */";
const DATA_MARKER: &str = "/* REGICIDE_DATA_JSON */";
const APP_MARKER: &str = "/* REGICIDE_APP_JS */";

/// The whole visualization, as one JSON object.
#[derive(serde::Serialize)]
#[serde(bound = "")]
#[serde(rename_all = "camelCase")]
struct VizBlob<'a, E>
where
    E: EntityRepr,
{
    /// The format version.
    version: u32,

    /// Entity type name to display prefix, the only place prefixes appear.
    entity_kinds: EntityKinds,

    /// Which field of which struct holds which kind of entity, the only place
    /// types appear.
    schema: Schema,

    /// The register file.
    machine: MachineInfo,

    /// The IR skeleton.
    function: FunctionInfo<E>,

    /// The event log, in the order the allocator recorded it.
    events: &'a EventsLog<E>,

    /// The ways into the event log that are not a position.
    index: &'a EventIndices<E>,

    /// The summaries the histograms tab draws.
    histograms: &'a [Histogram],
}

/// The blob's `schema` table, one half per kind of thing that holds entities.
#[derive(serde::Serialize)]
struct Schema {
    /// What each event kind's fields hold, generated from the same exhaustive
    /// match as `Event::visit_entities`.
    events: SerializeTable,

    /// What the IR skeleton's arrays hold.
    function: SerializeTable,

    /// What the register file's arrays hold.
    machine: SerializeTable,
}

/// `ENTITY_KINDS` as a JSON object.
struct EntityKinds;

impl serde::Serialize for EntityKinds {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        use serde::ser::SerializeMap;
        let mut map = serializer.serialize_map(Some(ENTITY_KINDS.len()))?;
        for (kind, prefix) in ENTITY_KINDS {
            map.serialize_entry(kind, prefix)?;
        }
        map.end()
    }
}

/// Write a self-contained HTML visualization of `context`'s results to `path`.
pub(crate) fn write_html<E, F>(
    context: &ContextInner<E>,
    input: &Input<'_, F>,
    path: &std::path::Path,
) -> std::io::Result<()>
where
    E: EntityRepr,
    F: InputFunction,
{
    std::fs::write(path, page(context, input)?)
}

/// Build the page: serialize the blob, stitch it and the assets into
/// `index.html`.
fn page<E, F>(context: &ContextInner<E>, input: &Input<'_, F>) -> std::io::Result<String>
where
    E: EntityRepr,
    F: InputFunction,
{
    let data = viz_blob_json(context, input)?;

    // Dependency order, and `model.js` in the worker's bundle only: the main
    // thread gets labels from `entities.js` and everything else through worker
    // queries, so that it never holds a second copy of the model.
    //
    // The worker's bundle also loses its `export` keywords, because it is
    // evaluated as a classic script — both as a `Blob` worker and, in the
    // fallback, as a `new Function` body — and a top-level `export` is a
    // syntax error in either. The app's bundle keeps them: it is an inline
    // module.
    let worker = strip_exports(&bundle(&[ENTITIES_JS, MODEL_JS, WORKER_JS]));
    let app = bundle(&[ENTITIES_JS, STATE_JS, ACTIONS_JS, VIEW_JS, MAIN_JS]);

    Ok(INDEX_HTML
        .replace(CSS_MARKER, MAIN_CSS)
        .replace(WORKER_MARKER, &escape_script(&worker))
        .replace(DATA_MARKER, &escape_script(&data))
        .replace(APP_MARKER, &escape_script(&app)))
}

/// Serialize the blob.
fn viz_blob_json<E, F>(context: &ContextInner<E>, input: &Input<'_, F>) -> std::io::Result<String>
where
    E: EntityRepr,
    F: InputFunction,
{
    let index = Index::build(input, context);
    let blob = VizBlob {
        version: VERSION,
        entity_kinds: EntityKinds,
        schema: Schema {
            events: SerializeTable(EVENT_SCHEMA),
            function: SerializeTable(FUNCTION_SCHEMA),
            machine: SerializeTable(MACHINE_SCHEMA),
        },
        machine: MachineInfo::new(input.machine),
        function: FunctionInfo::new(input, context, &index),
        events: &context.events,
        index: &index.indices,
        histograms: &index.histograms,
    };

    // `std::io::Result` is the return type, so a float that should have been
    // clamped has to become an `io::Error` rather than a panic.
    serde_json::to_string(&blob).map_err(std::io::Error::other)
}

/// Concatenate `sources` into one script, dropping their sibling imports.
fn bundle(sources: &[&str]) -> String {
    let mut out = String::new();
    for source in sources {
        out.push_str(&strip_imports(source));
        out.push('\n');
    }
    out
}

/// Drop every line that imports a sibling module, which the concatenation
/// above has already brought into scope.
///
/// XXX: This is a line-oriented hack: it breaks on a multi-line import, on a
/// re-export, and on a template literal whose text starts a line with `import`.
fn strip_imports(src: &str) -> String {
    let mut out = String::with_capacity(src.len());
    for line in src.lines() {
        let trimmed = line.trim_start();
        if trimmed.starts_with("import ") && trimmed.contains("\"./") {
            continue;
        }
        out.push_str(line);
        out.push('\n');
    }
    out
}

/// Drop the `export ` keyword from every declaration that has one, leaving a
/// plain top-level declaration behind.
///
/// XXX: This is also a hack, like `strip_imports`.
fn strip_exports(src: &str) -> String {
    let mut out = String::with_capacity(src.len());
    for line in src.lines() {
        out.push_str(line.strip_prefix("export ").unwrap_or(line));
        out.push('\n');
    }
    out
}

/// Escape the two sequences the HTML parser reacts to inside a `<script>`
/// element, either of which would otherwise end the element early.
///
/// `\/` and `\u0021` are both valid escapes in a JSON string and in a
/// JavaScript one, and neither sequence occurs anywhere else in either
/// language, which a test checks by looking for them in the emitted page.
///
/// `\!` would do the same job to the HTML parser but is *not* a legal JSON
/// escape, so a single `<!--` anywhere in the blob would have made the whole
/// thing unparseable and left the page with nothing to show.
fn escape_script(text: &str) -> String {
    text.replace("</", "<\\/").replace("<!--", "<\\u0021--")
}

const fn kind<T: VisualizedEntity>() -> (&'static str, &'static str) {
    (T::KIND, T::PREFIX)
}

/// The entity types the visualizer names, and nothing else: the macros also
/// declare cursor and storage-index types that nobody will ever search for.
macro_rules! entity_kinds {
    ( $( $ty:ty ),* $(,)? ) => {
        const ENTITY_KINDS: &[(&str, &str)] = &[ $( kind::<$ty>() ),* ];

        #[cfg(test)]
        const ENTITY_KIND_DEBUG_CHECKS: &[fn()] = &[ $( debug_matches_prefix::<$ty> ),* ];
    };
}

entity_kinds! {
    Val<u32>,
    Block<u32>,
    Inst<u32>,
    Region<u32>,
    LiveSpan<u32>,
    LiveBundle<u32>,
    Use<u32>,
    SpillSlot<u32>,
    SpillSlotGroup<u32>,
    Reg<u32>,
    RegUnit,
    RegGroup,
    RegClass,
    RegBank,
    EventIndex,
}

#[cfg(test)]
fn debug_matches_prefix<T: VisualizedEntity>() {
    use std::format;
    let e = T::try_new(3).unwrap();
    assert_eq!(format!("{e:?}"), format!("{}3", T::PREFIX));
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test::TestInput;
    use alloc::collections::BTreeMap;
    use std::{format, println, vec::Vec};

    /// The opening tag of each script the page carries, which is also how a
    /// test finds the body again.
    const WORKER_TAG: &str = "<script id=\"regicide-worker\" type=\"text/plain\">";
    const DATA_TAG: &str = "<script id=\"regicide-data\" type=\"application/json\">";
    const APP_TAG: &str = "<script type=\"module\">";

    /// Every JS asset, named so that a lint failure says which file.
    const JS_SOURCES: &[(&str, &str)] = &[
        ("entities.js", ENTITIES_JS),
        ("model.js", MODEL_JS),
        ("worker.js", WORKER_JS),
        ("state.js", STATE_JS),
        ("actions.js", ACTIONS_JS),
        ("view.js", VIEW_JS),
        ("main.js", MAIN_JS),
    ];

    /// Run the allocator over `test` and hand the results to `f`.
    ///
    /// `run_inner` rather than `run`: the narrow representations would answer
    /// the same questions, and pinning `u32` keeps a fixture from changing
    /// when someone turns `entity-repr-8` off.
    fn allocated<R>(
        test: &TestInput,
        f: impl FnOnce(&ContextInner<u32>, &Input<'_, crate::test::TestFunction>) -> R,
    ) -> R {
        test.with_input(|input| {
            let mut context = ContextInner::<u32>::new();
            crate::run_inner(&mut context, input).expect("the test input allocates");
            f(&context, input)
        })
    }

    /// The stitched page for `test`.
    fn page_for(test: &TestInput) -> String {
        allocated(test, |context, input| {
            page(context, input).expect("the page serializes")
        })
    }

    /// One script's body, still escaped.
    fn script_body<'a>(page: &'a str, open: &str) -> &'a str {
        let start = page.find(open).expect("the script tag") + open.len();
        let rest = &page[start..];
        &rest[..rest.find("</script>").expect("the script's closing tag")]
    }

    /// The JSON blob back out of a page.
    ///
    /// Nothing is undone: [`escape_script`] emits only escapes JSON already
    /// understands, so the escaped text parses as-is. Un-escaping by hand here
    /// instead would hide an escape that JSON does not accept.
    fn data_json(page: &str) -> &str {
        script_body(page, DATA_TAG)
    }

    /// If a prefix ever drifts from the `Debug` impl the rest of the crate
    /// uses, the visualizer's labels start lying.
    #[test]
    fn entity_kinds_match_debug_impls() {
        for check in ENTITY_KIND_DEBUG_CHECKS {
            check();
        }
    }

    #[test]
    fn entity_kinds_are_unique() {
        for (i, (kind, _)) in ENTITY_KINDS.iter().enumerate() {
            assert!(
                !ENTITY_KINDS[..i].iter().any(|(k, _)| k == kind),
                "duplicate entity kind {kind}"
            );
        }
    }

    /// A renamed marker emits a page that quietly does nothing, and every
    /// other test here would still pass.
    #[test]
    fn markers_are_replaced() {
        let page = page_for(&TestInput::with_a_critical_edge());
        for marker in [CSS_MARKER, WORKER_MARKER, DATA_MARKER, APP_MARKER] {
            assert_eq!(
                INDEX_HTML.matches(marker).count(),
                1,
                "`{marker}` should appear exactly once in `index.html`"
            );
            assert_eq!(
                page.matches(marker).count(),
                0,
                "`{marker}` survived into the page"
            );
        }
    }

    /// [`strip_imports`] is line-oriented, so the sources have to hold up
    /// their end: one sibling import per line, and no re-exports. Neither
    /// rule shows up under `node --test`, where the modules are real modules.
    #[test]
    fn js_sources_are_stitchable() {
        for (name, source) in JS_SOURCES {
            for (i, line) in source.lines().enumerate() {
                let at = format!("{name}:{}", i + 1);
                let trimmed = line.trim();
                if trimmed.contains("from \"./") {
                    assert!(
                        trimmed.starts_with("import "),
                        "{at}: a sibling import must start its line"
                    );
                    assert!(
                        trimmed.ends_with(';'),
                        "{at}: a sibling import must end on its own line"
                    );
                }
                assert!(
                    !(trimmed.starts_with("export ") && trimmed.contains("from \"")),
                    "{at}: re-exports are not stitchable"
                );
            }
        }
    }

    /// The name a top-level declaration binds, if the line declares one.
    ///
    /// Column 0 is the whole test: a declaration indented by even one space is
    /// inside something and cannot collide with anything.
    fn top_level_binding(line: &str) -> Option<&str> {
        let rest = line.strip_prefix("export ").unwrap_or(line);
        let rest = rest.strip_prefix("async ").unwrap_or(rest);
        let rest = ["function ", "class ", "const ", "let ", "var "]
            .iter()
            .find_map(|keyword| rest.strip_prefix(keyword))?;
        // `const {a, b} = ...` would need real parsing; the sources do not use
        // it, and a destructuring line simply binds nothing here.
        let name = rest
            .split(|c: char| !(c.is_ascii_alphanumeric() || c == '_' || c == '$'))
            .next()?;
        (!name.is_empty()).then_some(name)
    }

    /// Two modules may each have a top-level `dispatch`; one script may not.
    ///
    /// This is the failure mode the stitching creates and no other check sees:
    /// `node --test` runs the files as separate modules, where the collision
    /// does not exist, and the page only reports it as a syntax error that
    /// blanks the whole app.
    #[test]
    fn bundled_sources_do_not_shadow_each_other() {
        let bundles: &[(&str, &[(&str, &str)])] = &[
            (
                "worker",
                &[
                    ("entities.js", ENTITIES_JS),
                    ("model.js", MODEL_JS),
                    ("worker.js", WORKER_JS),
                ],
            ),
            (
                "app",
                &[
                    ("entities.js", ENTITIES_JS),
                    ("state.js", STATE_JS),
                    ("actions.js", ACTIONS_JS),
                    ("view.js", VIEW_JS),
                    ("main.js", MAIN_JS),
                ],
            ),
        ];

        for (bundle, sources) in bundles {
            let mut seen = BTreeMap::new();
            for (file, source) in *sources {
                for line in source.lines() {
                    let Some(name) = top_level_binding(line) else {
                        continue;
                    };
                    if let Some(first) = seen.insert(name, file) {
                        assert_eq!(
                            first, file,
                            "the {bundle} bundle binds `{name}` in both {first} and {file}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn top_level_binding_reads_declarations_and_nothing_else() {
        assert_eq!(
            top_level_binding("export function installView(root) {"),
            Some("installView")
        );
        assert_eq!(
            top_level_binding("let viewDispatch = () => {};"),
            Some("viewDispatch")
        );
        assert_eq!(top_level_binding("const INDENT = 4;"), Some("INDENT"));
        assert_eq!(top_level_binding("  const inner = 1;"), None);
        assert_eq!(top_level_binding("// const commented = 1;"), None);
        assert_eq!(top_level_binding("  return const;"), None);
    }

    #[test]
    fn strip_imports_only_drops_sibling_imports() {
        let stripped = strip_imports(
            "import { a } from \"./a.js\";\n\
             export function f() {}\n\
             const s = \"import { b } from './b.js'\";\n\
             // import { c } from \"./c.js\"\n",
        );
        assert_eq!(
            stripped,
            "export function f() {}\n\
             const s = \"import { b } from './b.js'\";\n\
             // import { c } from \"./c.js\"\n"
        );
    }

    #[test]
    fn strip_exports_leaves_everything_else() {
        assert_eq!(
            strip_exports("export function f() {}\n  export const g = 1;\n"),
            "function f() {}\n  export const g = 1;\n"
        );
    }

    /// Entities serialize as bare indices, so the array they index into has to
    /// be long enough for all of them. There are no `id` fields to cross-check
    /// against; the length is the invariant that replaces them.
    #[test]
    fn function_arrays_are_indexable() {
        let test = TestInput::with_values_in_two_banks_spilled_and_reloaded();
        allocated(&test, |context, input| {
            let json = viz_blob_json(context, input).expect("the blob serializes");
            let json: serde_json::Value = serde_json::from_str(&json).expect("valid JSON");
            let function = &json["function"];
            // `regions` is indexed by a strongly-connected component's
            // representative block, so it is as long as the block array.
            let expected = [
                ("blocks", input.func.len_blocks()),
                ("insts", input.func.len_insts()),
                ("regions", input.func.len_blocks()),
                ("spans", context.live_ranges.spans().count()),
                ("bundles", context.live_ranges.bundles().count()),
                ("uses", context.live_ranges.len_uses()),
                ("spillSlots", context.spill_slots.len_slots()),
            ];
            for (name, len) in expected {
                let array = function[name].as_array().expect(name);
                assert_eq!(array.len(), len, "function.{name}");
            }
        });
    }

    /// The exhaustiveness check that lets [`ENTITY_KINDS`] be a hand-written
    /// list: a type the schema names but the prefix table does not is a label
    /// the page cannot render.
    #[test]
    fn entity_kinds_cover_the_schema() {
        for table in [EVENT_SCHEMA, FUNCTION_SCHEMA, MACHINE_SCHEMA] {
            schema::visit_table_kinds(table, &mut |kind| {
                assert!(
                    ENTITY_KINDS.iter().any(|(k, _)| *k == kind),
                    "the schema names `{kind}`, which `entityKinds` does not"
                );
            });
        }
    }

    /// The whole path, through an actual file: serialize, stitch, write, read
    /// back, and find the blob again.
    #[test]
    fn round_trip_through_a_file() {
        let test = TestInput::with_a_critical_edge();
        let path = std::env::temp_dir().join("regicide-round-trip.html");
        allocated(&test, |context, input| {
            write_html(context, input, &path).expect("the page writes");
        });

        let page = std::fs::read_to_string(&path).expect("the page reads back");
        std::fs::remove_file(&path).expect("the page is removable");

        let json: serde_json::Value =
            serde_json::from_str(data_json(&page)).expect("the blob parses");
        assert_eq!(json["version"], VERSION);
        assert_eq!(
            json["function"]["blocks"].as_array().expect("blocks").len(),
            test.func.len_blocks()
        );
    }

    /// The escaping has to survive `JSON.parse`, which is the one thing the
    /// page does with the blob. An escape the HTML parser accepts but JSON
    /// rejects loses not one string but the entire visualization.
    #[test]
    fn escapes_are_valid_json() {
        let text = r#"a </script> and a <!-- comment --> walk in"#;
        let escaped = escape_script(&serde_json::to_string(&text).unwrap());
        assert!(!escaped.contains("</"), "`</` survived: {escaped}");
        assert!(!escaped.contains("<!--"), "`<!--` survived: {escaped}");

        let back: String = serde_json::from_str(&escaped).expect("the escaped string parses");
        assert_eq!(back, text);
    }

    /// Either sequence ends the `<script>` element early, which turns the rest
    /// of the page into text.
    #[test]
    fn script_bodies_close_no_tags() {
        let page = page_for(&TestInput::with_spilled_merge_param());
        for tag in [WORKER_TAG, DATA_TAG, APP_TAG] {
            let body = script_body(&page, tag);
            assert!(!body.contains("</"), "`</` inside {tag}");
            assert!(!body.contains("<!--"), "`<!--` inside {tag}");
        }
    }

    /// The blob duplicates a lot -- `function` restates parent links the
    /// index already has, `byEntity` restates the events -- and the per-event
    /// cost is what decides whether this is usable on a large function.
    ///
    /// So the blob is what is measured, not the page around it. Weighing the
    /// whole page instead put the assets on the scale too: they are about
    /// 110 KB and climbing, they do not grow with the function, and a pane
    /// added to `model.js` would trip a tripwire aimed at the event log.
    ///
    /// The ceiling is a tripwire, not a budget. The largest input in the
    /// suite comes to 23 KB, so this leaves room to grow and still catches a
    /// field quietly added to every event. When it trips, the printed sizes
    /// are what to re-observe it against.
    #[test]
    fn the_blob_stays_small() {
        const CEILING: usize = 32 * 1024;

        let inputs: &[(&str, fn() -> TestInput)] = &[
            ("default", TestInput::default),
            (
                "two_uses_of_different_values",
                TestInput::with_two_uses_of_different_values,
            ),
            (
                "values_in_two_banks_spilled_and_reloaded",
                TestInput::with_values_in_two_banks_spilled_and_reloaded,
            ),
            (
                "reuse_of_a_surviving_value",
                TestInput::with_reuse_of_a_surviving_value,
            ),
            (
                "two_reads_and_a_reuse_of_a_surviving_value",
                TestInput::with_two_reads_and_a_reuse_of_a_surviving_value,
            ),
            (
                "a_reuse_of_a_live_in_value",
                TestInput::with_a_reuse_of_a_live_in_value,
            ),
            (
                "two_reuses_at_one_point",
                TestInput::with_two_reuses_at_one_point,
            ),
            (
                "two_reuses_of_a_dying_value",
                TestInput::with_two_reuses_of_a_dying_value,
            ),
            ("a_critical_edge", TestInput::with_a_critical_edge),
            ("spilled_merge_param", TestInput::with_spilled_merge_param),
            (
                "a_self_looping_entry_block",
                TestInput::with_a_self_looping_entry_block,
            ),
            ("two_entry_params", TestInput::with_two_entry_params),
            (
                "an_entry_param_read_two_ways",
                TestInput::with_an_entry_param_read_two_ways,
            ),
            ("stack_param_and_arg", TestInput::with_stack_param_and_arg),
        ];

        let mut largest = ("", 0);
        for (name, build) in inputs {
            let size = data_json(&page_for(&build())).len();
            println!("{name}: {size} bytes");
            if size > largest.1 {
                largest = (name, size);
            }
        }

        let (name, size) = largest;
        assert!(
            size < CEILING,
            "the page for `{name}` is {size} bytes, over {CEILING}"
        );
    }

    /// The blobs the JS suites read.
    ///
    /// Without them, those suites would each hand-write a small blob and a
    /// change to the Rust shape would leave every JS test passing against a
    /// format that no longer exists.
    #[test]
    fn fixtures_are_up_to_date() {
        let fixtures: &[(&str, fn() -> TestInput)] = &[
            (
                "spills-and-reloads",
                TestInput::with_values_in_two_banks_spilled_and_reloaded,
            ),
            ("critical-edge", TestInput::with_a_critical_edge),
            ("spilled-merge-param", TestInput::with_spilled_merge_param),
            // The one prefix the other fixtures cannot show: a real allocation
            // over blocks the embedder called cold, hot, and merely unusual.
            ("block-kinds", || {
                let mut test = TestInput::with_spilled_merge_param();
                use crate::entity::{Block, Entity};
                let block = |i| Block::try_new(i).expect("a block index");
                test.set_block_frequency(block(1), crate::input::BlockFrequency::COLD);
                test.set_block_frequency(block(2), crate::input::BlockFrequency::HOT);
                test.set_block_frequency(block(3), crate::input::BlockFrequency::new(0.5));
                test
            }),
        ];

        let bless = std::env::var_os("REGICIDE_BLESS_FIXTURE").is_some();
        for (name, build) in fixtures {
            let test = build();
            let got = pretty_blob(&test);

            // A checked-in fixture is only reviewable if the same input always
            // produces the same bytes, so say so here rather than from a flaky
            // job later.
            assert_eq!(
                got,
                pretty_blob(&test),
                "the blob for `{name}` is not deterministic"
            );

            let path = std::path::Path::new(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/visualizer/test/fixtures"
            ))
            .join(format!("{name}.json"));

            if bless {
                std::fs::write(&path, &got).expect("the fixture writes");
                continue;
            }

            let want = std::fs::read_to_string(&path).unwrap_or_default();
            assert!(
                got == want,
                "`{name}.json` is out of date; re-bless it with \
                 `REGICIDE_BLESS_FIXTURE=1 cargo test --all-features`\n{}",
                first_difference(&got, &want)
            );
        }
    }

    /// The blob for `test`, pretty-printed.
    ///
    /// Round-tripping through a `Value` also sorts the keys, which costs
    /// nothing and makes a fixture diff readable.
    fn pretty_blob(test: &TestInput) -> String {
        allocated(test, |context, input| {
            let compact = viz_blob_json(context, input).expect("the blob serializes");
            let value: serde_json::Value =
                serde_json::from_str(&compact).expect("the blob is valid JSON");
            let mut pretty = serde_json::to_string_pretty(&value).expect("a `Value` serializes");
            pretty.push('\n');
            pretty
        })
    }

    /// Where two fixtures first disagree. `assert_eq!` on a megabyte of JSON
    /// is not a diff.
    fn first_difference(got: &str, want: &str) -> String {
        let got = Vec::from_iter(got.lines());
        let want = Vec::from_iter(want.lines());
        for (i, (a, b)) in got.iter().zip(want.iter()).enumerate() {
            if a != b {
                return format!(
                    "first difference at line {}:\n  got:  {a}\n  want: {b}",
                    i + 1
                );
            }
        }
        format!("got {} lines, want {}", got.len(), want.len())
    }
}
