// Layer 0: entity refs and labels.
//
// Pure, tiny, and imported from both sides of the worker boundary: the main
// thread needs to label and compare refs while rendering, and pulling
// `model.js` in for that would drag a second copy of the parsed blob onto the
// main thread and defeat the worker.
//
// A ref is `{kind, index}`. Only `model.js` invents one, by pairing a bare
// index from the blob with its type from the blob's `schema`; everything else
// passes refs around opaquely.

// The blob's `entityKinds`: kind name -> display prefix. Installed once per
// thread, because every function here is otherwise a pure function of a ref.
let prefixes = {};

// Kind names sorted so that the longest prefix is tried first: prefixes are not
// disjoint ("r" is a prefix of "rc", "reg" of "region") and a first match would
// read "rc12" as register 12.
let byLongestPrefix = [];

// Install the blob's prefix table. `main.js` and `worker.js` each call this
// once, with the same table.
export function install(entityKinds) {
  prefixes = { ...entityKinds };
  byLongestPrefix = Object.entries(prefixes)
    // `EventIndex` is an entity type in Rust, but an event is not something to
    // select and has no `byEntity` list. Commit 11 handles "event9" as its own
    // parser case, jumping to a log position.
    .filter(([kind]) => kind !== "EventIndex")
    .sort((a, b) => b[1].length - a[1].length);
}

// A string key for a ref, for `Map` keys and `data-` attributes.
//
// A rendering detail: nothing parses it back apart, and `sameEntity` is how
// refs are compared.
export function entityKey(ref) {
  return ref.kind + ":" + ref.index;
}

// How a ref is displayed: "v3", "r0", "span7".
export function entityLabel(ref) {
  const prefix = prefixes[ref.kind];
  return prefix === undefined ? entityKey(ref) : prefix + ref.index;
}

// Structural equality. Refs are copied across the worker boundary, so two refs
// for the same entity are never the same object.
export function sameEntity(a, b) {
  return a != null && b != null && a.kind === b.kind && a.index === b.index;
}

// Turn a search query into a ref, or `null` if it is not one.
//
// The longest prefix of the query that is a known entity prefix, and whose
// remainder is a non-empty run of decimal digits, wins.
export function parseEntityLabel(text) {
  for (const [kind, prefix] of byLongestPrefix) {
    if (!text.startsWith(prefix)) continue;
    const rest = text.slice(prefix.length);
    if (/^[0-9]+$/.test(rest)) return { kind, index: Number(rest) };
  }
  return null;
}

// The color a bundle's span bars are drawn in, from the ramp `main.css`
// defines. Commit 09 uses it; the ramp is here so that the model and the view
// agree on it.
export function bundleColor(index) {
  return "var(--bundle-" + (index % BUNDLE_RAMP_LENGTH) + ")";
}

// How many colors the ramp in `main.css` has.
export const BUNDLE_RAMP_LENGTH = 8;
