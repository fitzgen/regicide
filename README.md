<div align="center">
  <h1><code>regicide</code></h1>
  <p>
    <strong>A region-based, backtracking register allocator</strong>
  </p>
</div>

# Usage

TODO FITZGEN

# Serializing and Deserializing Register Allocation Inputs

When the `"serialize"` and `"deserialize"` cargo features are enabled,
`regicide` can serialize and deserialize register allocation inputs
respectively, which allows for offline replay, profiling, analysis,
visualization, etc...

See the [`serialize`] and [`deserialize`] modules for details.

# Visualizing Register Allocation

When the `"visualizer"` cargo feature is enabled, `regicide` can write a
self-contained HTML visualization of an input and its resulting register
allocations.

See the [`Output::write_visualization_html`] method for details.
