# DASL name/index sequences

`Silmaril.Formats.Dasl.IndexSequence.Thms` specifies two shallow DASL layouts
for the same ordered list of `(Name, Nat)` rows:

- Rows are a sequence of exactly two-element arrays, with caller-supplied
  codecs for names and naturals.
- Columns are a dictionary with exactly `t` (names) and `e` (indices).
  Each field takes a first-class sequence codec; the two fields need not use
  the same encoding. The raw columns codec preserves even unequal widths;
  converting to rows rejects unequal widths rather than truncating. Successful
  checked zip inverts unzip in both directions.

The index profile is supplied out of band. With `classId count`, `e[i]` is
a class identifier below `count`, independently of the row count. With
`orderedParent`, it is a row index: `e[i] = i` marks a root and every other
edge goes to a strictly earlier row. This is one acyclic parent-forest
profile, not a decoder for arbitrary union-find snapshots. Repeated names
are allowed for occurrences; the optional `asMap?` refinement checks global
name uniqueness. A successful checked decode certifies the selected guards,
not equality, congruence, or anything about what a decoded name denotes.

The flat sequence is an inline array. The paged sequence is an array of inline
arrays using the rope's payload split: full pages, then at most one nonempty
short page. Width is a positive caller parameter; the empty sequence has no
pages. The decoder checks the entire page-length vector. The flat and paged
round trips agree on ordered contents, not on DASL trees, serialized bytes,
or content names. There is no cost bound or external page resolver in this API.

Build the slice with `lake build --wfail +Silmaril.Formats.Dasl.IndexSequence.Thms`
and run `lake env lean -DwarningAsError=true --run tests/formats/DaslIndexSequence.lean`.
