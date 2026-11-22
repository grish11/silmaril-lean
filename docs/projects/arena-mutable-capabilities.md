# Exclusive-state arena capabilities

`Silmaril.Semantics.Arena.Mutable.{Defs,Thms}` adds an explicit-key
capability to the existing slot model. It does not change any of the slot,
CAS, or Prolly APIs. `Access.read` is a pure observation; `Access.change`
receives one current state and can return one successor. This shape models
the call boundary of a Rust method taking `&mut self`, not a borrow checker,
linear type system, concurrency contract, or executable Rust refinement.

| Command | Hole | Occupied reservation or resident |
| --- | --- | --- |
| `reserve` | Occupied, anonymous reservation | `.occupied` |
| `insert obj` | Occupied, anonymous resident | `.occupied` |
| `replace obj` | `.vacant` | Occupied, anonymous resident; old local name dropped |
| `remove` | `.vacant` | Hole |

`Cell Obj = Option (Option Obj)` does not identify a reservation with a hole.
`Change.run_raw` states the point-update specification; `Access.raw_spec`
gives the unchanged-key frame. `Mutation.bind` sequences tentative states
and `Mutation.commit` retains the original state if the composite fails. This
is an atomic visibility contract; a backend that performs irreversible I/O
before reporting failure does not implement it without extra staging.

`Access.raw` supports any key with decidable equality. `Access.array` is a
fixed-capacity Nat implementation: it agrees with the raw backend in bounds
and reports `.outOfBounds` elsewhere. `Allocator` is optional and has its own
error type. `Growing.allocate` always appends in the pure model, even if
earlier holes exist, and preserves their observations. This models neither
finite-memory allocation success nor the liveness of an arbitrary handle:
explicit-key insertion can reuse holes, and the caller must establish any
stronger reference invariant. `Examples` exercises occupancy and faults,
rollback, append and a String-keyed arena.

For the Rust API comparison, pin Rust 1.98.1 to
`48a229ceaefd4985c50990b14116b6d856af0985`: see `library/core/src/option.rs`,
`library/core/src/result.rs`, and `library/alloc/src/vec/mod.rs` in the Rust
source. A Rust allocator may fail independently of the logical edit. A trace
of `(command, read/result, live cells)` is the backend conformance seam;
allocation count, byte copies and disk I/O are separate measurements, not
consequences of this extensional equivalence.
