module

public import Silmaril.Logic.Consequence.Defs
public import Cslib.Computability.Automata.Acceptors.Acceptor

/-!
# CSLib acceptors and their interpreters as consequence systems

A CSLib acceptor (`Cslib.Automata.Acceptor X α`: values `x : X` that accept words
`List α`) is a consequence system from acceptors to words. An interpreter that reads a
program `m : W` (for example a Wasm module or component) as an acceptor gives a system from
programs to words, and a partial decoder of program bytes gives a system from bytes to words.

| view | system | judgement `· ⊢ w` holds iff |
|---|---|---|
| `System.ofAcceptor X` | `System X (List α)` | `x` accepts `w` |
| `System.ofInterpreter interp` | `System W (List α)` | the acceptor `interp m` accepts `w` |
| `System.ofDecoder decode interp` | `System B (List α)` | `b` decodes to some `m` and `interp m` accepts `w` |

All three are reindexings of the first: `ofInterpreter interp` is
`(ofAcceptor X).pullback interp id`, and `ofDecoder` is the existential pullback along a partial
map. The row of a context is the acceptor's language (`Thms`: `ofAcceptor_row`, …), so
inclusion of systems is inclusion of languages, context by context (`ofInterpreter_le_iff`).

**Undecodable bytes prove nothing.** In `ofDecoder`, a `b` with `decode b = none` has an empty
row, the same row as bytes that decode to a program accepting nothing (`Thms`:
`ofDecoder_of_eq_none`). When the difference matters, keep the `Option` and use the
interpretations of `Silmaril.Logic.Consequence.Interp` (`Interp.ofDecode`, `Interp.Defined`).

The words are the *conclusions* and the acceptor the *context*. The single-context readings of
`Silmaril.Logic.Consequence.Accept` (`liftTTC tt L`, `liftCAll L`) are the row of one acceptor
(`Thms`: `pullback_const_ofAcceptor`). Nothing structural (weakening, cut) is claimed or
needed: the contexts are acceptors or programs, not sets of formulas.
-/

@[expose] public section

namespace Silmaril.Consequence

universe u v w t

namespace System

open Cslib.Automata (Acceptor)

/-- **An acceptor as a consequence system**: `x ⊢ w` iff the acceptor `x` accepts the word `w`. -/
def ofAcceptor (X : Type u) {α : Type v} [Acceptor X α] : System X (List α) :=
  fun x w => Acceptor.Accepts x w

/-- **An interpreter as a consequence system**: `m ⊢ w` iff the acceptor `interp m` accepts `w`.
The interpreter fixes everything that makes `m` an acceptor (semantics, ABI, environments). -/
def ofInterpreter {W : Type w} {X : Type u} {α : Type v} [Acceptor X α] (interp : W → X) :
    System W (List α) :=
  (ofAcceptor X).pullback interp id

/-- **Encoded programs as a consequence system**: `b ⊢ w` iff `b` decodes to some program `m`
and `interp m` accepts `w`. Bytes that do not decode prove nothing. -/
def ofDecoder {B : Type t} {W : Type w} {X : Type u} {α : Type v} [Acceptor X α]
    (decode : B → Option W) (interp : W → X) : System B (List α) :=
  fun b w => ∃ m, decode b = some m ∧ ofInterpreter interp m w

end System

end Silmaril.Consequence
