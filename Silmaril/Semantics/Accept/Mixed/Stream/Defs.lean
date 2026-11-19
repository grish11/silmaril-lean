module

public import Silmaril.Semantics.Accept.Mixed.Defs

/-!
# Streaming mixed sessions: returns constrained by the pending buffer

`Silmaril.Accept.Mixed.ReturnsIn` constrains each return **for every parsing state**: for
`done() -> h` the related input is then any buffer, so an export specification phrased with it
cannot tie the returned tree to the values actually appended. Here the returns of a mixed trace
are read **along the trace**, with the append buffer the parsing host holds at each return.

* `accStep clears acc e`: the append buffer after the parsing event `e` from `acc` (one step of
  `Silmaril.Accept.Parse.pending`): `append v` appends `v`, `done` clears it when `clears`,
  `reset` clears it, every other event keeps it.
* `StreamRetFrom ppol σ R acc t`: reading `t` from the buffer `acc`, every parsing event `e`
  returning, from a parsing state whose buffer is the current one, a non-sentinel handle `h`
  for the input `w` with `σ h = some x` relates `(w, x) ∈ R`; writer events keep the buffer.
  For `done() -> h` the input is exactly the buffer: the values appended since the last `done`
  (`doneClears`) or `reset`. For one-shot `parse(v)` it is `[v]`; for `finish` the chunk buffer
  is still arbitrary.
* `StreamReturnsIn ppol σ R t := StreamRetFrom ppol σ R [] t`, from the empty buffer of the
  initial state.

The assume/guarantee theorems `Thms.mixedRel_subset_of_streamAG` and
`Thms.mixedFixedRel_subset_of_streamAG` replace `ReturnsIn` by `StreamReturnsIn`.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Accept.Mixed

open Silmaril.Accept.Handle Silmaril.Accept.Parse

universe u

variable {Op V H X : Type u}

/-- The append buffer after one parsing event (one step of `Silmaril.Accept.Parse.pending`). -/
def accStep (clears : Bool) : List V → PEv V H → List V
  | acc, .append v => acc ++ [v]
  | acc, .done _ => if clears then [] else acc
  | _, .reset => []
  | acc, _ => acc

/-- **The returns of a trace, read from the append buffer `acc`**: every return of a
non-sentinel handle, from a parsing state holding the current buffer, is related in `σ`. -/
def StreamRetFrom (ppol : PPolicy H) (σ : Env H X) (R : Set (List V × X)) :
    List V → List (MEv Op V H) → Prop
  | _, [] => True
  | acc, .w _ :: t => StreamRetFrom ppol σ R acc t
  | acc, .p e :: t =>
      (∀ ps w h ps', ps.acc = acc → Returns ppol ps e w h ps' → h ≠ ppol.sentinel →
        ∀ x, σ h = some x → (w, x) ∈ R) ∧
      StreamRetFrom ppol σ R (accStep ppol.doneClears acc e) t

/-- **The returns of a trace are related in `σ` along the trace**, from the empty buffer. -/
def StreamReturnsIn (ppol : PPolicy H) (σ : Env H X) (R : Set (List V × X))
    (t : List (MEv Op V H)) : Prop :=
  StreamRetFrom ppol σ R [] t

end Silmaril.Accept.Mixed
