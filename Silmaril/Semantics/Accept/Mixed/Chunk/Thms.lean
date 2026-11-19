module

public import Silmaril.Semantics.Accept.Mixed.Chunk.Defs
public import Silmaril.Semantics.Accept.Mixed.Thms
import Silmaril.Proofs.Semantics.Accept.Mixed.Chunk.Basic

/-!
# Chunk mixed sessions: laws

* `chunkFold_append`: `chunkFold` along a concatenation;
* `pstep_buf`: outside undefined behaviour a parsing step moves the chunk buffer by `chunkStep`
  (a `finish` overrun under `callTrap`/`ignore` leaves it, as `chunkStep` does);
* **assume/guarantee along the chunk buffer** (`mixedRel_subset_of_chunkAG`, store semantics
  without undefined behaviour; `mixedFixedRel_subset_of_chunkAG`, fixed environments for every
  writer policy): if in every trace of `T` whose writes agree with `σ` (every `σ`, resp. every
  `ρ ∈ Envs`), every return at `t = u ++ .p e :: v` from a parsing state whose buffer is
  `chunkFold [] (parseEvents u)` of a non-sentinel handle denoting `x` in `σ` relates
  `(w, x) ∈ R`, the relation is in `R`.
-/

@[expose] public section

namespace Silmaril.Accept.Mixed

open Silmaril.Accept Silmaril.Accept.Handle Silmaril.Accept.Parse

universe u

variable {Op V H X : Type u}

theorem chunkFold_append (b : List V) (t u : List (PEv V H)) :
    chunkFold b (t ++ u) = chunkFold (chunkFold b t) u := by
  simp [chunkFold, List.foldl_append]

variable [DecidableEq H] {W : Writer Op X} {pol : Policy H} {ppol : PPolicy H}

/-- **A parsing step moves the chunk buffer by `chunkStep`**, outside undefined behaviour. -/
theorem pstep_buf {σ : Env H X} {s s' : PState V} {e : PEv V H} {A : Set (List V × X)}
    (hs : PStep ppol σ s e s' A) (hc : s.phase ≠ .chaos) : s'.buf = chunkStep s.buf e :=
  Silmaril.Proofs.Semantics.Accept.Mixed.Chunk.pstep_buf hs hc

/-- **Assume/guarantee along the chunk buffer**, store semantics without undefined behaviour. -/
theorem mixedRel_subset_of_chunkAG (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub)
    (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) {T : Set (List (MEv Op V H))}
    {R : Set (List V × X)}
    (hAG : ∀ t ∈ T, ∀ σ, WritesAgree W pol.sentinel σ t → ∀ u e v, t = u ++ .p e :: v →
      ∀ ps w h ps', ps.buf = chunkFold [] (parseEvents u) → Returns ppol ps e w h ps' →
        h ≠ ppol.sentinel → ∀ x, σ h = some x → (w, x) ∈ R) :
    mixedRel W pol ppol T ⊆ R :=
  Silmaril.Proofs.Semantics.Accept.Mixed.Chunk.mixedRel_subset_of_chunkAG hw ha hb ho hAG

/-- **Assume/guarantee along the chunk buffer, fixed environments**, for every writer policy. -/
theorem mixedFixedRel_subset_of_chunkAG (hb : ppol.onBadHandle ≠ .ub)
    (ho : ppol.onOverrun ≠ .ub) {Envs : Set (Env H X)} {T : Set (List (MEv Op V H))}
    {R : Set (List V × X)}
    (hAG : ∀ ρ ∈ Envs, ∀ t ∈ T, WritesAgree W pol.sentinel ρ t → ∀ u e v, t = u ++ .p e :: v →
      ∀ ps w h ps', ps.buf = chunkFold [] (parseEvents u) → Returns ppol ps e w h ps' →
        h ≠ ppol.sentinel → ∀ x, ρ h = some x → (w, x) ∈ R) :
    mixedFixedRel W pol ppol Envs T ⊆ R :=
  Silmaril.Proofs.Semantics.Accept.Mixed.Chunk.mixedFixedRel_subset_of_chunkAG hb ho hAG

end Silmaril.Accept.Mixed
