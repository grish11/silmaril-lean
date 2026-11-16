module

public import Silmaril.Logic.Consequence.HOL.Thms
import Silmaril.Proofs.Logic.Consequence.HOL.Separation

/-!
# HOL propositions as consequence systems: examples

* Structural rules from the closure theorems: `[p] ⊢ p`, weakening, and single cut in `seq`;
  `p ⊢ q, p` in `gentzen`.
* Closure under instantiation and extension, applied to a `seq` judgement.
* `gentzen_iff_seq_disjList` on `⊢ x, ¬x`, and `derives_le_globalSeq` on an axiom.
* **Local and global differ, concretely.** Over the initial signature, with free boolean
  variables `x`, `y`: `x ⊢ y` holds model-wise (`globalSeq`, no model validates `x`) but not
  point-wise (`seq`); `⊢ x, ¬x` holds point-wise (`gentzen`, the LK reading) but not model-wise
  (`globalGentzen`). Proofs: `Silmaril.Proofs.Logic.Consequence.HOL.Separation`.
-/

@[expose] public section

namespace Silmaril.Consequence.HOL.Examples

open Silmaril.Logic.HOLLight
open Silmaril.Logic.Institution.Metatheory (HolSig)
open Silmaril.Proofs.Logic.Consequence.HOL (S₀ var notVar)

variable {S T : HolSig} (p q r : HOLProp S)

example : seq.{0} S [p] p := seq_closed.refl trivial (List.mem_singleton_self p)

example (h : seq.{0} S [p] q) : seq.{0} S [r, p] q :=
  seq_closed.weak (fun _ hx => List.mem_cons_of_mem r hx) h

example (hq : seq.{0} S [p] q) (hr : seq.{0} S [q] r) : seq.{0} S [p] r := by
  simpa using Structural.cut_single (seq_closed.refl trivial) (seq_closed.cut trivial) hq hr

example : gentzen.{0} S [p] [q, p] :=
  gentzen_closed.refl trivial (List.mem_singleton_self p) (by simp)

example (h : S ≤ T) (hs : seq.{0} S [p] q) : seq.{0} T [p.map h] (q.map h) := seq_map h hs

example (σ : Nat → Ty) (hσ : ∀ i, (σ i).WellFormed S.sig.tyOps) (hs : seq.{0} S [p] q) :
    seq.{0} S [p.tySubst σ hσ] (q.tySubst σ hσ) := seq_tySubst σ hσ hs

/-! ## Local and global differ -/

example : globalSeq.{0} S₀ [var 0] (var 1) := Proofs.Logic.Consequence.HOL.globalSeq_var
example : ¬ seq.{0} S₀ [var 0] (var 1) := Proofs.Logic.Consequence.HOL.not_seq_var
example : gentzen.{0} S₀ [] [var 0, notVar 0] := Proofs.Logic.Consequence.HOL.gentzen_excluded
example : ¬ globalGentzen.{0} S₀ [] [var 0, notVar 0] :=
  Proofs.Logic.Consequence.HOL.not_globalGentzen_excluded

/-- So `seq` is strictly below `globalSeq`. -/
example : seq.{0} S₀ ≠ globalSeq.{0} S₀ := fun h =>
  Proofs.Logic.Consequence.HOL.not_seq_var (h ▸ Proofs.Logic.Consequence.HOL.globalSeq_var)

/-! ## Classical collapse and axioms -/

/-- `⊢ x, ¬x` is the single-conclusion `⊢ x ∨ (¬x ∨ ⊥)`. -/
example : seq.{0} S₀ [] (HOLProp.disjList [var 0, notVar 0]) :=
  (gentzen_iff_seq_disjList _ _).1 Proofs.Logic.Consequence.HOL.gentzen_excluded

/-- An axiom is a model-wise consequence of itself, through the kernel. -/
example : globalSeq.{0} S [p] p :=
  derives_le_globalSeq (Derives.axiom (List.mem_singleton_self p.1) p.2)

end Silmaril.Consequence.HOL.Examples
