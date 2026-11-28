module

import Silmaril.SSA.Isotope.LetSeq.StraightLine.Thms

namespace Silmaril.Isotope.LetSeq.StraightLine

open LocallyNameless (Derivation Equiv Tm)
open Silmaril.Isotope.Semantics (BoundEnv)
open Silmaril.Semantics.NondeterministicTrace

set_option backward.isDefEq.respectTransparency false

private abbrev β := (input.snoc Atom).snoc Atom
private abbrev β₁ := (β.snoc Atom).snoc Atom
private abbrev β₂ := (β₁.snoc Atom).snoc Atom

private def leftInput : Slot β := ⟨1, rfl⟩
private def rightInput : Slot β := ⟨0, rfl⟩
private def keptInput : Slot β₁ := ⟨3, rfl⟩
private def firstRight : Slot β₁ := ⟨0, rfl⟩
private def firstLeft : Slot β₂ := ⟨3, rfl⟩
private def secondLeft : Slot β₂ := ⟨1, rfl⟩

private def secondRequest (f : Request) (result : Slot β₂) : Term 5 :=
  .let₂ (requestTerm f keptInput.1 firstRight.1) (.bv result.1)

private def directTerm (f g : Request) (result : Slot β₂) : Term 3 :=
  .let₂ (requestTerm f leftInput.1 rightInput.1) (secondRequest g result)

private def direct (f g : Request) (result : Slot β₂) : Admitted β (directTerm f g result) :=
  .request f leftInput rightInput (.request g keptInput firstRight (.ret result))

private def directDerivation (f g : Request) (result : Slot β₂) :
    Derivation Request Γ₀ β (directTerm f g result) Atom :=
  canonicalDerivation (.request f leftInput rightInput (.request g keptInput firstRight (.ret result)))

private def boundTerm : Term 3 :=
  .let₁ (requestTerm (.ask false) leftInput.1 rightInput.1)
    (.let₂ (.bv 0)
      (Tm.let₂ (requestTerm (.ask true) keptInput.1 firstRight.1)
        (.let₁ (.bv firstLeft.1) (.bv 0))).underTwoBinders)

private def bound : Admitted β boundTerm :=
  .bound (.ask false) leftInput rightInput
    (.request (.ask true) keptInput firstRight (.aliasReturn firstLeft))

private noncomputable def boundDerivation : Derivation Request Γ₀ β boundTerm Atom :=
  Classical.choice (Derivation.ofHasType bound.replay.hasType.1)

private def mainTerm := directTerm (.ask false) (.ask true) firstLeft
private def main := direct (.ask false) (.ask true) firstLeft
private def mainDerivation := directDerivation (.ask false) (.ask true) firstLeft

-- A packet binder and a pure return alias disappear by native replay.
example : Equiv false Γ₀ input (.let₂ (.bv 0) boundTerm) (.let₂ (.bv 0) mainTerm) Atom :=
  .let₂ (.refl .bv) bound.replay

example :
    LetCase.LocallyNameless.Equiv false Γ₀ input (Morphism.SeqCase.embed (.let₂ (.bv 0) boundTerm))
      (Morphism.SeqCase.embed (.let₂ (.bv 0) mainTerm)) Atom :=
  (entry_embed_iff_native bound main boundDerivation mainDerivation).mpr (.let₂ (.refl .bv) bound.replay)

-- The second argument keeps the left input and the first right reply.
-- The result keeps the first left reply even after the second request.
example :
    ((2 : Nat), FreeMonoid.of ⟨.ask false, (0, 1), (2, 3)⟩ *
      FreeMonoid.of ⟨.ask true, (0, 3), (4, 5)⟩) ∈
    (run (entry mainDerivation) (packetEnv (0, 1))).outcomes := by
  rw [entry_run]
  unfold mainDerivation directDerivation
  rw [run_request]
  apply mem_request_trace.mpr
  refine ⟨(2, 3), FreeMonoid.of ⟨.ask true, (0, 3), (4, 5)⟩, ?_, rfl⟩
  rw [run_request]
  apply mem_request_trace.mpr
  refine ⟨(4, 5), 1, ?_, mul_one _⟩
  rfl

example : run (entry mainDerivation) (packetEnv (0, 1)) ≠
    run (entry (directDerivation (.ask true) (.ask false) firstLeft)) (packetEnv (0, 1)) := by
  intro h
  have normal := (entry_run_eq_iff_normal main (direct (.ask true) (.ask false) firstLeft)
    mainDerivation (directDerivation (.ask true) (.ask false) firstLeft)).mp h
  have changed := (Tm.op.inj (Tm.let₂.inj normal).1).1
  cases (Request.ask.inj changed)

-- Keeping the request sequence and arguments does not erase which reply
-- supplied the final projection.
example : run (entry mainDerivation) (packetEnv (0, 1)) ≠
    run (entry (directDerivation (.ask false) (.ask true) secondLeft)) (packetEnv (0, 1)) := by
  intro h
  have normal := (entry_run_eq_iff_normal main (direct (.ask false) (.ask true) secondLeft)
    mainDerivation (directDerivation (.ask false) (.ask true) secondLeft)).mp h
  have output := Tm.bv.inj (Tm.let₂.inj (Tm.let₂.inj normal).2).2
  contradiction

end Silmaril.Isotope.LetSeq.StraightLine
