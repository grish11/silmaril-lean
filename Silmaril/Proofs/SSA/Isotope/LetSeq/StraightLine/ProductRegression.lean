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
private abbrev Out : Types := .product (.product Atom .unit) (.product .unit Atom)

private def arg₀ : Assembly β Packet := .pair (.slot ⟨1, rfl⟩) (.slot ⟨0, rfl⟩)
private def arg₁ : Assembly β₁ Packet := .pair (.slot ⟨3, rfl⟩) (.slot ⟨0, rfl⟩)
private def result (secondReply : Slot β₂) : Assembly β₂ Out :=
  .pair (.pair (.slot ⟨3, rfl⟩) .unit) (.pair .unit (.slot secondReply))

private def secondLeft : Slot β₂ := ⟨1, rfl⟩
private def secondRight : Slot β₂ := ⟨0, rfl⟩

-- The native first argument unpacks and reassembles the input projections.
private def etaArgument : Term 3 := .let₂ arg₀.term (.pair (.bv 1) (.bv 0))

private def etaWitness : PureAssembly β etaArgument Packet :=
  .substituted
    (.let₂ .bv (.pair .bv .bv) : Derivation Request Γ₀ input
      (.let₂ (.bv 0) (.pair (.bv 1) (.bv 0))) Packet)
    (.let₂ .bv (.pair .bv .bv)) (Fin.cases arg₀ (fun i => i.elim0))

-- The second argument extracts a packet from a larger product containing a unit.
private def projectedArgument : Term 5 := .let₂ (.pair .unit arg₁.term) (.bv 0)

private def projectedWitness : PureAssembly β₁ projectedArgument Packet :=
  .substituted
    (.let₂ (.pair .unit .bv) .bv : Derivation Request Γ₀ input
      (.let₂ (.pair .unit (.bv 0)) (.bv 0)) Packet)
    (.let₂ (.pair .unit .bv) .bv) (Fin.cases arg₁ (fun i => i.elim0))

private def aliasedResult : Term 7 := .let₁ (result secondLeft).term (.bv 0)

private def resultWitness : PureAssembly β₂ aliasedResult Out :=
  .substituted
    (.let₁ .bv .bv : Derivation Request Γ₀ (.snoc .nil Out) (.let₁ (.bv 0) (.bv 0)) Out)
    (.let₁ .bv .bv) (Fin.cases (result secondLeft) (fun i => i.elim0))

private def expandedTerm : Term 3 :=
  .let₂ (.op (.ask false) etaArgument)
    (.let₂ (.op (.ask true) projectedArgument) aliasedResult)

private def expanded : ProductProgram β expandedTerm Out :=
  .request (.ask false) etaWitness
    (.request (.ask true) projectedWitness (.ret resultWitness))

private def compactTerm (reply : Slot β₂) : Term 3 :=
  .let₂ (.op (.ask false) arg₀.term) (.let₂ (.op (.ask true) arg₁.term) (result reply).term)

private def compact (reply : Slot β₂) : ProductProgram β (compactTerm reply) Out :=
  .request (.ask false) (.assembled arg₀)
    (.request (.ask true) (.assembled arg₁) (.ret (.assembled (result reply))))

private def compactTyping (reply : Slot β₂) : ProductCanonical β (compactTerm reply) Out :=
  .step (.ask false) arg₀ (.step (.ask true) arg₁ (.result (result reply)))

private theorem projected_replay : Equiv false Γ₀ β₁ projectedArgument arg₁.term Packet := by
  have typed := arg₁.derivation.toHasType
  apply (Equiv.pairBeta (pureEff := false) .unit typed .bv).trans
  apply (Equiv.let₁ .unit (Equiv.letEta typed.lift)).trans
  exact Equiv.letBeta .unit .unit typed.lift

private theorem replay : Equiv false Γ₀ β expandedTerm (compactTerm secondLeft) Out :=
  .let₂ (.op (Equiv.pairEta arg₀.derivation.toHasType))
    (.let₂ (.op projected_replay) (Equiv.letEta (result secondLeft).derivation.toHasType))

private noncomputable def expandedTyping : Derivation Request Γ₀ β expandedTerm Out :=
  Classical.choice (Derivation.ofHasType replay.hasType.1)

example :
    run (entry expandedTyping) (packetEnv (0, 1)) =
      run (entry (compactTyping secondLeft).derivation) (packetEnv (0, 1)) :=
  (entry_product_run_eq_iff_native expanded (compact secondLeft) expandedTyping
    (compactTyping secondLeft).derivation).mpr (.let₂ (.refl .bv) replay)

example : LetCase.LocallyNameless.Equiv false Γ₀ input
    (Morphism.SeqCase.embed (.let₂ (.bv 0) expandedTerm))
    (Morphism.SeqCase.embed (.let₂ (.bv 0) (compactTerm secondLeft))) Out :=
  (entry_product_embed_iff_native expanded (compact secondLeft) expandedTyping
    (compactTyping secondLeft).derivation).mpr (.let₂ (.refl .bv) replay)

private def observedResult : Value Out := (((2 : Nat), ()), ((), (4 : Nat)))

private def firstEvent : Event := ⟨.ask false, (0, 1), (2, 3)⟩
private def secondEvent : Event := ⟨.ask true, (0, 3), (4, 5)⟩

-- Both replies appear in the nested result and the first right reply is reused
-- in the second request. The units contribute no trace events.
example :
    (observedResult, FreeMonoid.of firstEvent * FreeMonoid.of secondEvent) ∈
    (run (entry (compactTyping secondLeft).derivation) (packetEnv (0, 1))).outcomes := by
  rw [entry_run]
  unfold compactTyping
  rw [run_product_step]
  apply mem_request_trace.mpr
  refine ⟨(2, 3), FreeMonoid.of secondEvent, ?_, rfl⟩
  rw [run_product_step]
  apply mem_request_trace.mpr
  refine ⟨(4, 5), 1, ?_, mul_one _⟩
  change (observedResult, 1) ∈ (run (result secondLeft).derivation _).outcomes
  rw [Assembly.run_eq_pure]
  rfl

-- A different projection leaves the primitive order and arguments intact but
-- changes one coordinate of the nested observation.
example :
    (observedResult, FreeMonoid.of firstEvent * FreeMonoid.of secondEvent) ∉
    (run (entry (compactTyping secondRight).derivation) (packetEnv (0, 1))).outcomes := by
  rw [entry_run]
  unfold compactTyping
  rw [run_product_step]
  intro observed
  obtain ⟨reply, tail, observed, trace⟩ := mem_request_trace.mp observed
  have events : Event.mk (.ask false) _ reply :: tail.toList =
      firstEvent :: secondEvent :: [] := congrArg FreeMonoid.toList trace
  have first := (Event.mk.inj (List.cons.inj events).1).2.2
  subst reply
  rw [run_product_step] at observed
  obtain ⟨reply, tail', observed, trace'⟩ := mem_request_trace.mp observed
  have last : Event.mk (.ask true) _ reply :: tail'.toList =
      secondEvent :: [] := (congrArg FreeMonoid.toList trace').trans (List.cons.inj events).2
  have second := (Event.mk.inj (List.cons.inj last).1).2.2
  subst reply
  change (observedResult, tail') ∈ (run (result secondRight).derivation _).outcomes at observed
  rw [Assembly.run_eq_pure] at observed
  cases observed

end Silmaril.Isotope.LetSeq.StraightLine
