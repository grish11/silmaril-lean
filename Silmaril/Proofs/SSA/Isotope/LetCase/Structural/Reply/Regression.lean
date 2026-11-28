module

import Silmaril.SSA.Isotope.LetCase.Structural.Reply.Thms

namespace Silmaril.Isotope.LetCase.Structural.Reply

open LocallyNameless (Derivation Tm)
open LetSeq.StraightLine.Structural (Log Event)
open Silmaril.Isotope.Semantics (BoundEnv)
open Silmaril.Semantics.NondeterministicTrace

local notation "Value" => LetSeq.StraightLine.Structural.Value

set_option backward.isDefEq.respectTransparency false

private inductive Generator where
  | choose
  | emit
  | request

private instance : HasTy Generator (Ty Empty) where
  src _ := .unit
  trg
    | .emit => .unit
    | .choose | .request => .coprod .unit .unit

private abbrev β : BoundCtx (Ty Empty) 1 := .snoc .nil .unit

private def env : BoundEnv Value β := BoundEnv.snoc (fun i => i.elim0) PUnit.unit

private def argumentTerm : Tm Empty Generator 1 :=
  .case (.op .choose .unit) (.op .emit .unit) .unit

private def argument : Derivation Generator Γ₀ β argumentTerm .unit :=
  .case (.op .unit) (.op .unit) .unit

private def request :
    Derivation Generator Γ₀ β (.op .request argumentTerm) (.coprod .unit .unit) :=
  .op argument

private def arm : Derivation Generator Γ₀ (β.snoc .unit) .unit .unit := .unit

private def emits : Derivation Generator Γ₀ (β.snoc .unit) (.op .emit .unit) .unit := .op .unit

private def chooseL : Log Empty Generator := FreeMonoid.of ⟨.choose, (), .inl ()⟩
private def chooseR : Log Empty Generator := FreeMonoid.of ⟨.choose, (), .inr ()⟩
private def emitted : Log Empty Generator := FreeMonoid.of ⟨.emit, (), ()⟩

-- The common argument can finish with different log lengths before the call.
private theorem argument_paths :
    (PUnit.unit, chooseL * emitted) ∈ (run argument env).outcomes ∧
    (PUnit.unit, chooseR) ∈ (run argument env).outcomes := by
  simp only [argument, run, Derivation.denote, pure_bind]
  constructor
  · exact Finite.mem_bind.mpr ⟨Sum.inl PUnit.unit, chooseL, emitted,
      ⟨Sum.inl PUnit.unit, rfl⟩, ⟨PUnit.unit, rfl⟩, rfl⟩
  · exact Finite.mem_bind.mpr ⟨Sum.inr PUnit.unit, chooseR, 1,
      ⟨Sum.inr PUnit.unit, rfl⟩, rfl, mul_one _⟩

-- A change confined to the second arm still separates these categorical
-- arrows, despite variable-length traces in the common argument.
example : traceArrow (.case request arm emits) ≠ traceArrow (.case request arm arm) := by
  intro equal
  have observations := (traceArrow_case_eq_iff_replies request arm arm emits arm).mp equal env
  obtain ⟨w, hw⟩ := (run_op_reaches_reply (α := Empty) Generator.request argument env (Sum.inr (α := PUnit) PUnit.unit)).mpr
    ⟨(PUnit.unit, chooseR), argument_paths.2⟩
  have right := observations.2 PUnit.unit w hw
  have logged : (PUnit.unit, emitted) ∈ (run emits (env.snoc PUnit.unit)).outcomes := by
    simp only [emits, run, Derivation.denote, pure_bind]
    exact ⟨PUnit.unit, rfl⟩
  rw [right] at logged
  have bad : (PUnit.unit, emitted) = (PUnit.unit, (1 : Log Empty Generator)) := logged
  let event : Event (α := Empty) (Φ := Generator) := ⟨.emit, (), ()⟩
  have words : [event] = [] :=
    congrArg FreeMonoid.toList (congrArg Prod.snd bad)
  cases words

end Silmaril.Isotope.LetCase.Structural.Reply
