module

public import Silmaril.ProofFormats.DaslSyntax.Database.Examples.Defs
public import Silmaril.ProofFormats.DaslSyntax.Database.Thms
public import Silmaril.Logic.HOLLight.Classical

public section

namespace Silmaril.Proofs.ProofFormats.DaslSyntax.DatabaseExamples

open Silmaril.ProofFormats.DaslSyntax.Database

namespace HOL

open Silmaril.Logic.HOLLight
open Examples.HOL

theorem premiseTyped : HasType initialSignature [] premise .bool := .fvar _ trivial

theorem assumed : Derives initialSignature [] {premise} premise := .assume premiseTyped

theorem consequenceProof : Derives initialSignature [] {premise} consequence := by
  apply Derives.impIntro HasType.truth
  exact assumed.weaken (fun _ hit => Finset.mem_insert_of_mem hit) (fun term hit => by
    rcases Finset.mem_insert.mp hit with rfl | hit
    · exact HasType.truth
    · rw [Finset.mem_singleton.mp hit]
      exact premiseTyped)

theorem closedProof : Silmaril.ProofFormats.DaslSyntax.Database.HOL.ClosedProof initialSignature [] closed := by
  refine ⟨?_, ?_, Derives.impIntro HasType.truth ?_⟩
  · simp only [closed, Tm.imp, Tm.conj, Tm.weaken, Tm.rename_truth]
    simp [Tm.truth, Tm.identity, Tm.equal, Tm.Scope]
  · simp [closed, Tm.imp, Tm.conj, Tm.truth, Tm.identity, Tm.equal, Tm.freeVars]
  · simpa only [Finset.insert_empty] using Derives.assume (sig := initialSignature) (theory := []) HasType.truth

end HOL

namespace MLTT

open Silmaril.Logic.TypeTheory.ExtensionalMLTT
open Examples.MLTT

private theorem lastCases_zero {Item : Sort _} (last : Item) (earlier : Fin 0 → Item) :
    Fin.lastCases last earlier (0 : Fin 1) = last := Fin.lastCases_last

private theorem natFormation : ECtx.JEq .nil (.univ 0) .nats .nats := .nats .nil_ok

private theorem familyFormation (name : String) :
    ECtx.JEq (.cons .nil name .nats) (.univ 0) (fiber.open name) (fiber.open name) := by
  have context : ECtx.JEq (.cons .nil name .nats) .unit .star .star :=
    .cons_ok .nil_ok (by simp [ECtx.dv]) natFormation
  have variableTyping : ECtx.JEq (.cons .nil name .nats) .nats (.fv name) (.fv name) :=
    .var context (.here _ _ _)
  simpa only [fiber, ETm.open, lastCases_zero] using
    ECtx.JEq.id (.nats (n := 0) context) variableTyping variableTyping

private theorem zeroTyping : ECtx.JEq .nil .nats .zero .zero := .zero .nil_ok

private theorem fiberWitness : ECtx.JEq .nil (fiber.lst .zero) (.refl .zero) (.refl .zero) := by
  simpa only [fiber, ETm.lst, lastCases_zero, ETm.castLE] using ECtx.JEq.refl zeroTyping

theorem sigmaFormation : ECtx.JEq .nil (.univ 0) sigma sigma :=
  .sigma (L := ∅) natFormation (fun name _ => familyFormation name)

theorem pairTyping : ECtx.JEq .nil sigma pair pair :=
  .pair (L := ∅) natFormation (fun name _ => familyFormation name) zeroTyping fiberWitness

theorem firstProjection : ECtx.JEq .nil .nats (.fst pair) .zero :=
  .beta_fst (L := ∅) natFormation (fun name _ => familyFormation name) zeroTyping fiberWitness

theorem secondProjection : ECtx.JEq .nil (fiber.lst .zero) (.snd pair) (.refl .zero) :=
  .beta_snd (L := ∅) natFormation (fun name _ => familyFormation name) zeroTyping fiberWitness

end MLTT

end Silmaril.Proofs.ProofFormats.DaslSyntax.DatabaseExamples
