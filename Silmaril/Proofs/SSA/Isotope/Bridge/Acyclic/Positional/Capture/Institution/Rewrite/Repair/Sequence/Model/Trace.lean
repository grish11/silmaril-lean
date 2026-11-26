module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Sequence.Model.Defs

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Sequence

open CategoryTheory
open Isotope.Semantics (BoundEnv)
open Isotope.LetCase.LocallyNameless (AbortEquiv Derivation Tm)
open LambdaSSA.Region (packedExitType)
open LetIter.Semantics.Categorical (boundEnv boundObj denoteOfType denoteOfType_eq denoteOfType_eq_of_abortEquiv)
open Morphism.CaseIter (derivation denote_derivation)
open Silmaril.Elgot

set_option backward.isDefEq.respectTransparency false

local notation "Γ₀" => (Ctx.nil : Ctx Empty Sorts)

private theorem embed_denote {n : Nat} {β : BoundCtx Sorts n}
    {t : Tm Empty signature.Instr n} {A : Sorts} (h : Derivation signature.Instr Γ₀ β t A) :
    letI := traceInstructions
    Isotope.LetCase.Semantics.Categorical.denote traceJ traceTypes h =
      denoteOfType value model (derivation h) := by
  let _ := traceInstructions
  induction h with
  | fv hi => cases hi
  | bv | unit => rfl
  | op _ ih | inl _ ih | inr _ ih | abort _ ih =>
    simp only [derivation, Isotope.LetCase.Semantics.Categorical.denote,
      denoteOfType, LetIter.Semantics.Categorical.denote] at ih ⊢
    rw [ih]
  | let₁ _ _ ih₁ ih₂ | let₂ _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ =>
    simp only [derivation, Isotope.LetCase.Semantics.Categorical.denote,
      denoteOfType, LetIter.Semantics.Categorical.denote] at ih₁ ih₂ ⊢
    rw [ih₁, ih₂]
  | case _ _ _ ih₁ ih₂ ih₃ =>
    simp only [derivation, Isotope.LetCase.Semantics.Categorical.denote,
      denoteOfType, LetIter.Semantics.Categorical.denote] at ih₁ ih₂ ih₃ ⊢
    rw [ih₁, ih₂, ih₃]

private theorem run_stop {A : Type} (bit : Bool) (k : PEmpty → Trace A) :
    ((model.eval (Op.stop bit) PUnit.unit >>= k).run.run) = Part.some (.error bit, 1) := by
  change (Part.some (.error bit, (1 : FreeMonoid Bool)) >>= fun (res, word) =>
    (fun (out, more) => (out, word * more)) <$> (ExceptT.bindCont k res).run) = _
  rw [Part.bind_eq_bind, Part.bind_some]
  rfl

private theorem run_emit {A : Type} (bit : Bool) (k : PUnit → Trace A) :
    ((model.eval (Op.emit bit) PUnit.unit >>= k).run.run) =
      (fun (out, more) => (out, FreeMonoid.of bit * more)) <$> (k PUnit.unit).run.run := by
  change (Part.some (.ok PUnit.unit, FreeMonoid.of bit) >>= fun (res, word) =>
    (fun (out, more) => (out, word * more)) <$> (ExceptT.bindCont k res).run) = _
  rw [Part.bind_eq_bind, Part.bind_some]
  rfl

theorem operand_run_proof (p : Body) {n : Nat} {β : BoundCtx Sorts n} (ρ : BoundEnv value β) :
    run (p.operand β).2 ρ = p.normal.observe PUnit.unit := by
  induction p generalizing n with
  | returnUnit => rfl
  | emit bit next ih =>
    simp only [run, Body.operand, Derivation.denote, pure_bind, Body.normal, Normal.observe, FreeMonoid.ofList_cons]
    change ((model.eval (Op.emit bit) PUnit.unit >>= fun u =>
      (next.operand (β.snoc Ty.unit)).2.denote value model noFree (ρ.snoc u)).run.run) = _
    rw [run_emit, ← run, ih (ρ.snoc (A := Ty.unit) PUnit.unit)]
    simp only [Normal.observe, Part.map_eq_map, Part.map_some]
  | stop bit seq =>
    cases seq <;> simp only [run, Body.operand, Derivation.denote, pure_bind, Body.normal,
      Normal.observe, Option.elim, FreeMonoid.ofList_nil] <;> exact run_stop bit _

theorem sum_tag_run_proof {B : Type} (a : Trace PUnit) :
    ((a >>= fun u => (pure (.inl u) : Trace (PUnit ⊕ B))).run.run) =
      (fun (result, word) => (result.map Sum.inl, word)) <$> a.run.run := by
  change (a.run.run >>= fun (res, w) =>
    (fun (out, more) => (out, w * more)) <$>
      (ExceptT.bindCont (fun u => (pure (.inl u) : Trace (PUnit ⊕ B))) res).run) = _
  rw [Part.bind_eq_bind, Part.map_eq_map, ← Part.bind_some_eq_map]
  congr 1
  funext x
  obtain ⟨res, w⟩ := x
  cases res with
  | error e =>
    change Part.map _ (Part.some ((Except.error e : Except Bool (PUnit ⊕ B)), 1)) =
      Part.some (Except.error e, w)
    simp [Part.map_some]
  | ok u =>
    change Part.map _ (Part.some ((Except.ok (.inl u) : Except Bool (PUnit ⊕ B)), 1)) =
      Part.some (Except.ok (Sum.inl u), w)
    simp [Part.map_some]

theorem observe_injective_proof {A : Type} (a : A) :
    Function.Injective (fun nf : Normal => nf.observe a) := by
  intro p q h
  have unpacked := Part.some_injective h
  apply Prod.ext
  · exact congrArg (fun x => (FreeMonoid.toList x.2)) unpacked
  · have terminal := congrArg Prod.fst unpacked
    cases hp : p.2 <;> cases hq : q.2 <;> simp_all [Option.elim]

set_option maxHeartbeats 800000 in
private theorem pack_run (tail : List Sorts) (p : Body) (ρ : BoundEnv value .nil) :
    run (Rewrite.returnUnit tail (p.operand .nil)).toLetCase.2 ρ =
      p.normal.observe (Sum.inl PUnit.unit : PUnit ⊕ value (packedExitType tail)) := by
  let entry := (p.operand .nil).2
  change (Derivation.denote value model
    (.let₁ entry (.let₁ (.bv (ι := 0)) (.inl (.bv (ι := 0))))) noFree ρ).run.run = _
  simp only [Derivation.denote, pure_bind]
  change (((entry.denote value model noFree ρ) >>= fun u =>
    (pure (Sum.inl u) : Trace (PUnit ⊕ value (packedExitType tail)))).run.run) = _
  refine (sum_tag_run_proof (B := value (packedExitType tail))
    (show Trace PUnit from entry.denote value model noFree ρ)).trans ?_
  change ((fun (result, word) => (result.map Sum.inl, word)) <$>
    ((p.operand .nil).2.denote value model noFree ρ).run.run) = _
  rw [← run, operand_run_proof]
  simp only [Normal.observe, Part.map_eq_map, Part.map_some]
  cases p.normal.2 <;> rfl

theorem traceSat_run_proof (e : GrammarEquation signature)
    (sat : ((LetCase.inst Γ₀).obj signature).Sat traceAlgebra (grammarCase e))
    (ρ : boundObj traceTypes e.1.bound) :
    run (grammarCase e).2.1.2 (boundEnv value ρ) =
      run (grammarCase e).2.2.2 (boundEnv value ρ) := by
  let d := (grammarCase e).2.1.2
  let d' := (grammarCase e).2.2.2
  have eq := (LetCase.sat_iff Γ₀ signature traceAlgebra d d').mp sat
  let _ := traceInstructions
  change Isotope.LetCase.LocallyNameless.Models.denote
      (freydCaseAlgebra traceJ traceTypes traceInstructions) d =
    Isotope.LetCase.LocallyNameless.Models.denote (freydCaseAlgebra traceJ traceTypes traceInstructions) d' at eq
  rw [freydCaseAlgebra_denote, freydCaseAlgebra_denote, embed_denote, embed_denote] at eq
  have obs := congrArg (fun f =>
    (show Trace (value (packedExitType e.1.exits)) from f.of (PUnit.unit, ρ)).run.run) eq
  have free : LetIter.Semantics.Categorical.freeEnv value (Γ := Γ₀) PUnit.unit = noFree := by
    funext x
    exact x.elim
  simp only [denoteOfType_eq, denote_derivation, free] at obs
  exact obs

theorem traceSat_normal_proof (tail : List Sorts) (p q : Body)
    (sat : ((LetCase.inst Γ₀).obj signature).Sat traceAlgebra (grammarCase (equation tail p q))) :
    p.normal = q.normal := by
  have obs := traceSat_run_proof (equation tail p q) sat PUnit.unit
  exact observe_injective_proof _
    ((pack_run tail p _).symm.trans (obs.trans (pack_run tail q _)))

theorem traceSat_of_repaired_proof (s : GrammarEquation signature) (h : Repaired false s) :
    ((LetCase.inst Γ₀).obj signature).Sat traceAlgebra (grammarCase s) := by
  let d := (grammarCase s).2.1.2
  let e := (grammarCase s).2.2.2
  apply (LetCase.sat_iff Γ₀ signature traceAlgebra d e).mpr
  let _ := traceInstructions
  change Isotope.LetCase.LocallyNameless.Models.denote
      (freydCaseAlgebra traceJ traceTypes traceInstructions) d =
    Isotope.LetCase.LocallyNameless.Models.denote (freydCaseAlgebra traceJ traceTypes traceInstructions) e
  rw [freydCaseAlgebra_denote, freydCaseAlgebra_denote, embed_denote, embed_denote]
  apply denoteOfType_eq_of_abortEquiv (Empty.elim : Empty → Type) model _ (AbortEquiv.toLetIter h)
  intro f hf
  cases f <;> cases hf

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Sequence
