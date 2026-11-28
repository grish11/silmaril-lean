module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Signature.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms

public section

set_option backward.isDefEq.respectTransparency false

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.Theory (TypingIndex)
open Silmaril.Isotope.LetCase.LocallyNameless
open LambdaSSA.Acyclic (Code contextMap contextMap_isIso)
open LetIter.Semantics.Categorical (TypeModel InstructionModel)
open LambdaSSA.Semantics.Categorical (denoteRegion labelInject singletonLabelPayload)

variable {τ ε : Type} [TypeFormers τ]

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)

theorem compile_reify_proof {P : InstrSig τ ε} (e : CaseEquation P) :
    compile (reify e) = e := by
  obtain ⟨⟨n, β, A⟩, ⟨a, da⟩, ⟨b, db⟩⟩ := e
  simp only [compile, reify, Code.toLetCase_ofLetCase]

private theorem reified_side_map {P Q : InstrSig τ ε} (g : P ⟶ Q)
    {i : TypingIndex τ} (x : Models.Carrier P.Instr Γ₀ i) :
    (Code.ofLetCase ((PresSig.translate ((LetCase.pres Γ₀).map g)).map x).2).toSSA 0 =
      ((Code.ofLetCase x.2).toSSA 0).mapInstr (InstrSig.Hom.instr g) := by
  obtain ⟨n, β, A⟩ := i
  let x' := (PresSig.translate ((LetCase.pres Γ₀).map g)).map x
  have term : x'.1 = x.1.mapInstr (InstrSig.Hom.instr g) := LetCase.translate_fst Γ₀ g x
  let d := x.2.mapSignature (InstrSig.Hom.toSignatureMap g)
  have compare {t : Tm Empty Q.Instr n} (d' : Derivation Q.Instr Γ₀ β t A)
      (agree : t = x.1.mapInstr (InstrSig.Hom.instr g)) :
      (Code.ofLetCase d').toSSA 0 = (Code.ofLetCase d).toSSA 0 := by
    cases agree
    exact Code.ofLetCase_toSSA_congr d' d 0
  exact (compare x'.2 term).trans ((congrArg (fun c => c.toSSA 0)
    (Code.ofLetCase_mapSignature (InstrSig.Hom.toSignatureMap g) x.2)).trans
    (Code.toSSA_mapSignature (InstrSig.Hom.toSignatureMap g) _ 0))

theorem reify_mapSentence_proof {P Q : InstrSig τ ε} (g : P ⟶ Q) (e : CaseEquation P) :
    let e' := (((LetCase.inst Γ₀).map g).sen e : CaseEquation Q)
    ((reify e').2.1.toSSA 0, (reify e').2.2.toSSA 0) =
      ((reify e).2.1.toSSA 0 |>.mapInstr (InstrSig.Hom.instr g),
       (reify e).2.2.toSSA 0 |>.mapInstr (InstrSig.Hom.instr g)) :=
  Prod.ext (reified_side_map g e.2.1) (reified_side_map g e.2.2)

section FreydModels

variable {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  {J : V ⥤ C} [DistributiveFreydCategory J] {P : InstrSig τ ε}

theorem freydCaseAlgebra_denote_proof (M : TypeModel τ V) (I : InstructionModel J M P.Instr)
    {n : Nat} {β : BoundCtx τ n} {A : τ}
    {t : Isotope.LetCase.LocallyNameless.Tm Empty P.Instr n} (d : Derivation P.Instr Γ₀ β t A) :
    let _ := I
    Models.denote (freydCaseAlgebra J M I) d = Isotope.LetCase.Semantics.Categorical.denote J M d := by
  let _ := I
  induction d <;> simp_all only [freydCaseAlgebra, Models.denote, freydCaseOperation,
    Isotope.LetCase.Semantics.Categorical.denote, Fin.cases_zero]
  all_goals rfl

end FreydModels

section Models

variable {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] {P : InstrSig τ ε}

omit [FreydCategory.CentralUnit J] in
private theorem caseAlgebra_denote (K : CoherentRegionModel J P)
    {n : Nat} {β : BoundCtx τ n} {A : τ}
    {t : Isotope.LetCase.LocallyNameless.Tm Empty P.Instr n} (d : Derivation P.Instr Γ₀ β t A) :
    let _ := K.instructions
    Models.denote K.caseAlgebra d = Isotope.LetCase.Semantics.Categorical.denote J K.types d :=
  freydCaseAlgebra_denote_proof K.types K.instructions d

theorem sat_compile_iff_proof (K : CoherentRegionModel J P) (e : SSAEquation P) :
    ((LetCase.inst Γ₀).obj P).Sat K.caseAlgebra (compile e) ↔
      K.denoteSSA e.2.1 = K.denoteSSA e.2.2 := by
  let _ := K.instructions
  let _ := K.coherent
  obtain ⟨⟨n, β, A⟩, a, b⟩ := e
  have h : LambdaSSA.At [A] 0 A := rfl
  rw [compile, LetCase.sat_iff, caseAlgebra_denote, caseAlgebra_denote]
  simp only [CoherentRegionModel.denoteSSA, Code.denote_toSSA J K.types _ h]
  let _ := contextMap_isIso K.types β
  constructor
  · intro equal
    rw [equal]
  · intro equal
    have rhs := congrArg (fun f => f ≫ J.map (singletonLabelPayload K.types A)) equal
    simp only [Category.assoc, ← J.map_comp, LambdaSSA.Semantics.Categorical.SingletonDispatcher.labelInject_payload,
      J.map_id, Category.comp_id] at rhs
    exact (cancel_epi (J.map (contextMap K.types β))).mp rhs

theorem denote_eq_of_sameTerm_proof (K : CoherentRegionModel J P)
    {n : Nat} {β : BoundCtx τ n} {A : τ} {t : Tm Empty P.Instr n}
    (d d' : Derivation P.Instr Γ₀ β t A) :
    letI := K.instructions
    Isotope.LetCase.Semantics.Categorical.denote J K.types d =
      Isotope.LetCase.Semantics.Categorical.denote J K.types d' := by
  let _ := K.instructions
  let e : CaseEquation P := ⟨⟨n, β, A⟩, ⟨t, d⟩, ⟨t, d'⟩⟩
  have eqRegion {r s : LambdaSSA.Region P.Instr} (h : r = s)
      (hr : LambdaSSA.Region.HasType β.toList r [A])
      (hs : LambdaSSA.Region.HasType β.toList s [A]) :
      denoteRegion J K.types hr = denoteRegion J K.types hs := by
    cases h
    rfl
  have agree : K.denoteSSA (reify e).2.1 = K.denoteSSA (reify e).2.2 :=
    eqRegion (Code.ofLetCase_toSSA_congr d d' 0) _ _
  have sat := (sat_compile_iff_proof K (reify e)).mpr agree
  rw [compile_reify_proof] at sat
  exact (caseAlgebra_denote K d).symm.trans
    (((LetCase.sat_iff Γ₀ P K.caseAlgebra d d').mp sat).trans (caseAlgebra_denote K d'))

end Models
end Silmaril.Isotope.Institution.Acyclic
