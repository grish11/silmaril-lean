module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Model.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Singleton.Defs
import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Kleisli.Thms
import Silmaril.SSA.Isotope.LetSeq.StraightLine.Structural.Categorical.Thms

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native

open CategoryTheory CategoryTheory.Limits
open LambdaSSA.Semantics.Categorical (denoteRegion RegionTypingCoherent singletonLabelPayload
  labelInject denoteSingletonRegion)
open LambdaSSA.Semantics.Categorical.SingletonDispatcher (labelInject_payload payload_labelInject)
open LetIter.Semantics.Categorical (TypeModel InstructionModel TypingCoherent ofTypeModel ofInstructionModel)
open LetCase.Structural.Reply (Γ₀ traceArrow valid_of_equiv)
open LetCase.Structural.Finite (Types Context StructuralContext)
open LetCase.LocallyNameless (Derivation Equiv)
open LetSeq.StraightLine.Structural (Value Trace model)
open LetSeq.StraightLine.Structural.Categorical (traceJ traceTypes traceInstructions)
open scoped MonoidalCategory LetCase.Structural.Finite LetSeq.StraightLine.Structural

set_option backward.isDefEq.respectTransparency false

section Model

universe u v u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (M : TypeModel τ V) [InstructionModel J M Φ]
  [RegionTypingCoherent (Φ := Φ) J M]

local notation "caseDenote" => LetCase.Semantics.Categorical.denote J M
local notation "iterDenote" => LetIter.Semantics.Categorical.denote J M
local notation "ssaDenote" => denoteRegion J M

omit [FreydCategory.CentralUnit J] [RegionTypingCoherent (Φ := Φ) J M] in
theorem denote_caseIter_proof {n : Nat} {β : BoundCtx τ n} {t : LetCase.LocallyNameless.Tm Empty Φ n} {A : τ}
    (d : Derivation Φ (.nil : Ctx Empty τ) β t A) :
    iterDenote (Morphism.CaseIter.derivation d) = caseDenote d := by
  induction d <;> simp_all only [Morphism.CaseIter.derivation,
    LetCase.Semantics.Categorical.denote, LetIter.Semantics.Categorical.denote]

theorem Endpoint.denote_code_proof {n : Nat} {β : BoundCtx τ n} {A : τ} (p : Endpoint Φ β A)
    (c : Code Φ β A) (written : c.toSSA 0 = p.region) :
    ssaDenote p.typed = J.map (contextMap M β) ≫ caseDenote c.toLetCase.2 ≫
      J.map (labelInject M 0 (rfl : At [A] 0 A)) := by
  have same {r s : Region Φ} (e : r = s) (hr : Region.HasType β.toList r [A])
      (hs : Region.HasType β.toList s [A]) : ssaDenote hr = ssaDenote hs := by
    subst s
    rfl
  exact (same written.symm p.typed (c.toSSA_hasType rfl)).trans
    (c.denote_toSSA J M (rfl : At [A] 0 A))

theorem Endpoint.denote_eq_iff_proof {n : Nat} {β : BoundCtx τ n} {A : τ}
    (p q : Endpoint Φ β A) :
    ssaDenote p.typed = ssaDenote q.typed ↔
      caseDenote p.compile.2 = caseDenote q.compile.2 := by
  rw [p.denote_code_proof J M p.code p.code_exact, q.denote_code_proof J M q.code q.code_exact]
  change (J.map (contextMap M β) ≫ caseDenote p.compile.2 ≫ _) =
    (J.map (contextMap M β) ≫ caseDenote q.compile.2 ≫ _) ↔ _
  have := contextMap_isIso M β
  constructor
  · intro eq
    have out := congrArg (fun f => f ≫ J.map (singletonLabelPayload M A)) eq
    simp only [Category.assoc, ← J.map_comp, labelInject_payload, J.map_id, Category.comp_id] at out
    exact (cancel_epi (J.map (contextMap M β))).mp out
  · intro eq
    rw [eq]

theorem Endpoint.denoteSingleton_eq_iff_proof {X A : τ}
    (p q : Endpoint Φ (.snoc .nil X) A) :
    denoteSingletonRegion J M p.typed = denoteSingletonRegion J M q.typed ↔
      caseDenote p.compile.2 = caseDenote q.compile.2 := by
  unfold denoteSingletonRegion
  rw [← Endpoint.denote_eq_iff_proof J M p q]
  constructor
  · intro eq
    have e := (cancel_epi (J.map (λ_ (M.obj X)).inv)).mp eq
    have out := congrArg (fun f => f ≫ J.map (labelInject M 0 (rfl : At [A] 0 A))) e
    simpa only [Category.assoc, ← J.map_comp, payload_labelInject, J.map_id, Category.comp_id] using out
  · intro eq
    rw [eq]

end Model

section Trace

open Silmaril.Elgot

variable {Φ : Type} [HasTy Φ Types]

private def traceSig : Isotope.Institution.InstrSig Types Bool where
  Instr := Φ
  hasTy := inferInstance
  hasEff := inferInstance

theorem trace_region_coherent_proof :
    let := traceInstructions (α := Empty) (Φ := Φ)
    RegionTypingCoherent (Φ := Φ) (traceJ (α := Empty) (Φ := Φ)) (traceTypes Empty) := by
  have coherent (F : Empty → Type) (T : Isotope.Semantics.InstructionModel (Ty.denote F) Φ (Trace Empty Φ)) :
      letI := ofInstructionModel (Ty.denote F) T
      RegionTypingCoherent (Φ := Φ) (traceJ (α := Empty) (Φ := Φ)) (ofTypeModel (Ty.denote F)) := by
    have eq : F = Empty.elim := funext fun x => x.elim
    subst F
    let bad : {B : Type} → Trace Empty Φ B := fun {_} =>
      Silmaril.Semantics.NondeterministicTrace.Finite.ofOutcomes ∅
    exact Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.regionCoherent (m := Trace Empty Φ) (P := traceSig) T
      (fun f hf => by cases hf) (fun {_} => bad)
  exact coherent (fun _ => Nat) model

end Trace

section Finite

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ] {n : Nat} {β : Context n} {A : Types}

private theorem trace_of_valid {p q : Endpoint Φ β A} (valid : p.Valid q) :
    traceArrow p.compile.2 = traceArrow q.compile.2 := by
  classical
  let := traceInstructions (α := Empty) (Φ := Φ)
  let := trace_region_coherent_proof (Φ := Φ)
  let J := traceJ (α := Empty) (Φ := Φ)
  let M := traceTypes Empty
  have region := valid J M
    (LetIter.Semantics.Categorical.typingCoherent_ofType (ν := Empty) (fun _ : Empty => Nat) model)
    (fun _ _ => ⟨rfl, rfl⟩)
  have compiled := (Endpoint.denote_eq_iff_proof J M p q).mp region
  unfold traceArrow LetIter.Semantics.Categorical.denoteOfType
  rwa [denote_caseIter_proof, denote_caseIter_proof]

theorem Endpoint.valid_of_code_equiv_proof (p q : Endpoint Φ β A) (c d : Code Φ β A)
    (hc : c.toSSA 0 = p.region) (hd : d.toSSA 0 = q.region)
    (eq : Equiv false Γ₀ β c.toLetCase.1 d.toLetCase.1 A) : p.Valid q := by
  intro V C vcat ccat cart sym prem symPrem sumV sumC distV distC iter elgot J freyd central
    M instr regionCoherent exprCoherent shared
  rw [p.denote_code_proof J M c hc, q.denote_code_proof J M d hd]
  have sound := valid_of_equiv c.toLetCase.2 d.toLetCase.2 eq J M exprCoherent shared
    (fun f hf => by cases hf)
  rw [denote_caseIter_proof, denote_caseIter_proof] at sound
  rw [sound]

theorem Endpoint.valid_iff_compiled_proof (input : StructuralContext β) (p q : Endpoint Φ β A) :
    p.Valid q ↔ Equiv false Γ₀ β p.compile.1 q.compile.1 A :=
  ⟨fun h => (LetCase.Structural.Finite.equiv_iff_traceArrow_eq input p.compile.2 q.compile.2).mpr (trace_of_valid h),
    p.valid_of_code_equiv_proof q p.code q.code p.code_exact q.code_exact⟩

end Finite

end Silmaril.Isotope.LambdaSSA.Acyclic.Native
