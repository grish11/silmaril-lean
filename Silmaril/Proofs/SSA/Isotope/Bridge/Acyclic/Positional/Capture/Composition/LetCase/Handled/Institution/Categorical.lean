module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Defs
public import Silmaril.SSA.Isotope.LetIter.Categorical.Kleisli.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Soundness.Thms
import Silmaril.Raw.SSA.Isotope.Morphism.CaseIter.Monadic
import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Native.Comparison.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Categorical.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Thms

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open CategoryTheory Silmaril.Elgot
open Isotope.Semantics (BoundEnv)
open LetIter.Semantics.Categorical (boundEnv boundObj ctxObj freeEnv denoteOfType denoteOfType_eq ofTypeModel
  ofInstructionModel typingCoherent_ofType denote_equiv_of_coherent_shared_tensor)

universe u₁ u₂ v₁ v₂ w

section Sound

variable {τ Φ ε : Type} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] {pe : ε}
  {n : Nat} {β : BoundCtx τ n} {a b : LetIter.LocallyNameless.Tm Empty Φ n} {A : τ}

/-- Native equations hold in the validity class at every universe. -/
theorem validAt_of_equiv_proof (h : LetIter.LocallyNameless.Equiv pe (Ctx.nil : Ctx Empty τ) β a b A)
    (da : LetIter.LocallyNameless.Derivation Φ (Ctx.nil : Ctx Empty τ) β a A)
    (db : LetIter.LocallyNameless.Derivation Φ (Ctx.nil : Ctx Empty τ) β b A) :
    ValidAt.{u₁, u₂, v₁, v₂} pe da db := by
  intro V C vcat ccat cart sym prem symPrem sumV sumC distV distC iter elgot J freyd central
    M instr coherent shared pureInstr
  exact denote_equiv_of_coherent_shared_tensor J M coherent shared pureInstr h da db

end Sound

section Kleisli

variable {α : Type} [DecidableEq α] (F : α → Type w)
  {m : Type w → Type w} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  {Φ ε : Type} [HasTy Φ (Ty α)] [HasEff Φ ε] [Bot ε]
  (M : Isotope.Semantics.InstructionModel (Ty.denote F) Φ m)

omit [DecidableEq α] in
private theorem boundEnv_surjective {n : Nat} (β : BoundCtx (Ty α) n) :
    Function.Surjective (boundEnv (Ty.denote F) (β := β)) := by
  induction β with
  | nil =>
    intro ρ
    exact ⟨PUnit.unit, funext (fun i => i.elim0)⟩
  | snoc β A ih =>
    intro ρ
    obtain ⟨x, hx⟩ := ih (fun i => ρ i.succ)
    refine ⟨(x, ρ 0), ?_⟩
    refine (LetIter.Semantics.Categorical.boundEnv_snoc (Ty.denote F) (β := β) (A := A) x (ρ 0)).trans ?_
    refine (congrArg (fun env => BoundEnv.snoc (A := A) env (ρ 0)) hx).trans ?_
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

omit [DecidableEq α] in
/-- Equal Kleisli arrows are equal monadic denotations at every bound
environment, for a monad on any universe. -/
theorem denote_eq_of_arrow_eq_proof {n : Nat} {β : BoundCtx (Ty α) n}
    {a b : LetIter.LocallyNameless.Tm Empty Φ n} {A : Ty α}
    (da : LetIter.LocallyNameless.Derivation Φ (Ctx.nil : Ctx Empty (Ty α)) β a A)
    (db : LetIter.LocallyNameless.Derivation Φ (Ctx.nil : Ctx Empty (Ty α)) β b A)
    (same : denoteOfType (Ty.denote F) M da = denoteOfType (Ty.denote F) M db)
    (ρ : BoundEnv (Ty.denote F) β) :
    da.denote (Ty.denote F) M (fun x => x.elim) ρ = db.denote (Ty.denote F) M (fun x => x.elim) ρ := by
  obtain ⟨packed, rfl⟩ := boundEnv_surjective F β ρ
  let c : ctxObj (ofTypeModel (Ty.denote F)) (Ctx.nil : Ctx Empty (Ty α)) := PUnit.unit
  have applied := congrArg (fun f => f.of (c, packed)) same
  have pointwise := (denoteOfType_eq _ _ da c packed).symm.trans (applied.trans (denoteOfType_eq _ _ db c packed))
  have free : freeEnv (Ty.denote F) (Γ := (Ctx.nil : Ctx Empty (Ty α))) c = fun x => x.elim :=
    funext fun x => x.elim
  change da.denote (Ty.denote F) M (freeEnv (Ty.denote F) c) (boundEnv (Ty.denote F) packed) =
    db.denote (Ty.denote F) M (freeEnv (Ty.denote F) c) (boundEnv (Ty.denote F) packed) at pointwise
  rwa [free] at pointwise

/-- The Kleisli category of a lawful Elgot monad on any universe is in the
validity class one universe up, so validity there gives equal Kleisli arrows. -/
theorem arrow_eq_of_validAt_proof (pureM : Isotope.Semantics.InstructionModel.RespectsPure (ε := ε) M)
    {n : Nat} {β : BoundCtx (Ty α) n} {a b : LetIter.LocallyNameless.Tm Empty Φ n} {A : Ty α}
    (da : LetIter.LocallyNameless.Derivation Φ (Ctx.nil : Ctx Empty (Ty α)) β a A)
    (db : LetIter.LocallyNameless.Derivation Φ (Ctx.nil : Ctx Empty (Ty α)) β b A)
    (valid : ValidAt.{w + 1, w + 1, w, w} (⊥ : ε) da db) :
    denoteOfType (Ty.denote F) M da = denoteOfType (Ty.denote F) M db := by
  let inst := ofInstructionModel (Ty.denote F) M
  refine valid (Kleisli.Adjunction.toKleisli (ofTypeMonad m)) (ofTypeModel (Ty.denote F))
    (typingCoherent_ofType (ν := Empty) F M) (fun _ _ => ⟨rfl, rfl⟩) fun f hf => ?_
  obtain ⟨g, hg⟩ := pureM f hf
  refine ⟨TypeCat.ofHom g, ?_⟩
  apply Kleisli.hom_ext
  apply ConcreteCategory.coe_ext
  funext x
  exact hg x

end Kleisli

section Structural

open Silmaril.Elgot.ITree
open Silmaril.Isotope.Institution.Acyclic (CoherentRegionModel)
open Region (packedExitType)
open Reverse (CheckedTable)
open LambdaSSA.Semantics.Categorical (denoteRegion)
open LetCase.LocallyNameless (Derivation Equiv)
open LetCase.Structural.Finite (Context StructuralContext equiv_iff_traceArrow_eq_snoc)
open LetCase.Structural.Reply (Γ₀ traceArrow traceArrow_of_valid valid_of_equiv)
open LetSeq.StraightLine.Structural.Categorical (traceJ traceTypes traceInstructions)
open LetIter.PaperExpression.Source.FreeTree.Response (Structured.Lifted)
open Free
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ]

theorem caseValidAt_of_equiv_proof {n : Nat} {γ : Context n} {B : Ty Empty} {a b : Operand Φ γ B}
    (h : Equiv false Γ₀ γ a.1 b.1 B) : CaseValidAt.{u₁, u₂, v₁, v₂} a b :=
  validAt_of_equiv_proof (Morphism.CaseIter.embed_equiv h) _ _

/-- Validity at the universes of the tree Kleisli category gives equal
free trees in every environment. -/
theorem tree_eq_of_caseValidAt_proof {n : Nat} {γ : Context n} {B : Ty Empty} (a b : Operand Φ γ B)
    (valid : CaseValidAt.{2, 2, 1, 1} a b) (ρ : BoundEnv Val γ) :
    a.2.denote Val (model Φ) (fun x => x.elim) ρ = b.2.denote Val (model Φ) (fun x => x.elim) ρ := by
  have arrows := arrow_eq_of_validAt_proof (ε := Bool) (Structured.Lifted Atoms) (model Φ)
    (fun f pure => Bool.noConfusion pure) _ _ valid
  have pointwise := denote_eq_of_arrow_eq_proof (Structured.Lifted Atoms) (model Φ) _ _ arrows ρ
  simpa only [Morphism.CaseIter.denote_derivation] using pointwise

variable {d : Nat} {β : Context d} {A B : Ty Empty} {I J : LCtx (Ty Empty)}

theorem caseValidAt_tree_iff_equiv_proof (input : StructuralContext β) (a b : Operand Φ (β.snoc A) B) :
    CaseValidAt.{2, 2, 1, 1} a b ↔ Equiv false Γ₀ (β.snoc A) a.1 b.1 B :=
  ⟨fun valid => (treeRefines_iff_equiv input a b).mp fun ρ =>
      tree_eq_of_caseValidAt_proof a b valid ρ ▸ fun _ seen => seen,
    caseValidAt_of_equiv_proof⟩

theorem valid_iff_equiv_proof (input : StructuralContext β) (a b : Operand Φ (β.snoc A) B) :
    LetCase.Structural.Reply.Valid a.2 b.2 ↔ Equiv false Γ₀ (β.snoc A) a.1 b.1 B :=
  ⟨fun valid => (equiv_iff_traceArrow_eq_snoc input a.2 b.2).mpr (traceArrow_of_valid valid),
    valid_of_equiv a.2 b.2⟩

set_option backward.isDefEq.respectTransparency false in
/-- At the ordered trace model, the ordered-exit arrows of two written
graphs agree exactly when their emitted operands are natively equal. -/
theorem ranked_trace_iff_equiv_proof (input : StructuralContext β)
    (p q : CheckedTable Φ (β.snoc (packedExitType I)) J) :
    (let := traceInstructions (α := Empty) (Φ := Φ)
     denoteRegion (traceJ (α := Empty) (Φ := Φ)) (traceTypes Empty) (p.table.toSSA_hasType 0 p.entry) =
       denoteRegion (traceJ (α := Empty) (Φ := Φ)) (traceTypes Empty) (q.table.toSSA_hasType 0 q.entry)) ↔
      Equiv false Γ₀ (β.snoc (packedExitType I)) p.toLetCase.1 q.toLetCase.1 (packedExitType J) := by
  let := traceInstructions (α := Empty) (Φ := Φ)
  let := Native.trace_region_coherent (Φ := Φ)
  let F := traceJ (α := Empty) (Φ := Φ)
  let M := traceTypes Empty
  have ordered (c : CheckedTable Φ (β.snoc (packedExitType I)) J) :
      denoteRegion F M (c.table.toSSA_hasType 0 c.entry) =
        denoteRegion F M (c.table.packedSSA_hasType 0 c.entry) ≫
          F.map (LambdaSSA.Semantics.Categorical.unpackLabelExit M J) := by
    rw [Table.toLetCase_denote F M c.table c.checked 0 c.entry,
      Table.packed_denote F M (fun _ _ => ⟨rfl, rfl⟩) c.table c.checked 0 c.entry]
    simp only [Category.assoc, Functor.map_comp]
  have packed : denoteRegion F M (p.table.toSSA_hasType 0 p.entry) =
      denoteRegion F M (q.table.toSSA_hasType 0 q.entry) ↔
      denoteRegion F M (p.table.packedSSA_hasType 0 p.entry) =
        denoteRegion F M (q.table.packedSSA_hasType 0 q.entry) := by
    rw [ordered p, ordered q]
    constructor
    · intro same
      have out := congrArg (fun f => f ≫ F.map (LambdaSSA.Semantics.Categorical.packLabelExit M J)) same
      simp only [Category.assoc, ← Functor.map_comp,
        LambdaSSA.Semantics.Categorical.unpackLabelExit_packLabelExit] at out
      rw [F.map_id, Category.comp_id, Category.comp_id] at out
      exact out
    · intro same
      rw [same]
  have comparison := Table.packed_denote_iff F M (fun _ _ => ⟨rfl, rfl⟩) p.table q.table p.checked q.checked 0 0 p.entry q.entry
  have finite := equiv_iff_traceArrow_eq_snoc input p.toLetCase.2 q.toLetCase.2
  unfold traceArrow LetIter.Semantics.Categorical.denoteOfType at finite
  rw [Native.denote_caseIter F M, Native.denote_caseIter F M] at finite
  exact packed.trans (comparison.trans finite.symm)

end Structural

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
