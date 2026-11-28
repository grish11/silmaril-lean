module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Defs
public import Silmaril.Semantics.ITree.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Packing
import Silmaril.SSA.Isotope.LetIter.Categorical.Kleisli.Thms
import Silmaril.Raw.SSA.Isotope.Morphism.CaseIter.Monadic

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled

open Silmaril.Elgot Silmaril.Elgot.ITree
open Region (packedExitType)
open Reverse (CheckedTable operandSetoid)
open Isotope.Semantics (BoundEnv InstructionModel)
open LetCase.LocallyNameless (Derivation Equiv)
open LetCase.Structural.Finite (Context StructuralContext)
open LetCase.Structural.Reply (Γ₀)
open LetCase (HandledTrace.Program)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

universe e

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ] {d : Nat} {β : Context d}
  {I J K : LCtx (Ty Empty)} {F : Empty → Type (e + 1)} {Events : Type e → Type e}
  {M : InstructionModel (Ty.denote F) Φ (Tree Events)}

local notation "⟪" d "⟫" => Derivation.denote (Ty.denote F) M d (fun x => Empty.elim x)

/-- No primitive of the finite structural signature is declared pure, so
the native equations hold in every lawful Elgot monad model. -/
theorem denote_eq_of_equiv_proof {n : Nat} {γ : Context n} {a b : LetCase.LocallyNameless.Tm Empty Φ n} {A : Ty Empty}
    (h : Equiv false Γ₀ γ a b A) (da : Derivation Φ Γ₀ γ a A) (db : Derivation Φ Γ₀ γ b A)
    (ρ : BoundEnv (Ty.denote F) γ) : ⟪da⟫ ρ = ⟪db⟫ ρ := by
  have sound := LetIter.Semantics.Categorical.denote_eq_of_abortEquiv_nil (ε := Bool) F M
    (fun f pure => by cases pure) (.equiv (Morphism.CaseIter.embed_equiv h))
    (Morphism.CaseIter.derivation da) (Morphism.CaseIter.derivation db) ρ
  simpa only [Morphism.CaseIter.denote_derivation] using sound

theorem denote_emit_seq_proof (input : StructuralContext β)
    (p : CheckedTable Φ (β.snoc (packedExitType I)) J) (q : CheckedTable Φ (β.snoc (packedExitType J)) K)
    (ρ : BoundEnv (Ty.denote F) β) (x : Ty.denote F (packedExitType I)) :
    ⟪(seq p q).toLetCase.2⟫ (ρ.snoc x) =
      (⟪p.toLetCase.2⟫ (ρ.snoc x) >>= fun y => ⟪q.toLetCase.2⟫ (ρ.snoc y)) :=
  (denote_eq_of_equiv_proof (emit_seq_equiv input p q) _ (Case.seq p.toLetCase q.toLetCase).2 _).trans
    (denote_seq_proof p.toLetCase.2 q.toLetCase.2 ρ x)

theorem denote_emit_identity_proof (h : I ≠ []) (ρ : BoundEnv (Ty.denote F) β)
    (x : Ty.denote F (packedExitType I)) :
    ⟪(identity (Φ := Φ) (β := β) h).toLetCase.2⟫ (ρ.snoc x) = pure x :=
  denote_eq_of_equiv_proof (Link.identity_equiv h (identity h).entry) (identity h).toLetCase.2
    (⟨.bv 0, .bv⟩ : Operand Φ (β.snoc (packedExitType I)) (packedExitType I)).2 (ρ.snoc x)

theorem run_pack_congr_proof {a b : Operand Φ (β.snoc (packedExitType I)) (packedExitType J)}
    (h : (operandSetoid Φ (β.snoc (packedExitType I)) J).r a b)
    (w : Ty.denote F (wrap β (packedExitType I))) : (pack β a).run M w = (pack β b).run M w := by
  obtain ⟨ρ, x, rfl⟩ := wrapValue_surjective_proof β w
  rw [run_pack_proof, run_pack_proof]
  exact congrArg (· >>= _) (denote_eq_of_equiv_proof h a.2 b.2 _)

theorem run_pack_identity_proof (w : Ty.denote F (wrap β (packedExitType I))) :
    (pack β (⟨.bv 0, .bv⟩ : Operand Φ (β.snoc (packedExitType I)) (packedExitType I))).run M w = pure w := by
  obtain ⟨ρ, x, rfl⟩ := wrapValue_surjective_proof β w
  rw [run_pack_proof]
  exact pure_bind _ _

theorem run_pack_seq_proof (a : Operand Φ (β.snoc (packedExitType I)) (packedExitType J))
    (b : Operand Φ (β.snoc (packedExitType J)) (packedExitType K))
    (w : Ty.denote F (wrap β (packedExitType I))) :
    (pack β (Case.seq a b)).run M w = ((pack β a).run M w >>= (pack β b).run M) := by
  obtain ⟨ρ, x, rfl⟩ := wrapValue_surjective_proof β w
  rw [run_pack_proof, run_pack_proof, bind_assoc]
  refine (congrArg (· >>= _) (denote_seq_proof a.2 b.2 ρ x)).trans ?_
  rw [bind_assoc]
  exact bind_congr fun y => by rw [pure_bind, run_pack_proof]

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled
