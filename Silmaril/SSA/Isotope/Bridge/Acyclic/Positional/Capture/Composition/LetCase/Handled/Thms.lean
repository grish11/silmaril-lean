module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Defs
public import Silmaril.Semantics.ITree.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Packing
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Soundness

/-! # From captured LetCase classes to fixed-policy handled traces

The source homs are native LetCase equation classes with a fixed older
context. The target homs are one-input programs modulo mutual handled-trace
inclusion at one primitive interpretation and one reply policy. The functor
keeps the two equalities apart: it sends an equation class to the trace
class of its packed representative, and it is not claimed to be faithful.

Older captures are carried through each arrow in a product beside the
input. With no older captures the packed program is the operand itself.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled

open CategoryTheory Silmaril.Elgot.ITree
open Region (packedExitType)
open Reverse (CheckedTable operandSetoid)
open Isotope.Semantics (BoundEnv ProductModel UnitModel CoproductModel EmptyModel InstructionModel)
open LetCase.LocallyNameless (Derivation Equiv)
open LetCase.Structural.Finite (Context StructuralContext)
open LetCase.Structural.Reply (Γ₀)
open LetCase (HandledTrace.Program HandledTrace.Arrow)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

universe u v e s

section Packing

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {D : τ → Type (e + 1)} [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
  {Events : Type e → Type e} {M : InstructionModel D Φ (Tree Events)}
  {n : Nat} {β : BoundCtx τ n} {A X Y Z : τ}

local notation "⟪" d "⟫" => Derivation.denote D M d (fun x => Empty.elim x)

/-- The native let runs its receiver on the same older environment, with
the bound result in place of the input. -/
theorem denote_seq {s t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
    (a : Derivation Φ Ctx.nil (β.snoc X) s Y) (b : Derivation Φ Ctx.nil (β.snoc Y) t Z)
    (ρ : BoundEnv D β) (x : D X) :
    ⟪Derivation.let₁ a b.underBinder⟫ (ρ.snoc x) = (⟪a⟫ (ρ.snoc x) >>= fun y => ⟪b⟫ (ρ.snoc y)) :=
  denote_seq_proof a b ρ x

/-- Retaining a slot runs the operand once and pairs its result with the
unchanged slot. -/
theorem denote_keep (a : Operand Φ ((β.snoc A).snoc X) Y) (ρ : BoundEnv D β) (v : D A) (x : D X) :
    ⟪(keep a).2⟫ (ρ.snoc ((ProductModel.productEquiv A X).symm (v, x))) =
      (⟪a.2⟫ ((ρ.snoc v).snoc x) >>= fun y => pure ((ProductModel.productEquiv A Y).symm (v, y))) :=
  denote_keep_proof a ρ v x

/-- The packed program runs the operand in the unpacked older environment
and returns the same environment beside the result. -/
theorem run_pack (β : BoundCtx τ n) (a : Operand Φ (β.snoc X) Y) (ρ : BoundEnv D β) (x : D X) :
    (pack β a).run M (wrapValue β ρ x) = (⟪a.2⟫ (ρ.snoc x) >>= fun y => pure (wrapValue β ρ y)) :=
  run_pack_proof β a ρ x

omit [UnitModel D] [CoproductModel D] [EmptyModel D] in
/-- Every packed input comes from an older environment and an input. -/
theorem wrapValue_surjective (β : BoundCtx τ n) (w : D (wrap β X)) :
    ∃ (ρ : BoundEnv D β) (x : D X), wrapValue β ρ x = w :=
  wrapValue_surjective_proof β w

/-- With no older captures the packed program is the operand. -/
theorem pack_nil (a : Operand Φ (BoundCtx.nil.snoc X) Y) : pack .nil a = a := rfl

end Packing

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ] {d : Nat} {β : Context d}
  {I J K : LCtx (Ty Empty)} {F : Empty → Type (e + 1)} {Events : Type e → Type e}
  {State : Type s} {M : InstructionModel (Ty.denote F) Φ (Tree Events)}

local notation "⟪" d "⟫" => Derivation.denote (Ty.denote F) M d (fun x => Empty.elim x)

/-! ## Exact equations in every older environment

These are equalities of interaction trees. They do not mention a policy. -/

/-- Native equations are sound for the tree semantics in every older
environment. No primitive of the signature is declared pure. -/
theorem denote_eq_of_equiv {n : Nat} {γ : Context n} {a b : LetCase.LocallyNameless.Tm Empty Φ n}
    {A : Ty Empty} (h : Equiv false Γ₀ γ a b A) (da : Derivation Φ Γ₀ γ a A)
    (db : Derivation Φ Γ₀ γ b A) (ρ : BoundEnv (Ty.denote F) γ) : ⟪da⟫ ρ = ⟪db⟫ ρ :=
  denote_eq_of_equiv_proof h da db ρ

/-- The emitted written link runs the two emitted stages in order, with the
same older environment at both. -/
theorem denote_emit_seq (input : StructuralContext β)
    (p : CheckedTable Φ (β.snoc (packedExitType I)) J) (q : CheckedTable Φ (β.snoc (packedExitType J)) K)
    (ρ : BoundEnv (Ty.denote F) β) (x : Ty.denote F (packedExitType I)) :
    ⟪(seq p q).toLetCase.2⟫ (ρ.snoc x) =
      (⟪p.toLetCase.2⟫ (ρ.snoc x) >>= fun y => ⟪q.toLetCase.2⟫ (ρ.snoc y)) :=
  denote_emit_seq_proof input p q ρ x

/-- The emitted written identity returns its input. -/
theorem denote_emit_identity (h : I ≠ []) (ρ : BoundEnv (Ty.denote F) β)
    (x : Ty.denote F (packedExitType I)) :
    ⟪(identity (Φ := Φ) (β := β) h).toLetCase.2⟫ (ρ.snoc x) = pure x :=
  denote_emit_identity_proof h ρ x

/-- Natively equal operands have equal packed runs. -/
theorem run_pack_congr {a b : Operand Φ (β.snoc (packedExitType I)) (packedExitType J)}
    (h : (operandSetoid Φ (β.snoc (packedExitType I)) J).r a b)
    (w : Ty.denote F (wrap β (packedExitType I))) : (pack β a).run M w = (pack β b).run M w :=
  run_pack_congr_proof h w

/-- The packed input variable returns the whole packed input. -/
theorem run_pack_identity (w : Ty.denote F (wrap β (packedExitType I))) :
    (pack β (⟨.bv 0, .bv⟩ : Operand Φ (β.snoc (packedExitType I)) (packedExitType I))).run M w = pure w :=
  run_pack_identity_proof w

/-- Packing the native let is tree bind of the two packed programs. -/
theorem run_pack_seq (a : Operand Φ (β.snoc (packedExitType I)) (packedExitType J))
    (b : Operand Φ (β.snoc (packedExitType J)) (packedExitType K))
    (w : Ty.denote F (wrap β (packedExitType I))) :
    (pack β (Case.seq a b)).run M w = ((pack β a).run M w >>= (pack β b).run M) :=
  run_pack_seq_proof a b w

/-! ## The semantic functors -/

variable (M) (policy : Handler State Events)

/-- Send a native equation class to the handled-trace class of its packed
representative. Objects carry the older captures beside the packed exits. -/
def handledFunctor (input : StructuralContext β) :
    Case.Interface Φ β input ⥤ LetCase.HandledTrace.Interface M policy where
  obj X := ⟨wrap β (packedExitType X.exits)⟩
  map := Quotient.lift (fun a => HandledTrace.Arrow.ofProgram (pack β a))
    (fun _ _ h => Quotient.sound (HandledTrace.Program.equiv_of_run_eq (run_pack_congr h)))
  map_id _ := Quotient.sound (HandledTrace.Program.equiv_of_run_eq run_pack_identity)
  map_comp p q := Quotient.inductionOn₂ p q fun a b =>
    Quotient.sound (HandledTrace.Program.equiv_of_run_eq fun w =>
      (run_pack_seq a b w).trans (HandledTrace.Program.run_seq _ _ w).symm)

/-- On a representative the functor returns the class of the packed operand. -/
@[simp] theorem handledFunctor_map_mk (input : StructuralContext β) {X Y : Case.Interface Φ β input}
    (a : Operand Φ (β.snoc (packedExitType X.exits)) (packedExitType Y.exits)) :
    (handledFunctor M policy input).map (X := X) (Y := Y) (Quotient.mk _ a) =
      HandledTrace.Arrow.ofProgram (pack β a) :=
  rfl

/-- The semantic functor on written ranked graphs: emit, then pack and
take the handled-trace class. -/
def ssaHandledFunctor (input : StructuralContext β) :
    Interface Φ β input ⥤ LetCase.HandledTrace.Interface M policy :=
  emitFunctor input ⋙ handledFunctor M policy input

/-- A written graph goes to the class of its packed emitted operand. -/
@[simp] theorem ssaHandledFunctor_map_mk (input : StructuralContext β) {X Y : Interface Φ β input}
    (p : CheckedTable Φ (β.snoc (packedExitType X.exits)) Y.exits) :
    (ssaHandledFunctor M policy input).map (X := X) (Y := Y) (Quotient.mk _ p) =
      HandledTrace.Arrow.ofProgram (pack β p.toLetCase) :=
  congrArg ((handledFunctor M policy input).map (X := (emitFunctor input).obj X)
    (Y := (emitFunctor input).obj Y)) (emitClass_mk input p)

/-- Reading a native class back to a written graph and taking its written
semantics gives the native semantics. With the definition of the written
functor, both triangles over the emitter and the readback commute. -/
theorem readbackFunctor_comp_ssaHandledFunctor (input : StructuralContext β) :
    readbackFunctor input ⋙ ssaHandledFunctor M policy input = handledFunctor M policy input := by
  rw [ssaHandledFunctor, ← Functor.assoc, readbackFunctor_comp_emitFunctor, Functor.id_comp]

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled
