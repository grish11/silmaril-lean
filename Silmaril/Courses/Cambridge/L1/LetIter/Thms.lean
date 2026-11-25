module

public import Silmaril.Courses.Cambridge.L1.LetIter.Lowering
public import Silmaril.Courses.Cambridge.L1.EffectfulDenotational.Institution

@[expose] public section

namespace Silmaril.Courses.Cambridge.L1.LetIter

open Silmaril.Elgot Silmaril.Semantics.Operational
open Silmaril.Isotope (BoundCtx)
open Silmaril.Isotope.LetIter.ProofRelevant
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (BoundDen TyDen TypeModel)
open EffectfulDenotational (Computation)

-- The typed instruction and environment types are definitionally the L1 types.
set_option backward.isDefEq.respectTransparency false

/-- Interpret a typed return in the original L1 value syntax. The bind
preserves finite errors, store effects, and partiality. -/
def observe (T : L1.Ty) (m : Computation (TyDen (lowerTy T))) : Computation Expr :=
  m >>= fun v => pure (value T v)

private theorem value_boolTag (b : Bool) : value .bool (boolTag b) = .bool b := by
  cases b <;> rfl

private theorem coprod_apply {A B : TargetTy} (x : interp A ⊕ interp B) :
    TypeModel.coprodEquiv A B x = x := rfl

private theorem coprod_symm_apply {A B : TargetTy} (x : interp A ⊕ interp B) :
    (TypeModel.coprodEquiv A B).symm x = x := rfl

private theorem unit_symm_apply : (TypeModel.unitEquiv (τ := TargetTy)).symm () = () := rfl

private theorem read_agrees (loc : Loc) :
    observe .int (instrDenote (.read loc) ()) = EffectfulDenotational.read loc := by
  apply ExceptT.ext
  apply StateT.ext
  intro s
  change EffectfulDenotational.run (observe .int (instrDenote (.read loc) ())) s =
    EffectfulDenotational.run (EffectfulDenotational.read loc) s
  cases lookup : s.lookup loc <;>
    simp only [observe, instrDenote, EffectfulDenotational.run_bind,
      EffectfulDenotational.run_read, Part.bind_some, lookup, value, EffectfulDenotational.run_pure]

private theorem write_agrees (loc : Loc) (n : Int) :
    observe .unit (instrDenote (.write loc) n) = EffectfulDenotational.write loc n := by
  apply ExceptT.ext
  apply StateT.ext
  intro s
  change EffectfulDenotational.run (observe .unit (instrDenote (.write loc) n)) s =
    EffectfulDenotational.run (EffectfulDenotational.write loc n) s
  cases update : s.update loc n <;>
    simp only [observe, instrDenote, EffectfulDenotational.run_bind,
      EffectfulDenotational.run_write, Part.bind_some, update, value, EffectfulDenotational.run_pure]

/-- The typed lowering commutes with direct monadic evaluation under any
target bound environment. The original store is threaded by the same monad. -/
theorem evalLower_agrees {Γ : TypeEnv} {e : Expr} {T : L1.Ty} {n : Nat}
    {β : BoundCtx TargetTy n} (typed : L1.HasType Γ e T) (ρ : BoundDen β) :
    observe T (evalLower typed ρ) = EffectfulDenotational.denote e := by
  induction typed generalizing n with
  | int z =>
      change observe .int (pure () >>= instrDenote (.literal z)) = pure (.int z)
      simp only [pure_bind, observe, instrDenote, value]
  | bool b =>
      cases b <;>
        simp only [evalLower, lower, Semantics.denote, unit_symm_apply, coprod_symm_apply,
          EffectfulDenotational.denote, observe, pure_bind, value]
  | skip =>
      change observe .unit (pure ()) = pure .skip
      simp only [observe, pure_bind, value]
  | @deref loc present =>
      change observe .int (pure () >>= instrDenote (.read loc)) = EffectfulDenotational.read loc
      rw [pure_bind, read_agrees]
  | @assign loc e present rhs ih =>
      change observe .unit (evalLower rhs ρ >>= instrDenote (.write loc)) =
        EffectfulDenotational.denote e >>= EffectfulDenotational.assign loc
      rw [← ih ρ]
      simp only [observe, bind_assoc, pure_bind, value, EffectfulDenotational.assign]
      exact bind_congr (write_agrees loc)
  | @add l r left right ihLeft ihRight =>
      change observe .int ((evalLower left ρ >>= fun a =>
        evalLower right ρ >>= fun b => pure (a, b)) >>= instrDenote .add) =
          EffectfulDenotational.denote l >>= fun a =>
            EffectfulDenotational.denote r >>= EffectfulDenotational.binary .add a
      rw [← ihLeft ρ, ← ihRight ρ]
      simp only [observe, bind_assoc, pure_bind, instrDenote, value, EffectfulDenotational.binary]
      rfl
  | @ge l r left right ihLeft ihRight =>
      change observe .bool ((evalLower left ρ >>= fun a =>
        evalLower right ρ >>= fun b => pure (a, b)) >>= instrDenote .ge) =
          EffectfulDenotational.denote l >>= fun a =>
            EffectfulDenotational.denote r >>= EffectfulDenotational.binary .ge a
      rw [← ihLeft ρ, ← ihRight ρ]
      simp only [observe, bind_assoc, pure_bind, value, EffectfulDenotational.binary]
      apply bind_congr
      intro a
      apply bind_congr
      intro b
      let x : Int := a
      let y : Int := b
      change (pure (compare x y) >>= fun bit => pure (value .bool bit)) =
        pure (.bool (x ≥ y))
      simp only [pure_bind, compare, value_boolTag]
  | @seq l r T left right ihLeft ihRight =>
      change observe T (evalLower left ρ >>= fun u =>
        evalLower (β := .snoc β unitTy) right (ρ, u)) =
        EffectfulDenotational.denote l >>=
          EffectfulDenotational.afterSkip (EffectfulDenotational.denote r)
      rw [← ihLeft ρ]
      simp only [observe, bind_assoc, pure_bind, value, EffectfulDenotational.afterSkip]
      apply bind_congr
      intro u
      exact ihRight (β := .snoc β unitTy) (ρ, u)
  | @cond test yes no T guard left right ihGuard ihLeft ihRight =>
      simp only [evalLower, lower, Semantics.denote, coprod_apply, EffectfulDenotational.denote]
      have guardAgreement := ihGuard ρ
      unfold evalLower at guardAgreement
      rw [← guardAgreement]
      simp only [observe, bind_assoc, pure_bind]
      apply bind_congr
      intro bit
      cases bit with
      | inl u => exact ihLeft (β := .snoc β unitTy) (ρ, u)
      | inr u => exact ihRight (β := .snoc β unitTy) (ρ, u)
  | @loop test body guard command ihGuard ihCommand =>
      let f : Unit → Computation (Unit ⊕ Unit) := fun u =>
        evalLower (β := .snoc β unitTy) guard (ρ, u) >>= fun bit => match bit with
        | .inl b => evalLower (β := .snoc (.snoc β unitTy) unitTy) command ((ρ, u), b) >>=
            fun _ => pure (.inr ())
        | .inr _ => pure (.inl ())
      have nativeLoop : evalLower (.loop guard command) ρ = iter f () := by
        simp only [evalLower, lower, Semantics.denote, unit_symm_apply, coprod_apply,
          coprod_symm_apply, pure_bind]
        apply congrArg (fun step => iter step ())
        funext u
        simp only [bind_assoc]
        apply bind_congr
        intro bit
        cases bit with
        | inl b => simp only [bind_assoc, pure_bind, evalLower]
        | inr _ => simp only [pure_bind]
      have mapExit := congrFun (LawfulElgotMonad.naturality f (fun _ => pure Expr.skip)) ()
      change observe .unit (iter f ()) =
        iter (mapReturn f (fun _ => pure Expr.skip)) () at mapExit
      rw [nativeLoop]
      refine mapExit.trans ?_
      change iter (mapReturn f (fun _ => pure Expr.skip)) () =
        iter (EffectfulDenotational.whileBody
          (EffectfulDenotational.denote test) (EffectfulDenotational.denote body)) ()
      apply congrArg (fun step => iter step ())
      funext u
      cases u
      simp only [mapReturn, f, EffectfulDenotational.whileBody, bind_assoc]
      rw [← ihGuard (β := .snoc β unitTy) (ρ, ())]
      simp only [observe, bind_assoc, pure_bind]
      apply bind_congr
      intro bit
      cases bit with
      | inl b =>
          rw [← ihCommand (β := .snoc (.snoc β unitTy) unitTy) ((ρ, ()), b)]
          simp only [observe, bind_assoc, pure_bind, value, EffectfulDenotational.branch,
            EffectfulDenotational.afterSkip]
          exact bind_congr (fun _ => rfl)
      | inr _ =>
          simp only [pure_bind, EffectfulDenotational.branch, value]
          rfl

/-- The existing categorical interpretation of the closed translated term. -/
noncomputable def arrow {Γ : TypeEnv} {e : Expr} {T : L1.Ty} (typed : L1.HasType Γ e T) :=
  Semantics.Categorical.denoteOfType (ε := Bool) (m := Computation) (lower e T typed .nil).2

/-- Evaluate the Kleisli arrow in the empty environment and decode its return. -/
noncomputable def evaluate {Γ : TypeEnv} {e : Expr} {T : L1.Ty}
    (typed : L1.HasType Γ e T) : Computation Expr :=
  observe T ((arrow typed).of (PUnit.unit, PUnit.unit))

/-- The categorical and source routes agree as complete L1 computations. -/
theorem evaluate_agrees {Γ : TypeEnv} {e : Expr} {T : L1.Ty} (typed : L1.HasType Γ e T) :
    evaluate typed = EffectfulDenotational.denote e := by
  have agrees := Semantics.categorical_denote_eq (m := Computation) (ε := Bool)
    (lower e T typed .nil).2 PUnit.unit PUnit.unit
  exact (congrArg (observe T) agrees).trans (evalLower_agrees (β := .nil) typed PUnit.unit)

/-- Categorical evaluation observes the same finite returns as the existing
L1 operational institution, including the entire final store. -/
theorem return_iff {Γ : TypeEnv} {e : Expr} {T : L1.Ty} (typed : L1.HasType Γ e T)
    (s : Store) (target : Config) :
    (.ok target.expr, target.store) ∈ EffectfulDenotational.run (evaluate typed) s ↔
      OperationalInstitution.semantics.May ⟨e, s⟩ (.returned target) := by
  rw [evaluate_agrees]
  exact EffectfulDenotational.Institution.sat_iff ⟨e, s⟩ target

/-- A categorical finite error records the final store of a stuck L1 run. -/
theorem error_iff {Γ : TypeEnv} {e : Expr} {T : L1.Ty} (typed : L1.HasType Γ e T)
    (s t : Store) :
    (.error (), t) ∈ EffectfulDenotational.run (evaluate typed) s ↔
      ∃ out, Steps ⟨e, s⟩ ⟨out, t⟩ ∧ Stuck ⟨out, t⟩ := by
  rw [evaluate_agrees]
  exact EffectfulDenotational.error_iff (source := ⟨e, s⟩)

/-- An undefined categorical result corresponds to an infinite L1 reduction. -/
theorem diverges_iff {Γ : TypeEnv} {e : Expr} {T : L1.Ty} (typed : L1.HasType Γ e T)
    (s : Store) :
    ¬ (EffectfulDenotational.run (evaluate typed) s).Dom ↔ InfiniteTrace Step ⟨e, s⟩ := by
  rw [evaluate_agrees]
  exact (EffectfulDenotational.diverges_iff (source := ⟨e, s⟩)).symm

end Silmaril.Courses.Cambridge.L1.LetIter
