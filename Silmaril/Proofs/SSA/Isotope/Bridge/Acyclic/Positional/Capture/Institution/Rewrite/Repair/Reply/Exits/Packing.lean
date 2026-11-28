module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Exits.Defs

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Exits

open Kleisli (value)
open Isotope.Semantics (BoundEnv InstructionModel)
open Isotope.LetCase.LocallyNameless (Derivation)
open LambdaSSA (At Ren)
open LambdaSSA.Acyclic (Operand FiniteExit Code)
open LambdaSSA.Acyclic.Positional.Capture (Scope)
open LambdaSSA.Region (packedExitType)

set_option backward.isDefEq.respectTransparency false

private def unpack : (L : List Sorts) → value (packedExitType L) → Exit L
  | [], x => x.elim
  | _ :: _, .inl a => ⟨0, a⟩
  | _ :: L, .inr b =>
    let x := unpack L b
    ⟨x.1.succ, x.2⟩

private theorem unpack_packed (L : List Sorts) (a : Exit L) : unpack L a.packed = a := by
  obtain ⟨i, x⟩ := a
  induction L with
  | nil => exact i.elim0
  | cons A L ih =>
    refine Fin.cases (motive := fun i => ∀ x : value ((A :: L).get i),
      unpack (A :: L) (Exit.packed ⟨i, x⟩) = ⟨i, x⟩) (fun x => rfl) (fun i x => ?_) i x
    change (let y := unpack L (Exit.packed (⟨i, x⟩ : Exit L)); (⟨y.1.succ, y.2⟩ : Exit (A :: L))) = _
    rw [ih i x]

theorem packed_injective_proof (L : List Sorts) : Function.Injective (@Exit.packed L) := by
  intro a b h
  exact (unpack_packed L a).symm.trans ((congrArg (unpack L) h).trans (unpack_packed L b))

private theorem literal_run {n : Nat} {β : BoundCtx Sorts n} (ρ : BoundEnv value β)
    (A : Sorts) (x : value A) :
    Kleisli.run model (literal β A x).2 ρ = pure x := by
  induction A with
  | base a => exact a.elim
  | empty => exact x.elim
  | unit => cases x; rfl
  | product A B ihA ihB =>
    obtain ⟨a, b⟩ := x
    simp only [literal, Kleisli.run, Derivation.denote] at ihA ihB ⊢
    rw [ihA, pure_bind, ihB, pure_bind]
    rfl
  | coprod A B ihA ihB =>
    cases x <;> simp only [literal, Kleisli.run, Derivation.denote] at ihA ihB ⊢
    · rw [ihA, pure_bind]
      rfl
    · rw [ihB, pure_bind]
      rfl

variable {P : InstrSig Sorts Bool} {m : Type → Type} [Monad m] [LawfulMonad m]

theorem tag_run_proof (M : InstructionModel value P.Instr m)
    {n : Nat} {β : BoundCtx Sorts n} (ρ : BoundEnv value β)
    (L : List Sorts) (i : Nat) {A : Sorts} (h : At L i A) (x : value A)
    (a : Operand P.Instr β A) (ha : Kleisli.run M a.2 ρ = pure x) :
    Kleisli.run M (FiniteExit.tag L i h a).2 ρ = pure (packAt L i h x) := by
  induction L generalizing i with
  | nil => cases i <;> contradiction
  | cons B L ih =>
    cases i with
    | zero =>
      have e : B = A := Option.some.inj h
      cases e
      simp only [FiniteExit.tag, packAt, Kleisli.run, Derivation.denote] at ha ⊢
      rw [ha, pure_bind]
      rfl
    | succ i =>
      have smaller := ih i h
      simp only [FiniteExit.tag, packAt, Kleisli.run, Derivation.denote] at smaller ⊢
      rw [smaller, pure_bind]
      rfl

theorem exitOperand_run_proof {L : List Sorts} {n : Nat} {β : BoundCtx Sorts n}
    (ρ : BoundEnv value β) (x : Exit L) :
    Kleisli.run model (exitOperand L β x).2 ρ = pure x.packed :=
  tag_run_proof model ρ L _ _ _ _ (literal_run ρ _ _)

theorem router_run_proof (M : InstructionModel value P.Instr m)
    {K : List Sorts} {j : Nat} {D : Sorts} (fallback : At K j D)
    (L : List Sorts) {f : Nat → Nat} (ren : Ren L K f)
    {k n : Nat} {γ : BoundCtx Sorts k} {β : BoundCtx Sorts n}
    (s : Scope γ β) (ρ : BoundEnv value β)
    (i : Nat) {A : Sorts} (h : At L i A) (x : value A) :
    Kleisli.run M ((router fallback L ren).render s).encode.toLetCase.2
      (ρ.snoc (A := packedExitType L) (packAt L i h x)) = pure (packAt K (f i) (ren h) x) := by
  induction L generalizing f n i with
  | nil => cases i <;> contradiction
  | cons H L ih =>
    let T := packedExitType (H :: L)
    let next := router (Φ := P.Instr) (β := γ)
      fallback L (ρ := fun i => f (i + 1)) (fun _ _ h => ren h)
    let left : Operand P.Instr ((β.snoc T).snoc H) (packedExitType K) :=
      FiniteExit.tag K (f 0) (ren (rfl : At (H :: L) 0 H)) ⟨.bv 0, .bv⟩
    let right := (next.render (.skip s T)).encode.toLetCase
    change Kleisli.run M (.case (.bv (ι := 0)) left.2 right.2)
      (ρ.snoc (A := T) (packAt (H :: L) i h x)) = _
    cases i with
    | zero =>
      have e : H = A := Option.some.inj h
      cases e
      let input := ρ.snoc (A := T) (Sum.inl x)
      simp only [Kleisli.run, Derivation.denote, pure_bind]
      change Kleisli.run M left.2 (input.snoc (A := A) x) = _
      let packet : Operand P.Instr ((β.snoc T).snoc A) A := ⟨.bv 0, .bv⟩
      have purePacket : Kleisli.run M packet.2 (input.snoc (A := A) x) = pure x := rfl
      exact tag_run_proof M _ _ _ _ x packet purePacket
    | succ i =>
      let input := ρ.snoc (A := T) (Sum.inr (packAt L i h x))
      simp only [Kleisli.run, Derivation.denote, pure_bind]
      change Kleisli.run M right.2 (input.snoc (A := packedExitType L) (packAt L i h x)) = _
      exact ih (f := fun index => f (index + 1)) _ (.skip s T) input i h

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Exits
