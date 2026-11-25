module

public import Silmaril.Semantics.Calco2019.Maybe.Types.Defs

@[expose] public section

universe u

namespace Silmaril.Calco2019.Maybe.Types.Proofs

open CategoryTheory CategoryTheory.Limits

theorem lawful : LawfulMonad Model.{u} := LawfulMonad.mk'
  (id_map := fun x => by cases x <;> rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x _ _ => by cases x <;> rfl)

private theorem observe_inl {X : Type u} (x : X) :
    (observe X).symm (Sum.inl x) = Part.some x := rfl

private theorem observe_inr {X : Type u} (p : PUnit.{u + 1}) :
    (observe X).symm (Sum.inr p) = Part.none := rfl

private noncomputable def embedding : Elgot.Embedding Model.{u} Part where
  map := (observe _).symm
  injective := fun h => (observe _).symm.injective h
  map_pure x := observe_inl x
  map_bind x f := by
    cases x with
    | inl x =>
      change (observe _).symm (f x) = (observe _).symm (Sum.inl x) >>= _
      rw [observe_inl]
      exact (Part.bind_some _ _).symm
    | inr p =>
      change (observe _).symm (Sum.inr p) = (observe _).symm (Sum.inr p) >>= _
      rw [observe_inr, observe_inr]
      exact (Part.bind_none _).symm
  map_iter f x := (observe _).symm_apply_apply _

theorem lawfulElgot : @Elgot.LawfulElgotMonad Model.{u} _ lawful _ := by
  let _ : LawfulMonad Model.{u} := lawful
  exact embedding.lawful

theorem monad_eq :
    @ofTypeMonad Model.{u} _ lawful = monad typeCoproducts PUnit.{u + 1} := by
  rfl


section Decomposition

variable {X Y : Type u} (f : X ⟶ typeCoproducts.sum Y X)

private theorem exitAt_unique {x : X} {n m : ℕ}
    (hn : (exitAt f n x).isSome) (hm : (exitAt f m x).isSome) : n = m := by
  induction n generalizing m x with
  | zero =>
    cases hf : f x with
    | inl y => cases m <;> simp_all [exitAt]
    | inr x' => simp [exitAt, hf] at hn
  | succ n ih =>
    cases hf : f x with
    | inl y => simp [exitAt, hf] at hn
    | inr x' =>
      cases m with
      | zero => simp [exitAt, hf] at hm
      | succ m =>
        exact congrArg Nat.succ (ih (by simpa [exitAt, hf] using hn) (by simpa [exitAt, hf] using hm))

private abbrev Branch (i : Option ℕ) :=
  i.elim { x : X // ∀ n, (exitAt f n x).isSome = false }
    (fun n => { x : X // (exitAt f n x).isSome = true })

private def state (i : Option ℕ) : Branch f i → X :=
  match i with
  | none => Subtype.val
  | some _ => Subtype.val

private theorem state_injective (i : Option ℕ) : Function.Injective (state f i) := by
  cases i <;> exact Subtype.val_injective

private theorem branch_unique {i j : Option ℕ} (x : Branch f i) (y : Branch f j)
    (h : state f i x = state f j y) : i = j := by
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some n =>
      have h' : x.val = y.val := h
      exact False.elim (Bool.false_ne_true ((x.prop n).symm.trans (h' ▸ y.prop)))
  | some n =>
    cases j with
    | none =>
      have h' : x.val = y.val := h
      have e : (exitAt f n x.val).isSome = false := h' ▸ y.prop n
      exact False.elim (Bool.false_ne_true (e.symm.trans x.prop))
    | some m =>
      have h' : x.val = y.val := h
      exact congrArg some (exitAt_unique f x.prop (h' ▸ y.prop))

private def cover : Cofan (Branch f) := Cofan.mk X (fun i => ↾state f i)

private theorem cover_isColimit : Nonempty (IsColimit (cover f)) := by
  classical
  apply (Cofan.nonempty_isColimit_iff_bijective_fromSigma _).mpr
  constructor
  · rintro ⟨i, x⟩ ⟨j, y⟩ (h : state f i x = state f j y)
    cases branch_unique f x y h
    exact congrArg (Sigma.mk i) (state_injective f i h)
  · intro x
    by_cases h : ∃ n, (exitAt f n x).isSome
    · obtain ⟨n, hn⟩ := h
      exact ⟨⟨some n, ⟨x, hn⟩⟩, rfl⟩
    · have hx (n : ℕ) : (exitAt f n x).isSome = false := by
        simpa using (fun hi => h ⟨n, hi⟩ : ¬ (exitAt f n x).isSome)
      exact ⟨⟨none, ⟨x, hx⟩⟩, rfl⟩

private def next (n : ℕ) : Branch f (some (n + 1)) → Branch f (some n) := fun x =>
  match hx : f x.val with
  | .inl _ => False.elim (by have e := x.prop; simp [exitAt, hx] at e)
  | .inr x' => ⟨x', by simpa [exitAt, hx] using x.prop⟩

private def stay : Branch f none → Branch f none := fun x =>
  match hx : f x.val with
  | .inl _ => False.elim (by have e := x.prop 0; simp [exitAt, hx] at e)
  | .inr x' => ⟨x', fun n => by simpa [exitAt, hx] using x.prop (n + 1)⟩

theorem decompose : Nonempty (LoopDecomposition f) := by
  obtain ⟨colimit⟩ := cover_isColimit f
  refine ⟨{
    finite := fun n => Branch f (some n)
    residual := Branch f none
    finiteIn := fun _ => ↾Subtype.val
    residualIn := ↾Subtype.val
    result := ↾fun x => (exitAt f 0 x.val).get x.prop
    advance := fun n => ↾next f n
    residualStep := ↾stay f
    zero_eq := ?_
    succ_eq := ?_
    residual_eq := ?_
    isColimit := ?_ }⟩
  · apply ConcreteCategory.hom_ext
    intro x
    change f x.val = .inl ((exitAt f 0 x.val).get x.prop)
    have getEq := Option.some_get x.prop
    cases h : f x.val with
    | inl y =>
      have e : some ((exitAt f 0 x.val).get x.prop) = some y := getEq.trans (by simp [exitAt, h])
      exact congrArg Sum.inl (Option.some.inj e).symm
    | inr x' =>
      have e := x.prop
      simp [exitAt, h] at e
  · intro n
    apply ConcreteCategory.hom_ext
    intro x
    change f x.val = .inr (next f n x).val
    unfold next
    split
    next hx => have e := x.prop; simp [exitAt, hx] at e
    next hx => exact hx
  · apply ConcreteCategory.hom_ext
    intro x
    change f x.val = .inr (stay f x).val
    unfold stay
    split
    next hx => have e := x.prop 0; simp [exitAt, hx] at e
    next hx => exact hx
  · have h : (fun i : Option ℕ => match i with
        | some n => (↾Subtype.val : Branch f (.some n) ⟶ X)
        | none => (↾Subtype.val : Branch f none ⟶ X)) = (fun i => ↾state f i) := by
      funext i
      cases i <;> rfl
    change IsColimit (Cofan.mk (f := Branch f) X (fun i => match i with
      | some _ => ↾Subtype.val | none => ↾Subtype.val))
    rw [h]
    exact colimit

end Decomposition

end Silmaril.Calco2019.Maybe.Types.Proofs
