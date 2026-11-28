module

public import Silmaril.Semantics.Brookes.Iteration.Defs
import Silmaril.Semantics.Brookes.Parallel.Thms

public section

namespace Silmaril.Proofs.Semantics.Brookes.Iteration

open Silmaril.Semantics.Brookes
open Silmaril.Semantics.Domain OmegaCompletePartialOrder
open Silmaril.Elgot

universe u v w

variable {Store : Type u} {X : Type v} {Y : Type w}

theorem bind_mono {p q : Behavior Store X} {k l : X → Behavior Store Y}
    (hp : p ≤ q) (hk : k ≤ l) : p.bind k ≤ q.bind l := by
  intro trace y h
  obtain ⟨left, right, x, hl, hr, hd⟩ := Behavior.bind_accepts_iff.mp h
  exact Behavior.bind_accepts_iff.mpr ⟨left, right, x, hp hl, hk x hr, hd⟩

theorem bind_union_left {ι : Type*} (p : ι → Behavior Store X) (k : X → Behavior Store Y) :
    (Behavior.union p).bind k = Behavior.union (fun i => (p i).bind k) := by
  apply Behavior.ext
  intro trace y
  constructor
  · intro h
    obtain ⟨left, right, x, ⟨i, hl⟩, hr, hd⟩ := Behavior.bind_accepts_iff.mp h
    exact ⟨i, Behavior.bind_accepts_iff.mpr ⟨left, right, x, hl, hr, hd⟩⟩
  · rintro ⟨i, hi⟩
    obtain ⟨left, right, x, hl, hr, hd⟩ := Behavior.bind_accepts_iff.mp hi
    exact Behavior.bind_accepts_iff.mpr ⟨left, right, x, ⟨i, hl⟩, hr, hd⟩

theorem bind_union_right {ι : Type*} (p : Behavior Store X) (k : ι → X → Behavior Store Y) :
    p.bind (fun x => Behavior.union (fun i => k i x)) =
      Behavior.union (fun i => p.bind (k i)) := by
  apply Behavior.ext
  intro trace y
  constructor
  · intro h
    obtain ⟨left, right, x, hl, ⟨i, hr⟩, hd⟩ := Behavior.bind_accepts_iff.mp h
    exact ⟨i, Behavior.bind_accepts_iff.mpr ⟨left, right, x, hl, hr, hd⟩⟩
  · rintro ⟨i, hi⟩
    obtain ⟨left, right, x, hl, hr, hd⟩ := Behavior.bind_accepts_iff.mp hi
    exact Behavior.bind_accepts_iff.mpr ⟨left, right, x, hl, ⟨i, hr⟩, hd⟩

theorem bot_bind (k : X → Behavior Store Y) : (⊥ : Behavior Store X).bind k = ⊥ := by
  apply Behavior.ext
  intro trace y
  exact ⟨fun h => by obtain ⟨_, _, _, h, _, _⟩ := Behavior.bind_accepts_iff.mp h; exact h,
    False.elim⟩

theorem bind_bot (p : Behavior Store X) : p.bind (fun _ => (⊥ : Behavior Store Y)) = ⊥ := by
  apply Behavior.ext
  intro trace y
  exact ⟨fun h => by obtain ⟨_, _, _, _, h, _⟩ := Behavior.bind_accepts_iff.mp h; exact h,
    False.elim⟩

private theorem unfold_mono (body : X → Behavior Store (Y ⊕ X)) :
    Monotone (Behavior.unfoldLoop body) := by
  intro k l h x
  apply bind_mono le_rfl
  intro s
  cases s with
  | inl y => exact le_rfl
  | inr x => exact h x

theorem unfold_continuous (body : X → Behavior Store (Y ⊕ X)) :
    ωScottContinuous (Behavior.unfoldLoop body) := by
  refine ωScottContinuous.of_monotone_map_ωSup ⟨unfold_mono body, fun c => ?_⟩
  funext x
  change (body x).bind (Sum.elim Behavior.ret (ωSup c)) =
    Behavior.union (fun n => (body x).bind (Sum.elim Behavior.ret (c n)))
  rw [← bind_union_right (body x) (fun n => Sum.elim Behavior.ret (c n))]
  congr 1
  funext s
  cases s with
  | inr _ => rfl
  | inl y =>
    apply Behavior.ext
    intro trace result
    exact ⟨fun h => ⟨0, h⟩, fun ⟨_, h⟩ => h⟩

private theorem approx_eq_chain (body : X → Behavior Store (Y ⊕ X)) (n : Nat) :
    Behavior.approx body n =
      kleeneChain ⟨Behavior.unfoldLoop body, unfold_mono body⟩ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Behavior.approx, kleeneChain_succ, ih]
    rfl

theorem approx_monotone (body : X → Behavior Store (Y ⊕ X)) :
    Monotone (Behavior.approx body) := by
  intro m n h
  rw [approx_eq_chain, approx_eq_chain]
  exact (kleeneChain ⟨Behavior.unfoldLoop body, unfold_mono body⟩).monotone h

theorem iterate_eq_fix (body : X → Behavior Store (Y ⊕ X)) :
    Behavior.iterate body = fix (ContinuousHom.ofFun _ (unfold_continuous body)) := by
  funext x
  change Behavior.union (fun n => Behavior.approx body n x) =
    Behavior.union (fun n => kleeneChain ⟨Behavior.unfoldLoop body, unfold_mono body⟩ n x)
  exact congrArg Behavior.union (funext fun n => congrFun (approx_eq_chain body n) x)

theorem iterate_unfold (body : X → Behavior Store (Y ⊕ X)) :
    Behavior.unfoldLoop body (Behavior.iterate body) = Behavior.iterate body := by
  rw [iterate_eq_fix]
  exact fix_eq (ContinuousHom.ofFun _ (unfold_continuous body))

theorem iterate_least (body : X → Behavior Store (Y ⊕ X)) (k : X → Behavior Store Y)
    (h : Behavior.unfoldLoop body k ≤ k) : Behavior.iterate body ≤ k := by
  rw [iterate_eq_fix]
  exact fix_le (f := ContinuousHom.ofFun _ (unfold_continuous body)) h

section Elgot

variable {A B C : Type v}

private theorem unfold_post (f : A → Behavior Store (B ⊕ A)) (k : A → Behavior Store B)
    (g : B → Behavior Store C) (x : A) :
    (Behavior.unfoldLoop f k x).bind g =
      (f x).bind (Sum.elim g (fun next => (k next).bind g)) := by
  rw [Behavior.unfoldLoop, Behavior.bind_assoc]
  congr 1
  funext s
  cases s with
  | inl y => exact Behavior.ret_bind y g
  | inr x => rfl

private theorem unfold_mapReturn (f : A → Behavior Store (B ⊕ A)) (g : B → Behavior Store C)
    (k : A → Behavior Store C) (x : A) :
    Behavior.unfoldLoop (mapReturn f g) k x = (f x).bind (Sum.elim g k) := by
  change ((f x).bind _).bind _ = _
  rw [Behavior.bind_assoc]
  congr 1
  funext s
  cases s with
  | inl y =>
    change ((g y).bind (Behavior.ret ∘ Sum.inl)).bind (Sum.elim Behavior.ret k) = g y
    rw [Behavior.bind_assoc]
    have h : (fun z => (Behavior.ret (Sum.inl z)).bind (Sum.elim Behavior.ret k)) =
        (Behavior.ret : C → Behavior Store C) :=
      funext fun z => Behavior.ret_bind (.inl z) (Sum.elim Behavior.ret k)
    change (g y).bind (fun z => (Behavior.ret (Sum.inl z)).bind _) = g y
    rw [h, Behavior.bind_ret]
  | inr x => exact Behavior.ret_bind (.inr x) (Sum.elim Behavior.ret k)

theorem iterate_naturality (f : A → Behavior Store (B ⊕ A)) (g : B → Behavior Store C) :
    (fun x => (Behavior.iterate f x).bind g) = Behavior.iterate (mapReturn f g) := by
  have h (n : Nat) (x : A) :
      (Behavior.approx f n x).bind g = Behavior.approx (mapReturn f g) n x := by
    induction n generalizing x with
    | zero => exact bot_bind g
    | succ n ih =>
      rw [Behavior.approx, Behavior.approx, unfold_post, unfold_mapReturn]
      simp only [ih]
  funext x
  rw [Behavior.iterate, bind_union_left, Behavior.iterate]
  exact congrArg Behavior.union (funext fun n => h n x)

theorem iterate_uniformity (f : A → Behavior Store (B ⊕ A))
    (g : C → Behavior Store (B ⊕ C)) (h : A → C)
    (comm : (f >=> liftPure (Sum.map id h)) = (liftPure h >=> g)) :
    Behavior.iterate f = Behavior.iterate g ∘ h := by
  have unfold (k : C → Behavior Store B) (x : A) :
      Behavior.unfoldLoop f (k ∘ h) x = Behavior.unfoldLoop g k (h x) := by
    have eq := congrArg (fun p => (p x).bind (Sum.elim Behavior.ret k)) comm
    change ((f x).bind (Behavior.ret ∘ Sum.map id h)).bind _ =
      ((Behavior.ret (h x)).bind g).bind _ at eq
    rw [Behavior.ret_bind, Behavior.bind_assoc] at eq
    refine Eq.trans ?_ eq
    change (f x).bind _ = (f x).bind _
    congr 1
    funext s
    cases s with
    | inl b => exact (Behavior.ret_bind (.inl b) (Sum.elim Behavior.ret k)).symm
    | inr a => exact (Behavior.ret_bind (.inr (h a)) (Sum.elim Behavior.ret k)).symm
  have ha (n : Nat) : Behavior.approx f n = Behavior.approx g n ∘ h := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Behavior.approx, Behavior.approx, ih]
      exact funext (unfold _)
  funext x
  exact congrArg Behavior.union (funext fun n => congrFun (ha n) x)

private theorem unfold_flatten (f : A → Behavior Store ((B ⊕ A) ⊕ A))
    (k : A → Behavior Store B) (x : A) :
    Behavior.unfoldLoop (flattenBody f) k x = (f x).bind (Sum.elim (Sum.elim Behavior.ret k) k) := by
  change ((f x).bind (Behavior.ret ∘ flatten)).bind (Sum.elim Behavior.ret k) = _
  rw [Behavior.bind_assoc]
  congr 1
  funext s
  cases s <;> exact Behavior.ret_bind _ _

theorem iterate_codiagonal (f : A → Behavior Store ((B ⊕ A) ⊕ A)) :
    Behavior.iterate (Behavior.iterate f) = Behavior.iterate (flattenBody f) := by
  apply le_antisymm
  · let k := Behavior.iterate (flattenBody f)
    have fixed (x : A) : (f x).bind (Sum.elim (Sum.elim Behavior.ret k) k) = k x :=
      (unfold_flatten f k x).symm.trans (congrFun (iterate_unfold (flattenBody f)) x)
    have bounded (n : Nat) (x : A) :
        (Behavior.approx f n x).bind (Sum.elim Behavior.ret k) ≤ k x := by
      induction n generalizing x with
      | zero =>
        change (⊥ : Behavior Store (B ⊕ A)).bind (Sum.elim Behavior.ret k) ≤ _
        rw [bot_bind]
        exact bot_le
      | succ n ih =>
        rw [Behavior.approx, unfold_post, ← fixed x]
        apply bind_mono le_rfl
        intro s
        cases s with
        | inl y => exact le_rfl
        | inr next => exact ih next
    apply iterate_least
    intro x
    change (Behavior.union _).bind (Sum.elim Behavior.ret k) ≤ k x
    rw [bind_union_left]
    rintro _ _ ⟨n, h⟩
    exact bounded n x h
  · let k := Behavior.iterate (Behavior.iterate f)
    have outer (x : A) : (Behavior.iterate f x).bind (Sum.elim Behavior.ret k) = k x :=
      congrFun (iterate_unfold (Behavior.iterate f)) x
    apply iterate_least
    intro x
    rw [unfold_flatten]
    have inner := unfold_post f (Behavior.iterate f) (Sum.elim Behavior.ret k) x
    rw [congrFun (iterate_unfold f) x, outer x] at inner
    have h : (fun next => (Behavior.iterate f next).bind (Sum.elim Behavior.ret k)) = k :=
      funext outer
    rw [h] at inner
    exact inner.symm.le

end Elgot

theorem iterate_strength {D : Type*} (f : X → Behavior Store (Y ⊕ X)) (d : D) (x : X) :
    (Behavior.iterate f x).strength d = Behavior.iterate (Behavior.strengthBody f) (d, x) := by
  have h (n : Nat) (x : X) :
      (Behavior.approx f n x).strength d =
        Behavior.approx (Behavior.strengthBody f) n (d, x) := by
    induction n generalizing x with
    | zero =>
      apply Behavior.ext
      intro trace value
      exact ⟨fun ⟨_, h, _⟩ => h, False.elim⟩
    | succ n ih =>
      rw [Behavior.approx, Behavior.approx]
      change ((f x).bind (Sum.elim Behavior.ret (Behavior.approx f n))).mapResult
          (fun y => (d, y)) =
        ((f x).mapResult (Sum.map (fun y => (d, y)) (fun x' => (d, x')))).bind
          (Sum.elim Behavior.ret (Behavior.approx (Behavior.strengthBody f) n))
      rw [Behavior.mapResult_bind, Behavior.bind_mapResult]
      congr 1
      funext s
      cases s with
      | inl y => exact Behavior.mapResult_ret (fun y => (d, y)) y
      | inr next => exact ih next
  apply Behavior.ext
  intro trace result
  constructor
  · rintro ⟨y, ⟨n, hy⟩, eq⟩
    refine ⟨n, ?_⟩
    change (Behavior.approx (Behavior.strengthBody f) n (d, x)).accepts trace result
    rw [← h n x]
    exact ⟨y, hy, eq⟩
  · rintro ⟨n, hn⟩
    change (Behavior.approx (Behavior.strengthBody f) n (d, x)).accepts trace result at hn
    rw [← h n x] at hn
    obtain ⟨y, hy, eq⟩ := hn
    exact ⟨y, ⟨n, hy⟩, eq⟩

theorem iterate_inr_eq_bot (f : X → Behavior Store (Y ⊕ X))
    (h : ∀ x trace y, ¬(f x).accepts trace (.inl y)) : Behavior.iterate f = ⊥ := by
  have ha (n : Nat) (x : X) : Behavior.approx f n x = ⊥ := by
    induction n generalizing x with
    | zero => rfl
    | succ n ih =>
      apply Behavior.ext
      intro trace y
      refine ⟨fun hb => ?_, False.elim⟩
      obtain ⟨left, right, s, hl, hr, _⟩ := Behavior.bind_accepts_iff.mp hb
      cases s with
      | inl result => exact h x left result hl
      | inr next =>
        change (Behavior.approx f n next).accepts right y at hr
        rw [ih] at hr
        exact hr
  funext x
  apply Behavior.ext
  intro trace y
  refine ⟨fun ⟨n, hn⟩ => ?_, False.elim⟩
  change (Behavior.approx f n x).accepts trace y at hn
  rw [ha n x] at hn
  exact hn

theorem ret_ne_bot (s : Store) (y : Y) : Behavior.ret y ≠ (⊥ : Behavior Store Y) := by
  intro eq
  have h : (Behavior.ret y).completes s s y := Behavior.atomic_completes_iff.mpr ⟨rfl, rfl⟩
  rw [eq] at h
  exact h


end Silmaril.Proofs.Semantics.Brookes.Iteration
