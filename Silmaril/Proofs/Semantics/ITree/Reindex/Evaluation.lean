module

public import Silmaril.Semantics.ITree.Reindex.Defs

public section

namespace Silmaril.Proofs.ITree.Reindex

open Silmaril.Elgot.ITree

universe u v

variable {E F : Type u → Type u} {A A' B B' : Type v}

private theorem approx_bind (e : SignatureEquiv E F) (a : A ≃ A') (b : B ≃ B')
    (n : Nat) (x : Approx E A n) (k : A → Approx E B n) (l : A' → Approx F B' n)
    (h : ∀ z, e.approx b n (k z) = l (a z)) :
    e.approx b n (Approx.bind n x k) = Approx.bind n (e.approx a n x) l := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Approx.bind, SignatureEquiv.approx, Equiv.coe_fn_mk, Part.bind_eq_bind,
      Part.map_bind, Part.bind_map]
    apply congrArg (Part.bind x)
    funext node
    cases node with
    | ret z => exact h z
    | @vis R ev next =>
      let q : Request E := ⟨R, ev⟩
      change Part.map (e.visibleEquiv b (e.approx b n))
          (Part.some (.vis ev fun r => Approx.bind n (next r) (fun z => Approx.truncate n (k z)))) =
        Part.some (.vis (e.request q).2 fun r =>
          Approx.bind n (e.approx a n (next ((e.reply q).symm r)))
            (fun z => Approx.truncate n (l z)))
      rw [Part.map_some]
      apply congrArg (fun k => Part.some (Visible.vis (e.request q).2 k))
      funext r
      apply ih
      intro z
      rw [← e.approx_truncate, h z]

theorem tree_bind (e : SignatureEquiv E F) (a : A ≃ A') (b : B ≃ B') (t : Tree E A)
    (k : A → Tree E B) (l : A' → Tree F B') (h : ∀ z, e.tree b (k z) = l (a z)) :
    e.tree b (t >>= k) = (e.tree a t >>= l) :=
  Tree.ext fun n => approx_bind e a b n (t.observe n) (fun z => (k z).observe n)
    (fun z => (l z).observe n) (fun z => congrArg (fun t => t.observe n) (h z))

private theorem part_iter {X X' Y Y' : Type v} (a : X → X') (b : Y → Y')
    (f : X → Part (Y ⊕ X)) (g : X' → Part (Y' ⊕ X'))
    (h : ∀ x, Part.map (Sum.map b a) (f x) = g (a x)) (x : X) :
    Part.map b (Elgot.iter f x) = Elgot.iter g (a x) := by
  have hu : (Elgot.mapReturn f (Elgot.liftPure b) >=> Elgot.liftPure (Sum.map id a)) =
      (Elgot.liftPure a >=> g) := by
    funext z
    simp only [Bind.kleisliRight, Elgot.mapReturn, Elgot.liftPure,
      Part.bind_eq_bind, Part.bind_assoc, Function.comp_apply, Part.pure_eq_some, Part.bind_some]
    rw [← h z, ← Part.bind_some_eq_map]
    apply congrArg (Part.bind (f z))
    funext s
    cases s <;> simp [Sum.elim, Part.pure_eq_some]
  calc
    Part.map b (Elgot.iter f x) = (Elgot.iter f >=> Elgot.liftPure b) x :=
      (Part.bind_some_eq_map _ _).symm
    _ = Elgot.iter (Elgot.mapReturn f (Elgot.liftPure b)) x :=
      congrFun (Elgot.Part.naturality f (Elgot.liftPure b)) x
    _ = (Elgot.liftPure a >=> Elgot.iter g) x :=
      congrFun (Elgot.Part.uniformity _ g a hu) x
    _ = Elgot.iter g (a x) := by simp [Bind.kleisliRight, Elgot.liftPure]

private theorem approx_iter (e : SignatureEquiv E F) (a : A ≃ A') (b : B ≃ B')
    (n : Nat) (x : Approx E (B ⊕ A) n) (f : A → Approx E (B ⊕ A) n)
    (g : A' → Approx F (B' ⊕ A') n)
    (h : ∀ z, e.approx (Equiv.sumCongr b a) n (f z) = g (a z)) :
    e.approx b n (Approx.iter n x f) =
      Approx.iter n (e.approx (Equiv.sumCongr b a) n x) g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let state := e.approx (Equiv.sumCongr b a) (n + 1)
    let result := e.visibleEquiv b (e.approx b n)
    change Part.map result (Elgot.iter (Approx.iterStep n f) x) =
      Elgot.iter (Approx.iterStep n g) (state x)
    apply part_iter state result
    intro y
    change Part.map (Sum.map result state) (Approx.iterStep n f y) =
      Approx.iterStep n g (Part.map (e.visibleEquiv (Equiv.sumCongr b a)
        (e.approx (Equiv.sumCongr b a) n)) y)
    simp only [Approx.iterStep, Part.bind_eq_bind, Part.map_bind, Part.bind_map]
    apply congrArg (Part.bind y)
    funext node
    cases node with
    | ret s =>
      cases s with
      | inl => rfl
      | inr z =>
        change Part.some (Sum.inr (α := Visible F B' (Approx F B' n)) (state (f z))) =
          Part.some (Sum.inr (g (a z)))
        rw [h z]
    | @vis R ev next =>
      let q : Request E := ⟨R, ev⟩
      change Part.some (Sum.inl (β := Approx F (B' ⊕ A') (n + 1)) (result (.vis ev fun r =>
          Approx.iter n (next r) (fun z => Approx.truncate n (f z))))) =
        Part.some (Sum.inl (Visible.vis (e.request q).2 fun r =>
          Approx.iter n (e.approx (Equiv.sumCongr b a) n (next ((e.reply q).symm r)))
            (fun z => Approx.truncate n (g z))))
      apply congrArg (fun k => Part.some (Sum.inl (β := Approx F (B' ⊕ A') (n + 1))
        (Visible.vis (e.request q).2 k)))
      funext r
      apply ih
      intro z
      rw [← e.approx_truncate, h z]

theorem tree_iter (e : SignatureEquiv E F) (a : A ≃ A') (b : B ≃ B')
    (f : A → Tree E (B ⊕ A)) (g : A' → Tree F (B' ⊕ A'))
    (h : ∀ z, e.tree (Equiv.sumCongr b a) (f z) = g (a z)) (x : A) :
    e.tree b (Elgot.iter f x) = Elgot.iter g (a x) := by
  apply Tree.ext
  intro n
  change e.approx b n ((Elgot.iter f x).observe n) = (Elgot.iter g (a x)).observe n
  simp only [observe_iter]
  have hn (z : A) : e.approx (Equiv.sumCongr b a) n ((f z).observe n) =
      (g (a z)).observe n := congrArg (fun t => t.observe n) (h z)
  rw [approx_iter e a b n _ _ (fun z => (g z).observe n) hn, hn]

end Silmaril.Proofs.ITree.Reindex
