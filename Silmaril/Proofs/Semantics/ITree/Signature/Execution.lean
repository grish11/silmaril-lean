module

public import Silmaril.Semantics.ITree.Signature.Thms
import Silmaril.Proofs.Semantics.ITree.Signature.Coherence

public section

namespace Silmaril.Elgot.ITree.Signature.Proofs

open CategoryTheory
universe u v
variable {S T : Signature.{u}} {A B : Type v}

private theorem approx_bind_reindex (f : S ⟶ T) (n : Nat) (x : Approx S.Event A n)
    (k : A → Approx S.Event B n) :
    f.approx id n (Approx.bind n x k) = Approx.bind n (f.approx id n x) (f.approx id n ∘ k) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Approx.bind, Hom.approx, Part.bind_eq_bind, Part.map_bind, Part.bind_map]
    apply congrArg (Part.bind x)
    funext node
    cases node with
    | ret z => rfl
    | @vis R event next =>
      let q : Request S.Event := ⟨R, event⟩
      change Part.map (f.visible id (f.approx id n))
          (Part.some (.vis event fun r => Approx.bind n (next r) (fun z => Approx.truncate n (k z)))) =
        Part.some (.vis (f.request q).2 fun r =>
          Approx.bind n (f.approx id n (next (f.reply q r)))
            (fun z => Approx.truncate n (f.approx id (n + 1) (k z))))
      rw [Part.map_some]
      apply congrArg (fun k => Part.some (Visible.vis (f.request q).2 k))
      funext r
      simp only [truncate_approx f id]
      exact ih (next (f.reply q r)) (fun z => Approx.truncate n (k z))

theorem tree_bind_reindex (f : S ⟶ T) (t : Tree S.Event A) (k : A → Tree S.Event B) :
    f.tree id (t >>= k) = (f.tree id t >>= fun a => f.tree id (k a)) :=
  Tree.ext fun n => approx_bind_reindex f n (t.observe n) (fun a => (k a).observe n)

private theorem part_iter_map {X Y C D : Type v} (state : X → Y) (result : C → D)
    (f : X → Part (C ⊕ X)) (g : Y → Part (D ⊕ Y))
    (step : ∀ x, Part.map (Sum.map result state) (f x) = g (state x)) (x : X) :
    Part.map result (Elgot.iter f x) = Elgot.iter g (state x) := by
  have square : (Elgot.mapReturn f (Elgot.liftPure result) >=> Elgot.liftPure (Sum.map id state)) =
      (Elgot.liftPure state >=> g) := by
    funext z
    simp only [Bind.kleisliRight, Elgot.mapReturn, Elgot.liftPure,
      Part.bind_eq_bind, Part.bind_assoc, Function.comp_apply, Part.pure_eq_some, Part.bind_some]
    rw [← step z, ← Part.bind_some_eq_map]
    apply congrArg (Part.bind (f z))
    funext s
    cases s <;> simp [Sum.elim, Part.pure_eq_some]
  calc
    Part.map result (Elgot.iter f x) = (Elgot.iter f >=> Elgot.liftPure result) x :=
      (Part.bind_some_eq_map _ _).symm
    _ = Elgot.iter (Elgot.mapReturn f (Elgot.liftPure result)) x :=
      congrFun (Elgot.Part.naturality f (Elgot.liftPure result)) x
    _ = (Elgot.liftPure state >=> Elgot.iter g) x :=
      congrFun (Elgot.Part.uniformity _ g state square) x
    _ = Elgot.iter g (state x) := by simp [Bind.kleisliRight, Elgot.liftPure]

private theorem approx_iter_reindex (f : S ⟶ T) (n : Nat) (x : Approx S.Event (B ⊕ A) n)
    (k : A → Approx S.Event (B ⊕ A) n) :
    f.approx id n (Approx.iter n x k) = Approx.iter n (f.approx id n x) (f.approx id n ∘ k) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let state := f.approx (id : B ⊕ A → B ⊕ A) (n + 1)
    let result := f.visible (id : B → B) (f.approx (id : B → B) n)
    change Part.map result (Elgot.iter (Approx.iterStep n k) x) =
      Elgot.iter (Approx.iterStep n (state ∘ k)) (state x)
    apply part_iter_map state result
    intro y
    change Part.map (Sum.map result state) (Approx.iterStep n k y) =
      Approx.iterStep n (state ∘ k) (Part.map (f.visible id (f.approx id n)) y)
    simp only [Approx.iterStep, Part.bind_eq_bind, Part.map_bind, Part.bind_map]
    apply congrArg (Part.bind y)
    funext node
    cases node with
    | ret s => cases s <;> rfl
    | @vis R event next =>
      let q : Request S.Event := ⟨R, event⟩
      change Part.some (Sum.inl (β := Approx T.Event (B ⊕ A) (n + 1)) (result (.vis event fun r =>
          Approx.iter n (next r) (fun z => Approx.truncate n (k z))))) =
        Part.some (Sum.inl (Visible.vis (f.request q).2 fun r =>
          Approx.iter n (f.approx id n (next (f.reply q r)))
            (fun z => Approx.truncate n (state (k z)))))
      apply congrArg (fun k => Part.some (Sum.inl (β := Approx T.Event (B ⊕ A) (n + 1))
        (Visible.vis (f.request q).2 k)))
      funext r
      simp only [state, truncate_approx f id]
      exact ih (next (f.reply q r)) (fun z => Approx.truncate n (k z))

theorem tree_iter_reindex (f : S ⟶ T) (step : A → Tree S.Event (B ⊕ A)) (x : A) :
    f.tree id (Elgot.iter step x) = Elgot.iter (fun a => f.tree id (step a)) x := by
  apply Tree.ext
  intro n
  change f.approx id n ((Elgot.iter step x).observe n) = (Elgot.iter (fun a => f.tree id (step a)) x).observe n
  simp only [observe_iter]
  exact approx_iter_reindex f n ((step x).observe n) (fun a => (step a).observe n)

end Silmaril.Elgot.ITree.Signature.Proofs
