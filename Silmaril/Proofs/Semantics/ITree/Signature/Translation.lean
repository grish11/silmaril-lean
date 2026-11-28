module

public import Silmaril.Semantics.ITree.Signature.Tree.Defs

public section

namespace Silmaril.Elgot.ITree.Signature.Proofs

open CategoryTheory

universe u v w z

variable {S T U : Signature.{u}} {A : Type v} {B : Type w} {C : Type z}

theorem approx_id (n : Nat) (obs : Approx S.Event A n) :
    Hom.approx (𝟙 S) id n obs = obs := by
  induction n with
  | zero => cases obs; rfl
  | succ n ih =>
    change Part.map _ obs = obs
    have h : (𝟙 S : S ⟶ S).visible (id : A → A) ((𝟙 S : S ⟶ S).approx (id : A → A) n) = id := by
      funext node
      cases node with
      | ret => rfl
      | vis ev next =>
        change Visible.vis ev (fun r => Hom.approx (𝟙 S) id n (next r)) = _
        simp only [ih, id]
    rw [h, Part.map_id']; intro; rfl

theorem approx_comp (f : S ⟶ T) (g : T ⟶ U) (a : A → B) (b : B → C)
    (n : Nat) (obs : Approx S.Event A n) :
    (f ≫ g).approx (b ∘ a) n obs = g.approx b n (f.approx a n obs) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Hom.approx, Part.map_map]
    apply congrArg (fun h => Part.map h obs)
    funext node
    cases node with
    | ret => rfl
    | vis ev next =>
      simp only [Function.comp_apply, Hom.visible, ih]
      rfl

theorem approx_ofEquiv {B : Type v} (e : SignatureEquiv S.Event T.Event) (a : A ≃ B)
    (n : Nat) (obs : Approx S.Event A n) :
    (ofEquiv e).approx a n obs = (e.approx a n) obs := by
  induction n with
  | zero => cases obs; rfl
  | succ n ih =>
    simp only [Hom.approx, SignatureEquiv.approx, Equiv.coe_fn_mk]
    apply congrArg (fun h => Part.map h obs)
    funext node
    cases node with
    | ret => rfl
    | @vis R ev next =>
      let q : Request S.Event := ⟨R, ev⟩
      let reply := (e.reply q).symm
      change Visible.vis (e.request q).2 (fun r => (ofEquiv e).approx a n (next (reply r))) =
        Visible.vis (e.request q).2 (fun r => (e.approx a n) (next (reply r)))
      simp only [ih]

theorem out_tree (f : S ⟶ T) (a : A → B) (t : Tree S.Event A) :
    out (f.tree a t) = Part.map (f.visible a (f.tree a)) (out t) := by
  rw [← out_roll (Part.map (f.visible a (f.tree a)) (out t))]
  congr 1
  apply Tree.ext
  intro n
  cases n with
  | zero => rfl
  | succ n =>
    change Part.map (f.visible a (f.approx a n)) (t.observe (n + 1)) = _
    rw [observe_succ_eq_out, Part.map_eq_map]
    simp only [roll, Part.map_eq_map, Part.map_map]
    apply congrArg (fun h => Part.map h (out t))
    funext node
    cases node <;> rfl

end Silmaril.Elgot.ITree.Signature.Proofs
