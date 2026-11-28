module

public import Silmaril.Semantics.ExactITree.Defs

public section

namespace Silmaril.Elgot.ITree.Exact.Proofs

open CategoryTheory

universe u v

variable {S T U : Signature.{u}} {P : Profile.{v}} {A B : Type v}

@[simp] theorem lower_ret (f : S ⟶ T) (a : A) : f.lower (ret a) = ret a := by
  apply Tree.ext
  intro n
  cases n <;> rfl

@[simp] theorem lower_diverge (f : S ⟶ T) : f.lower (diverge : Tree S.Event A) = diverge := by
  apply Tree.ext
  intro n
  cases n
  · rfl
  · exact Part.map_none _

@[simp] theorem lower_vis (f : S ⟶ T) {R : Type u} (e : S.Event R) (k : R → Tree S.Event A) :
    f.lower (vis e k) = vis (f.exchange e).event (fun r => f.lower (k ((f.exchange e).project r))) := by
  apply Tree.ext
  intro n
  cases n <;> rfl

private theorem approx_id (n : Nat) (x : Approx S.Event A n) : Signature.Hom.approx (𝟙 S) n x = x := by
  induction n with
  | zero => cases x; rfl
  | succ n ih =>
    change Part.map _ x = x
    apply Part.map_id' _ x
    intro root
    cases root with
    | ret => rfl
    | vis e k =>
      change Visible.vis e (fun r => Signature.Hom.approx (𝟙 S) n (k r)) = Visible.vis e k
      simp only [ih]

theorem lower_id (t : Tree S.Event A) : Signature.Hom.lower (𝟙 S) t = t :=
  Tree.ext fun n => approx_id n (t.observe n)

private theorem approx_comp (f : S ⟶ T) (g : T ⟶ U) (n : Nat) (x : Approx S.Event A n) :
    (f ≫ g).approx n x = g.approx n (f.approx n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Signature.Hom.approx, Part.map_map]
    apply congrArg (fun h => Part.map h x)
    funext root
    cases root with
    | ret => rfl
    | vis e k =>
      simp only [Function.comp_apply, Signature.Hom.layer]
      change Visible.vis (g.exchange (f.exchange e).event).event _ = Visible.vis _ _
      congr 1
      funext r
      exact ih _

theorem lower_comp (f : S ⟶ T) (g : T ⟶ U) (t : Tree S.Event A) :
    (f ≫ g).lower t = g.lower (f.lower t) :=
  Tree.ext fun n => approx_comp f g n (t.observe n)

theorem lower_bind (f : S ⟶ T) (t : Tree S.Event A) (k : A → Tree S.Event B) :
    f.lower (t >>= k) = f.lower t >>= fun a => f.lower (k a) := by
  apply Tree.ext
  intro n
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    rcases cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R, e, next, rfl⟩
    · simp
    · have source : (ret a >>= k : Tree S.Event B) = k a := pure_bind a k
      have target : (ret a >>= fun a => f.lower (k a)) = f.lower (k a) := pure_bind a _
      rw [source, lower_ret, target]
    · simp only [vis_bind, lower_vis]
      change Part.some (Visible.vis (f.exchange e).event _) = Part.some (Visible.vis _ _)
      congr 2
      funext r
      exact ih _

private theorem completion_map_id {R : Type u} (c : Completion P R) : c.map id = c := by
  cases c <;> rfl

private theorem completion_map_comp {R X Y : Type u} (p : X → Y) (q : R → X)
    (c : Completion P R) : c.map (p ∘ q) = (c.map q).map p := by
  cases c <;> rfl

theorem reduct_id (K : Kernel P S) : Kernel.reduct (𝟙 S) K = K := by
  funext env store R e answer
  apply propext
  simp only [Kernel.reduct]
  change (∃ c, K env store e c ∧ c.map id = answer) ↔ _
  simp [completion_map_id]

theorem reduct_comp (f : S ⟶ T) (g : T ⟶ U) (K : Kernel P U) :
    Kernel.reduct (f ≫ g) K = Kernel.reduct f (Kernel.reduct g K) := by
  funext env store R e answer
  apply propext
  simp only [Kernel.reduct]
  change (∃ c, K env store (g.exchange (f.exchange e).event).event c ∧
      c.map ((f.exchange e).project ∘ (g.exchange (f.exchange e).event).project) = answer) ↔ _
  simp only [completion_map_comp]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨_, ⟨c, hc, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨c, hc, rfl⟩

end Silmaril.Elgot.ITree.Exact.Proofs
