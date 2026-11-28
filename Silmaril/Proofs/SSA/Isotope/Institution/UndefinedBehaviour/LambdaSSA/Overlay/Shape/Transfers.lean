module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Preservation
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Behaviour

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape
open Silmaril.Isotope.Morphism.SSAIter (envOfBound_agrees)

universe u v w x

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)]
variable {α : Type w} {σ : Type x} {atomType : α → κ → Prop} {R L K : List (Ty κ)}

private theorem bind_returns_typed {p : Behaviour L.length α σ}
    {k : Fin L.length → Value α → σ → Behaviour K.length α σ}
    (source : ReturnsTyped atomType p)
    (next : ∀ i a s, ValueTyped atomType a (L.get i) → ReturnsTyped atomType (k i a s)) :
    ReturnsTyped atomType (p.bind k) := by
  classical
  intro j b t ret
  have ordinary : ¬ (p = ⊤ ∨ ∃ i a s, .ret i a s ∈ p.possible ∧ k i a s = ⊤) := by
    intro reached
    exact ret.1 (ite_eq_left reached)
  have run := ret.2
  rw [Behaviour.bind, ite_eq_right ordinary] at run
  change False ∨ ∃ i a s, Outcome.ret i a s ∈ p.possible ∧
    Outcome.ret j b t ∈ (k i a s).possible at run
  rcases run with impossible | ⟨i, a, s, head, tail⟩
  · exact impossible.elim
  · exact next i a s (source ⟨fun h => ordinary (.inl h), head⟩)
      ⟨fun h => ordinary (.inr ⟨i, a, s, head, h⟩), tail⟩

private theorem close_returns_typed {entry : σ → Behaviour (R ++ L).length α σ}
    {blocks : Fin R.length → Value α → σ → Behaviour (R ++ L).length α σ} {s : σ}
    (head : ∀ s, ReturnsTyped atomType (entry s))
    (body : ∀ i a s, ValueTyped atomType a (R.get i) → ReturnsTyped atomType (blocks i a s)) :
    ReturnsTyped atomType (Feedback.close (Feedback.run entry blocks) (.entry s)) := by
  let f := Feedback.run (R := R) (L := L) entry blocks
  let TypedPoint : Feedback.Point R.length α σ → Prop
    | .entry _ => True
    | .block i a _ => ValueTyped atomType a (R.get i)
  have localReturns (p) (hp : TypedPoint p) : ReturnsTyped atomType (f p) := by
    cases p with
    | entry s => exact head s
    | block i a s => exact body i a s hp
  have stepTyped {p q} (hp : TypedPoint p) (step : Feedback.Step f p q) : TypedPoint q := by
    cases step with
    | branch ret =>
      have typed := localReturns p hp ret
      simpa [TypedPoint, Feedback.internal, List.get_eq_getElem] using typed
  intro i a t ret
  rcases (Feedback.ordinary_close_iff.mp ret).2 with ⟨q, reach, finish⟩ | ⟨impossible, _⟩
  · have hq : TypedPoint q := by
      clear finish
      induction reach with
      | refl => trivial
      | tail _ step ih => exact stepTyped ih step
    have typed := localReturns q hq finish
    simpa [Feedback.external, List.get_eq_getElem, Nat.add_comm] using typed
  · cases impossible

theorem returns_typed {Γ L : List (Ty κ)} (r : LambdaSSA.UB.Overlay.Region Φ Γ L)
    (M : Shape.Model.{u,v,w,x} Φ Γ) (s : M.raw.σ) : ReturnsTyped M.atomType (Shape.denote r M s) := by
  induction r with
  | @native Γ L r =>
    intro i a t ret
    have observed := (mem_nativeOutcomes_iff r (envOfBound_agrees M.raw.bound) s (.ret i a t)).mp ret.2
    obtain ⟨A, atLabel, typed⟩ := region_eval_typed M r.property observed
    have same : A = L.get i := Option.some.inj (atLabel.symm.trans (List.getElem?_eq_getElem i.isLt))
    exact same ▸ typed
  | ub =>
    intro i a t ret
    exact (ret.1 rfl).elim
  | lsubst r k ih branches =>
    exact bind_returns_typed (ih M s) (fun i _ t ha => branches i (M.extend ha) t)
  | feedback entry blocks ih heads =>
    exact close_returns_typed (ih M) (fun i _ t ha => heads i (M.extend ha) t)

theorem lsubst_mono_typed {Γ : List (Ty κ)} (r : LambdaSSA.UB.Overlay.Region Φ Γ L)
    (k h : (i : Fin L.length) → LambdaSSA.UB.Overlay.Region Φ (L.get i :: Γ) K)
    (M : Shape.Model.{u,v,w,x} Φ Γ) (s : M.raw.σ)
    (next : ∀ i {a} (ha : ValueTyped M.atomType a (L.get i)) t,
      Shape.denote (k i) (M.extend ha) t ≤ Shape.denote (h i) (M.extend ha) t) :
    Shape.denote (.lsubst r k) M s ≤ Shape.denote (.lsubst r h) M s := by
  classical
  let p := Shape.denote r M s
  let left (i : Fin L.length) a t := denote (k i) (extendModel M.raw a) t
  let right (i : Fin L.length) a t := denote (h i) (extendModel M.raw a) t
  let reachable (i : Fin L.length) a t := if p.Ordinary (.ret i a t) then left i a t else right i a t
  change p.bind left ≤ p.bind right
  have same : p.bind left = p.bind reachable :=
    Category.bind_congr (fun i a t hit => (ite_eq_left hit).symm)
  rw [same]
  refine Behaviour.bind_mono le_rfl fun i a t => ?_
  by_cases hit : p.Ordinary (.ret i a t)
  · have ha := returns_typed r M s hit
    rw [show reachable i a t = left i a t from ite_eq_left hit]
    exact next i ha t
  · simp only [reachable, ite_eq_right hit, le_rfl]

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape
