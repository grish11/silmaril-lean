module

public import Silmaril.Logic.Algebraic.OrderSorted.Quotient.Thms

@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Algebraic.OrderSorted.Presented.Examples
open CategoryTheory CategoryTheory.Limits Silmaril.Logic.Institution.Examples

inductive Sorts where
  | lower | upper
  deriving DecidableEq
open Sorts

instance : PartialOrder Sorts where
  le s t := s = lower ∨ t = upper
  le_refl s := by cases s <;> simp
  le_trans := by intro s t u; cases s <;> cases t <;> cases u <;> simp_all
  le_antisymm := by intro s t; cases s <;> cases t <;> simp_all

theorem lower_upper : lower ≤ upper := Or.inl rfl

/-- Unique operation profiles: two lower constants and one genuinely upper value. -/
inductive Op : (n : Nat) → (Fin n → Sorts) → Sorts → Type where
  | left : Op 0 Fin.elim0 lower
  | right : Op 0 Fin.elim0 lower
  | fresh : Op 0 Fin.elim0 upper
abbrev signature : Signature := ⟨⟨Sorts, Op⟩, inferInstance⟩

def left {k : Nat} {Γ : Fin k → Sorts} : EQ.Term (compiled signature) Γ lower :=
  .app (.base .left) (fun i => i.elim0)
def right {k : Nat} {Γ : Fin k → Sorts} : EQ.Term (compiled signature) Γ lower :=
  .app (.base .right) (fun i => i.elim0)
def fresh {k : Nat} {Γ : Fin k → Sorts} : EQ.Term (compiled signature) Γ upper :=
  .app (.base .fresh) (fun i => i.elim0)
def up {k : Nat} {Γ : Fin k → Sorts} (t : EQ.Term (compiled signature) Γ lower) :
    EQ.Term (compiled signature) Γ upper :=
  .app (n := 1) (Operation.inclusion (A := signature) lower upper lower_upper) (fun _ => t)
def imageEquation : Sentence signature :=
  ⟨0, Free.closedContext signature, upper, up left, up right⟩
def theory : Initial.Theory := ⟨signature, {ULift.up imageEquation}⟩

abbrev rawLeft : Free.Normal signature (Free.closedContext signature) lower :=
  Free.embed (.app .left (fun i => i.elim0))
abbrev rawRight : Free.Normal signature (Free.closedContext signature) lower :=
  Free.embed (.app .right (fun i => i.elim0))
abbrev rawFresh : Free.Normal signature (Free.closedContext signature) upper :=
  Free.embed (.app .fresh (fun i => i.elim0))

theorem raw_lower_distinct : rawLeft ≠ rawRight := by
  intro h
  cases h

/-- Distinct lower syntax is identified by an equation only at the upper sort. -/
theorem forced_lower_collapse :
    (projection theory (Free.closedContext signature)).map lower rawLeft =
      (projection theory (Free.closedContext signature)).map lower rawRight := by
  apply Quotient.sound (s := setoid theory (Free.closedContext signature) lower)
  apply Rel.reflect lower_upper
  have h := Rel.equation (T := theory) (Γ := Free.closedContext signature) imageEquation
    (Set.mem_singleton _) (fun i => i.elim0)
  have hl : imageEquation.lhs.eval (Free.model signature (Free.closedContext signature)).algebra
      (fun i => i.elim0) = Free.coerce lower_upper rawLeft := by
    dsimp only [imageEquation, up, left, EQ.Term.eval, Free.model]
    apply congrArg (Free.coerce lower_upper)
    apply congrArg Free.embed
    apply congrArg (Free.Core.app (A := signature) Op.left)
    funext i
    exact i.elim0
  have hr : imageEquation.rhs.eval (Free.model signature (Free.closedContext signature)).algebra
      (fun i => i.elim0) = Free.coerce lower_upper rawRight := by
    dsimp only [imageEquation, up, right, EQ.Term.eval, Free.model]
    apply congrArg (Free.coerce lower_upper)
    apply congrArg Free.embed
    apply congrArg (Free.Core.app (A := signature) Op.right)
    funext i
    exact i.elim0
  exact hl ▸ hr ▸ h

abbrev carrier : Sorts → Type
  | lower => Unit
  | upper => Bool

def inclusion {s t : Sorts} (h : s ≤ t) : carrier s → carrier t :=
  match s, t with
  | lower, lower => id
  | lower, upper => fun _ => false
  | upper, upper => id
  | upper, lower => False.elim (by change upper = lower ∨ lower = upper at h; cases h <;> contradiction)

/-- Independent coherent target: the lower image is false and the fresh value true. -/
abbrev separating : Model signature where
  algebra := {
    carrier := carrier
    op := fun o args => match o with
      | .base .left => ()
      | .base .right => ()
      | .base .fresh => true
      | .inclusion _ _ h => inclusion h (args 0) }
  coherent := {
    identity := by intro s x; cases s <;> rfl
    injective := by
      intro s t h x y he
      cases s <;> cases t
      · exact he
      · exact Subsingleton.elim _ _
      · exact False.elim (by change upper = lower ∨ lower = upper at h; cases h <;> contradiction)
      · exact he
    composition := by
      intro s t u h j x
      cases s <;> cases t <;> cases u <;>
        first | rfl | exact False.elim (by change upper = lower ∨ lower = upper at h; cases h <;> contradiction) }

def separatingModel : Initial.Models theory := ⟨separating, by
  intro e he
  have heq : e = ULift.up imageEquation := Set.mem_singleton_iff.mp he
  subst e
  intro v
  rfl⟩

/-- The quotient keeps a proper upper value outside the entire lower image. -/
theorem fresh_outside_image (x : (quotientModel theory).obj.algebra.carrier lower) :
    (quotientModel theory).obj.algebra.coerce lower_upper x ≠
      (projection theory (Free.closedContext signature)).map upper rawFresh := by
  intro h
  have he := congrArg ((foldHom separatingModel (fun i => i.elim0)).map upper) h
  have hc := Model.hom_coerce (foldHom separatingModel (fun i => i.elim0)) lower_upper x
  have impossible : false = true := hc.symm.trans he
  cases impossible

/-- A coherent singleton target and an actual noninjective model arrow. -/
def singleton : Model signature where
  algebra := { carrier _ := Unit, op _ _ := () }
  coherent := {
    identity := fun _ _ => Subsingleton.elim _ _
    injective := fun _ _ _ _ => Subsingleton.elim _ _
    composition := fun _ _ _ => rfl }
def collapseHom : separating ⟶ singleton where
  map _ _ := ()
  map_op _ _ := rfl

def singletonTheoryModel : Initial.Models theory := ⟨singleton, by
  intro e _ v
  exact @Subsingleton.elim Unit _ (e.down.lhs.eval singleton.algebra v)
    (e.down.rhs.eval singleton.algebra v)⟩

def theoryCollapseHom : separatingModel ⟶ singletonTheoryModel := ⟨collapseHom⟩

theorem collapseHom_not_injective : ¬ Function.Injective (collapseHom.map upper) := by
  intro h
  have impossible : false = true := h (a₁ := false) (a₂ := true) rfl
  cases impossible

theorem theoryCollapseHom_not_injective :
    ¬ Function.Injective (theoryCollapseHom.hom.map upper) := collapseHom_not_injective

/-- With no lower constructors, a lower context variable has no closed valuation. -/
inductive UpperOp : (n : Nat) → (Fin n → Sorts) → Sorts → Type where
  | left : UpperOp 0 Fin.elim0 upper
  | right : UpperOp 0 Fin.elim0 upper
abbrev upperSignature : Signature := ⟨⟨Sorts, UpperOp⟩, inferInstance⟩
def upperLeft {k : Nat} {Γ : Fin k → Sorts} : EQ.Term (compiled upperSignature) Γ upper :=
  .app (.base .left) (fun i => i.elim0)
def upperRight {k : Nat} {Γ : Fin k → Sorts} : EQ.Term (compiled upperSignature) Γ upper :=
  .app (.base .right) (fun i => i.elim0)
def vacuousEquation : Sentence upperSignature :=
  ⟨1, fun _ => lower, upper, upperLeft, upperRight⟩
def vacuousTheory : Initial.Theory := ⟨upperSignature, {ULift.up vacuousEquation}⟩

abbrev upperCarrier : Sorts → Type
  | lower => Empty
  | upper => Bool

def upperInclusion {s t : Sorts} (h : s ≤ t) : upperCarrier s → upperCarrier t :=
  match s, t with
  | lower, _ => Empty.elim
  | upper, upper => id
  | upper, lower => False.elim (by change upper = lower ∨ lower = upper at h; cases h <;> contradiction)
abbrev upperOnly : Model upperSignature where
  algebra := {
    carrier := upperCarrier
    op := fun o args => match o with
      | .base .left => false
      | .base .right => true
      | .inclusion _ _ h => upperInclusion h (args 0) }
  coherent := {
    identity := by intro s x; cases s; exact x.elim; rfl
    injective := by
      intro s t h x y he
      cases s
      · exact x.elim
      · cases t
        · exact False.elim (by change upper = lower ∨ lower = upper at h; cases h <;> contradiction)
        · exact he
    composition := by
      intro s t u h j x
      cases s
      · exact x.elim
      · cases t
        · exact False.elim (by change upper = lower ∨ lower = upper at h; cases h <;> contradiction)
        · cases u
          · exact False.elim (by change upper = lower ∨ lower = upper at j; cases j <;> contradiction)
          · rfl }
def upperOnlyModel : Initial.Models vacuousTheory := ⟨upperOnly, by
  intro e he
  have heq : e = ULift.up vacuousEquation := Set.mem_singleton_iff.mp he
  subst e
  intro v
  change (∀ i : Fin 1, upperCarrier lower) at v
  exact (v 0).elim⟩
abbrev rawUpperLeft : Free.Normal upperSignature (Free.closedContext upperSignature) upper :=
  Free.embed (.app .left (fun i => i.elim0))
abbrev rawUpperRight : Free.Normal upperSignature (Free.closedContext upperSignature) upper :=
  Free.embed (.app .right (fun i => i.elim0))

theorem lower_empty : IsEmpty ((quotientModel vacuousTheory).obj.algebra.carrier lower) :=
  ⟨fun q => ((foldHom upperOnlyModel (fun i => i.elim0)).map lower q).elim⟩

theorem vacuous_constants_distinct :
    (projection vacuousTheory (Free.closedContext upperSignature)).map upper rawUpperLeft ≠
      (projection vacuousTheory (Free.closedContext upperSignature)).map upper rawUpperRight := by
  intro h
  have he := rel_sound upperOnlyModel (fun i => i.elim0) (Quotient.exact h)
  have impossible : false = true := he
  cases impossible

end Silmaril.Logic.Algebraic.OrderSorted.Presented.Examples
