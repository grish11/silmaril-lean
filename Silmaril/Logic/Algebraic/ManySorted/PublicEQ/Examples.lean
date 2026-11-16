module

public import Silmaril.Logic.Algebraic.ManySorted.PublicEQ.Institution

@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Algebraic.ManySorted.PublicEQ.Examples
open CategoryTheory Silmaril.Logic.Institution.Examples

def pure : Signature Unit := ⟨fun _ _ _ => PEmpty⟩
def pureModel (X : Type) : Model pure := ⟨fun _ => X, fun op => PEmpty.elim op⟩
def ctx (k : Nat) : Fin k → Unit := fun _ => ()
def distinct : EQ.Equation (signature pure) := ⟨2, ctx 2, (), .var 0, .var 1⟩

theorem empty_vacuous : Equation.Satisfies (pureModel Empty) (toEquation distinct) := by
  intro ρ
  exact (ρ (0 : Fin 2)).elim

theorem false_nonreflexive : ¬ Equation.Satisfies (pureModel Bool) (toEquation distinct) := by
  intro h
  exact Bool.noConfusion (h (Fin.cases true (fun _ => false)))

theorem actual_public_false : ¬ distinct.Holds (fromModel (pureModel Bool)) :=
  fun h => false_nonreflexive ((satisfaction _ _).2 h)

/-- A genuinely noninjective arrow passes through both independently typed model APIs. -/
def squash : Model.Hom (pureModel Bool) (pureModel Unit) :=
  ⟨fun _ _ => (), fun op => PEmpty.elim op⟩

theorem squash_noninjective : ¬ Function.Injective (squash.map ()) := by
  intro h
  exact Bool.noConfusion (h (show squash.map () false = squash.map () true from rfl))

theorem actual_hom_roundtrip : (toModels pure).map ((fromModels pure).map squash) = squash := rfl

inductive Two : (n : Nat) → (Fin n → Unit) → Unit → Type
  | left : Two 0 (fun _ => ()) ()
  | right : Two 0 (fun _ => ()) ()
inductive One : (n : Nat) → (Fin n → Unit) → Unit → Type
  | only : One 0 (fun _ => ()) ()
def source : Signature Unit := ⟨Two⟩
def target : Signature Unit := ⟨One⟩
def collapse : source ⟶ target :=
  ⟨fun op => match op with | .left => .only | .right => .only⟩

theorem collapse_noninjective :
    collapse.operations Two.left = collapse.operations Two.right ∧ Two.left ≠ Two.right :=
  ⟨rfl, by intro h; cases h⟩

def constants : EQ.Equation (signature source) :=
  ⟨0, ctx 0, (), .app .left (fun i => i.elim0), .app .right (fun i => i.elim0)⟩
def separated : Model source :=
  ⟨fun _ => Bool, fun op _ => match op with | .left => false | .right => true⟩
def collapsed : Model target := ⟨fun _ => Bool, fun op _ => match op with | .only => false⟩

theorem constants_false : ¬ Equation.Satisfies separated (toEquation constants) := by
  intro h
  exact Bool.noConfusion (h (fun i => i.elim0))

theorem mapped_constants_true :
    Equation.Satisfies collapsed (toEquation (constants.map (signatureMap collapse))) :=
  fun _ => rfl

theorem collapse_square :
    fromModels target ⋙ EQ.Algebra.reduct (signatureMap collapse) =
      Signature.Hom.reductFunctor collapse ⋙ fromModels source := fromModels_reduct collapse

theorem sorts_fixed (S : Type) {A B : Signature S} (f : A ⟶ B) :
    (signatureMap f).sorts = id := rfl

end Silmaril.Logic.Algebraic.ManySorted.PublicEQ.Examples
