module

public import Silmaril.Logic.Separation.FirstOrder.Examples

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Separation.FirstOrder.Examples
open CategoryTheory Silmaril.Logic.Institution.Examples

inductive UnaryOp : (n : Nat) → (Fin n → Unit) → Unit → Type where
  | a : UnaryOp 1 (ctx 1) ()
  | b : UnaryOp 1 (ctx 1) ()

inductive UnaryRel : (n : Nat) → (Fin n → Unit) → Type where
  | p : UnaryRel 1 (ctx 1)
  | q : UnaryRel 1 (ctx 1)

def symbols : FixedSignature Unit := ⟨UnaryOp, UnaryRel⟩

/-- A signature arrow identifying distinct function and relation symbols. -/
def identify : symbols ⟶ symbols where
  operations o := by cases o; exact .a; exact .a
  relations r := by cases r; exact .p; exact .p

def symbolModel : FOL.Structure symbols.fol where
  carrier := fun _ => Bool
  op o args := by
    cases o with
    | a => exact !(args 0)
    | b => exact args 0
  rel r args := by
    cases r with
    | p => exact args 0 = true
    | q => exact args 0 = false

def query : Atom symbols.fol :=
  .rel (ctx 1) UnaryRel.q (fun _ => .app UnaryOp.b (fun _ => .var 0))

theorem mapped_query : atomMap identify query =
    Atom.rel (A := symbols.fol) (ctx 1) UnaryRel.p
      (fun _ => EQ.Term.app UnaryOp.a (fun _ => .var 0)) := rfl

/-- The mapped function is evaluated and its mapped relation tested independently. -/
theorem mapped_query_native : singleton 0 (⟨(),false⟩ : Value symbolModel) ∈
    atom symbolModel (atomMap identify query) := by
  refine ⟨fun _ => false, ?_, rfl⟩
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

theorem original_query_native : singleton 0 (⟨(),false⟩ : Value symbolModel) ∈
    atom symbolModel query := by
  refine ⟨fun _ => false, ?_, rfl⟩
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

theorem symbol_reduct_exact :
    native ((FOL.Structure.reduct identify.fol).obj symbolModel) =
      Separation.reduct (atomMap identify) (native symbolModel) :=
  native_reduct identify symbolModel

end Silmaril.Logic.Separation.FirstOrder.Examples
