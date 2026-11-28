module

public import Silmaril.Logic.ACL2.Thms
public import Silmaril.Logic.Institution.Examples.Equational

@[expose] public section

namespace Silmaril.Logic.ACL2.Equational

open CategoryTheory Institution.Examples

/-- Operation symbols of the one-sort equational view of an ACL2 signature. -/
inductive Op (S : Signature) : Nat → Type
  | user {n : Nat} (f : S.Symbol n) : Op S n
  | nil : Op S 0
  | truth : Op S 0
  | cons : Op S 2
  | car : Op S 1
  | cdr : Op S 1
  | consp : Op S 1
  | equal : Op S 2
  | ite : Op S 3

variable {S T : Signature} {n k : Nat}

def Op.map (σ : S ⟶ T) : Op S n → Op T n
  | .user f => .user (σ.symbol f)
  | .nil => .nil
  | .truth => .truth
  | .cons => .cons
  | .car => .car
  | .cdr => .cdr
  | .consp => .consp
  | .equal => .equal
  | .ite => .ite

def Op.term (op : Op S n) (args : Fin n → Term S k) : Term S k :=
  match op with
  | .user f => .app f args
  | .nil => .nil
  | .truth => .truth
  | .cons => .cons (args 0) (args 1)
  | .car => .car (args 0)
  | .cdr => .cdr (args 0)
  | .consp => .consp (args 0)
  | .equal => .equal (args 0) (args 1)
  | .ite => .ite (args 0) (args 1) (args 2)

def Op.eval (M : Model S) (op : Op S n) (args : Fin n → M.primitives.Value) :
    M.primitives.Value :=
  match op with
  | .user f => M.interpret f args
  | .nil => M.primitives.nil
  | .truth => M.primitives.truth
  | .cons => M.primitives.cons (args 0) (args 1)
  | .car => M.primitives.car (args 0)
  | .cdr => M.primitives.cdr (args 0)
  | .consp => M.primitives.ofBool (M.primitives.consp (args 0))
  | .equal => M.primitives.equal (args 0) (args 1)
  | .ite => M.primitives.ite (args 0) (args 1) (args 2)

def signature (S : Signature) : EQ.Signature := ⟨LogicalSort, fun n _ _ => Op S n⟩

/-- The equational view preserves every user symbol and exposes the built-in functions. -/
def signatures : Signature ⥤ EQ.Signature where
  obj := signature
  map σ := ⟨id, Op.map σ⟩
  map_id S := by
    change @EQ.Signature.Hom.mk (signature S) (signature S) id (Op.map (𝟙 S)) =
      EQ.Signature.Hom.mk id (fun op => op)
    congr
    funext n _ _ op
    cases op <;> rfl
  map_comp := fun {S _ U} σ τ => by
    change @EQ.Signature.Hom.mk (signature S) (signature U) id (Op.map (σ ≫ τ)) =
      @EQ.Signature.Hom.mk (signature S) (signature U) id (fun op => Op.map τ (Op.map σ op))
    congr
    funext n _ _ op
    cases op <;> rfl

def term {ctx : Fin k → (signature S).S} :
    {s : (signature S).S} → EQ.Term (signature S) ctx s → Term S k
  | _, .var i => .var i
  | _, .app op args => Op.term op (fun j => term (args j))

def sentence (e : EQ.Equation (signature S)) : Sentence S := .eq (term e.lhs) (term e.rhs)

def algebra (M : Model S) : EQ.Algebra (signature S) :=
  ⟨fun _ => M.primitives.Value, Op.eval M⟩

end Silmaril.Logic.ACL2.Equational
