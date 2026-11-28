module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.TwoRequest.Defs
public import Mathlib.Data.Finset.Lattice.Fold

/-! # Request trees with key-indexed exact finite replies -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree

open Category.FiniteIteration
open Category.FiniteIteration.CFG.Dependent (pack)
open LambdaSSA.Region (packedExitType)
open TwoRequest (Exit Exits exit_type)

universe u

/-- A closed constructor argument can be written in any exact block context. -/
def inContext {Γ : List Syntax.Ty} : {A : Syntax.Ty} → Syntax.Expr [] A → Syntax.Expr Γ A
  | _, .var i => i.elim0
  | _, .unit => .unit
  | _, .pair a b => .pair (inContext a) (inContext b)
  | _, .inl a => .inl (inContext a)
  | _, .inr a => .inr (inContext a)

/-- The query value of a closed constructor expression. -/
def operandValue {A : Syntax.Ty} (a : Syntax.Expr [] A) : Value Unit :=
  (a.eval Syntax.emptyBindings).val

/-- The native opcode returns the packed sum of its ordered reply payload
types. Each tree node supplies its own closed operand. -/
structure RequestSignature (Φ : Type u) [HasTy Φ Syntax.Ty] where
  replies : Φ → List Syntax.Ty
  target : ∀ f, instrTrg f = packedExitType (replies f)

variable {Φ : Type u} {R : Φ → List Syntax.Ty}

/-- Each tag gets its own continuation. The empty reply list defines a
pending request with no successful branch. -/
inductive Tree [HasTy Φ Syntax.Ty] (R : Φ → List Syntax.Ty) where
  | stop (exit : Exit)
  | ask (f : Φ) (arg : Syntax.Expr [] (instrSrc f)) (arms : Fin (R f).length → Tree R)

def Tree.depth [HasTy Φ Syntax.Ty] : Tree R → Nat
  | .stop _ => 0
  | .ask _ _ arms => (Finset.univ.sup fun i => (arms i).depth) + 1

def Tree.region [HasTy Φ Syntax.Ty] (S : RequestSignature Φ) :
    Tree S.replies → {Γ : List Syntax.Ty} → Overlay.Region Φ Γ Exits
  | .stop .ub, _ => .ub
  | .stop (.ret i), _ => CFG.jump (L := Exits) i (exit_type i) .unit
  | .ask f arg arms, _ => .lsubst (CFG.Dependent.packedRequest f (inContext arg) (S.target f))
      (fun i => (arms i).region S)

/-- Compare the opcode and evaluated argument before considering inhabited
reply branches. A fault or divergence can distinguish unequal queries
even when neither has a successful reply. -/
def Tree.Refines [HasTy Φ Syntax.Ty] : Tree R → Tree R → Prop
  | .stop a, .stop b => a.Refines b
  | .ask _ _ _, .stop .ub => True
  | .ask f arg arms, .ask g arg' next => ∃ same : f = g,
      operandValue arg = operandValue arg' ∧ ∀ i,
        Nonempty (Syntax.Payload ((R f).get i)) → (arms i).Refines (next (same ▸ i))
  | _, _ => False

inductive Action (R : Φ → List Syntax.Ty) (f : Φ) (n : Nat) where
  | reply (i : Fin (R f).length) (payload : Syntax.Payload ((R f).get i)) (final : Fin n)
  | fault (final : Fin n)
  | diverge

abbrev Handler (R : Φ → List Syntax.Ty) (n : Nat) := (f : Φ) → Value Unit → Fin n → Action R f n

def RequestSignature.primitives [HasTy Φ Syntax.Ty] (S : RequestSignature Φ) {n : Nat}
    (h : Handler S.replies n) : Syntax.Primitives Φ n := fun f a s =>
  match h f a.val s with
  | .reply i a t => .ret (cast (congrArg Syntax.Payload (S.target f).symm) (pack ⟨i, a⟩)) t
  | .fault t => .fault t
  | .diverge => .diverge

abbrev RequestSignature.model [HasTy Φ Syntax.Ty] (S : RequestSignature Φ) {n : Nat} (h : Handler S.replies n) :=
  Syntax.model (S.primitives h) Syntax.emptyBindings

def Tree.execute [HasTy Φ Syntax.Ty] {n : Nat} (h : Handler R n) : Tree R → Fin n → Result 2 n
  | .stop e, s => e.result s
  | .ask f arg arms, s =>
    match h f (operandValue arg) s with
    | .reply i _ t => (arms i).execute h t
    | .fault t => .fault t
    | .diverge => .diverge

/-- Record the concrete query and typed reply at each prefix state.
The last state may fault on one opcode and argument pair. -/
inductive Prefix (R : Φ → List Syntax.Ty) : Nat → Type u
  | stop (fault : Option (Φ × Value Unit)) : Prefix R 0
  | step {n : Nat} (f : Φ) (arg : Value Unit) (i : Fin (R f).length)
      (a : Syntax.Payload ((R f).get i)) (rest : Prefix R n) : Prefix R (n + 1)

/-- Key equality and the installed constructor-value equality make a
prefix executable. No enumeration of possible argument values is used. -/
def Prefix.handler [DecidableEq Φ] : {n : Nat} → Prefix R n → Handler R (n + 1)
  | _, .stop fault => fun f a _ => if fault = some (f, a) then .fault 0 else .diverge
  | _, .step f arg i a rest => fun g input s =>
    Fin.cases
      (if same : (f, arg) = (g, input) then
        by
          have keyEq : f = g := congrArg Prod.fst same
          subst g
          exact .reply i a (Fin.succ 0)
      else .diverge)
      (fun t =>
        match rest.handler g input t with
        | .reply j b u => .reply j b u.succ
        | .fault u => .fault u.succ
        | .diverge => .diverge) s

theorem Prefix.handler_succ [DecidableEq Φ] {n : Nat} (rest : Prefix R n) (f g : Φ)
    (arg input : Value Unit) (i : Fin (R f).length) (a : Syntax.Payload ((R f).get i)) (s : Fin (n + 1)) :
    (Prefix.step f arg i a rest).handler g input s.succ =
      match rest.handler g input s with
      | .reply j b t => .reply j b t.succ
      | .fault t => .fault t.succ
      | .diverge => .diverge := rfl

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree
