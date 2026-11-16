module

public import Silmaril.Logic.CommonLogic.Core.Defs
public import Silmaril.Logic.Institution.Examples.FirstOrder

@[expose] public section

namespace Silmaril.Logic.CommonLogic.Core.FirstOrder

open Silmaril.Logic.Institution.Examples

/-- Fixed named heads may be discourse or non-discourse objects. -/
abbrev Head (S : Signature) := Sum S.discourse S.nondiscourse

def Head.eval {S : Signature} (M : Model S) : Head S → M.Reference
  | .inl d => M.embed (M.discourse d)
  | .inr d => M.nondiscourse d

def Head.expr {S : Signature} {n k : Nat} : Head S → Expr S n k .reference
  | .inl d => .lift (.name d)
  | .inr d => .nonname d

/-- Bare individual names and nullary functional applications are separate symbols. -/
inductive Operation (S : Signature) : (n : Nat) → (Fin n → Unit) → Unit → Type where
  | name (d : S.discourse) : Operation S 0 (fun _ => ()) ()
  | apply (head : Head S) (n : Nat) : Operation S n (fun _ => ()) ()

inductive Relation (S : Signature) : (n : Nat) → (Fin n → Unit) → Type where
  | pred (head : Head S) (n : Nat) : Relation S n (fun _ => ())

abbrev signature (S : Signature) : FOL.Signature := ⟨⟨Unit, Operation S⟩, Relation S⟩

/-- The named-head, fixed-arity first-order view of a general CL model.
This construction retains nonempty discourse; arbitrary public FOL models need not be in its image. -/
def model {S : Signature} (M : Model S) : FOL.Structure (signature S) where
  carrier _ := M.Discourse
  op o := match o with
    | .name d => fun _ => M.discourse d
    | .apply h _ => fun args => M.function (h.eval M) (List.ofFn args)
  rel r := match r with
    | .pred h _ => fun args => M.relation (h.eval M) (List.ofFn args)

/-- Convert a finite argument tuple into a CL sequence without sequence markers. -/
def tuple {S : Signature} {n k : Nat} : {m : Nat} →
    (Fin m → Expr S n k .individual) → Expr S n k .sequence
  | 0, _ => .nil
  | _+1, args => .cons (args 0) (tuple (fun i => args i.succ))

/-- Embeds the named-head first-order fragment; variable sorts are uniquely Unit. -/
def term {S : Signature} {n k : Nat} {Γ : Fin n → Unit} :
    {s : Unit} → EQ.Term (signature S).toSignature Γ s → Expr S n k .individual
  | _, .var i => .var i
  | _, .app (.name d) _ => .name d
  | _, .app (.apply h _) args => .app h.expr (tuple (fun i => term (args i)))

def formula {S : Signature} : {n k : Nat} → {Γ : Fin n → Unit} →
    FOL.Formula (signature S) Γ → Formula S n k
  | _, _, _, .eq t u => .equal (term t) (term u)
  | _, _, _, .rel (.pred h _) args => .pred h.expr (tuple (fun i => term (args i)))
  | _, _, _, .tt => .tt
  | _, _, _, .not p => .neg (formula p)
  | _, _, _, .and p q => .conj (formula p) (formula q)
  | _, _, _, .all _ p => .all (formula p)

end Silmaril.Logic.CommonLogic.Core.FirstOrder
