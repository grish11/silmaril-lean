module

public import Silmaril.Logic.ACL2.Recursive.Defs

@[expose] public section

namespace Silmaril.Logic.ACL2.Recursive

variable {S R : Signature} {n : Nat}

/-- The carrier supplies the measure law. This interface is independent of the representation of
ACL2 values and does not require guards or assume termination of a user function. -/
structure CdrSize (P : Primitives) where
  size : P.Value → Nat
  cdr_lt : ∀ x, P.consp x = true → size (P.cdr x) < size x

abbrev MeasureArgument (R : Signature) := ∀ {k}, R.Symbol k → Fin k

def CdrSize.rank {M : Model S} (size : CdrSize M.primitives) (arg : MeasureArgument R) :
    Rank M R :=
  fun state => size.size (state.args (arg state.symbol))

/-- Each branch records the original test and whether the path requires it to be non-NIL. -/
abbrev Path (S : Signature) (n : Nat) := List (Term S n × Bool)

def Path.Holds (path : Path S n) (M : Model S) (env : Env M n) : Prop :=
  ∀ fact ∈ path, if fact.2 then fact.1.eval M env ≠ M.primitives.nil
    else fact.1.eval M env = M.primitives.nil

/-- The certificate covers every subbody. At a recursive call, `cdr` identifies a positive
`consp` fact by its index in the path, counting from the innermost branch. -/
inductive Certificate where
  | base
  | cdr (guard : Nat)
  | apply (args : List Certificate)
  | ite (yes no : Certificate)
  deriving Repr

def checkCdr (caller : Fin n) (argument : Term S n) (fact : Term S n × Bool) : Bool :=
  match argument, fact with
  | .cdr (.var i), (.consp (.var j), true) => i == caller && j == caller
  | _, _ => false

/-- Check a certificate against the actual body and argument positions. The checker constructs
the path from the body. The certificate supplies only the selected fact's index. -/
def Certificate.check (arg : MeasureArgument R) (caller : Fin n) (path : Path S n) :
    Body S R n → Certificate → Bool
  | .base _, .base => true
  | .call f args, .cdr guard =>
      (path[guard]?).any (checkCdr caller (args (arg f)))
  | .apply (arity := k) _ args, .apply certs =>
      certs.length == k && (List.finRange k).all fun i =>
        (certs[i.val]?).any (check arg caller path (args i))
  | .ite test yes no, .ite cy cn =>
      check arg caller ((test, true) :: path) yes cy &&
        check arg caller ((test, false) :: path) no cn
  | _, _ => false

/-- A block certificate provides a certificate for each declared member. -/
abbrev BlockCertificate (B : Block S) := ∀ {k}, B.members.Symbol k → Certificate

def BlockCertificate.Accepted (B : Block S) (arg : MeasureArgument B.members)
    (cert : BlockCertificate B) : Prop :=
  ∀ {k} (f : B.members.Symbol k), (cert f).check arg (arg f) [] (B.body f) = true

end Silmaril.Logic.ACL2.Recursive
