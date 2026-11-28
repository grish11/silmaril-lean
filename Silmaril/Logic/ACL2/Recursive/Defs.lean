module

public import Silmaril.Logic.ACL2.Books.Defs

@[expose] public section

namespace Silmaril.Logic.ACL2.Recursive

open CategoryTheory

/-- A recursive body separates old-world terms from calls to the new block. Tests and recursive
call arguments are old-world terms. A context can combine any finite number of recursive results. -/
inductive Body (S R : Signature) (vars : Nat) where
  | base (term : Term S vars)
  | call {arity : Nat} (f : R.Symbol arity) (args : Fin arity → Term S vars)
  | apply {arity : Nat} (context : Term S arity) (args : Fin arity → Body S R vars)
  | ite (test : Term S vars) (yes no : Body S R vars)

variable {S R : Signature} {n : Nat}

abbrev Env (M : Model S) (n : Nat) := Fin n → M.primitives.Value

/-- A state identifies the callee, including its arity, and its actual arguments. -/
structure Call (R : Signature) (Value : Type) where
  arity : Nat
  symbol : R.Symbol arity
  args : Fin arity → Value

/-- All members share a natural-valued ranking, which may depend on the callee and every argument. -/
abbrev Rank (M : Model S) (R : Signature) := Call R M.primitives.Value → Nat

def Call.ofTerms (M : Model S) (env : Env M n) {k : Nat}
    (f : R.Symbol k) (args : Fin k → Term S n) : Call R M.primitives.Value :=
  ⟨k, f, fun i => (args i).eval M env⟩

/-- A property of the recursive calls on the chosen path. A context contributes all of its
argument calls. -/
def Body.CallsSatisfy (M : Model S) (env : Env M n)
    (property : Call R M.primitives.Value → Prop) : Body S R n → Prop
  | .base _ => True
  | .call f args => property (Call.ofTerms M env f args)
  | .apply _ args => ∀ i, (args i).CallsSatisfy M env property
  | .ite test yes no =>
      (test.eval M env ≠ M.primitives.nil → yes.CallsSatisfy M env property) ∧
      (test.eval M env = M.primitives.nil → no.CallsSatisfy M env property)

/-- Each recursive call compares its resulting state with the original caller. -/
abbrev Body.Decreases (M : Model S) (rank : Rank M R) (caller : Nat) (env : Env M n)
    (body : Body S R n) : Prop :=
  body.CallsSatisfy M env (fun state => rank state < caller)

/-- The evaluator can only invoke the recursive continuation at a strictly smaller state. -/
def Body.eval (M : Model S) (rank : Rank M R) (caller : Nat) (env : Env M n)
    (recur : ∀ state, rank state < caller → M.primitives.Value) :
    (body : Body S R n) → body.Decreases M rank caller env → M.primitives.Value
  | .base term, _ => term.eval M env
  | .call f args, h => recur (Call.ofTerms M env f args) h
  | .apply context args, h => context.eval M (fun i => eval M rank caller env recur (args i) (h i))
  | .ite test yes no, h =>
      if hn : test.eval M env = M.primitives.nil then eval M rank caller env recur no (h.2 hn)
      else eval M rank caller env recur yes (h.1 hn)

/-- A block of simultaneously declared, fresh functions and their typed bodies. -/
structure Block (S : Signature) where
  members : Signature
  fresh : ∀ {name k}, members.arity name = some k → S.arity name = none
  body : ∀ {k}, members.Symbol k → Body S members k

namespace Block

def signature (B : Block S) : Signature :=
  ⟨fun name => (B.members.arity name).or (S.arity name)⟩

def inclusion (B : Block S) : S ⟶ B.signature where
  preserve := by
    intro name k declared
    cases h : B.members.arity name with
    | none => simpa [signature, h] using declared
    | some _ => simp [B.fresh h] at declared

def symbol (B : Block S) {k : Nat} (f : B.members.Symbol k) : B.signature.Symbol k :=
  ⟨f.val, by simp [signature, f.property]⟩

/-- Statewise evidence for the actual definition bodies, independent of source admission and guards. -/
def Terminates (B : Block S) (M : Model S) (rank : Rank M B.members) : Prop :=
  ∀ state, (B.body state.symbol).Decreases M rank (rank state) state.args

/-- Interpret all members together by well-founded recursion on their common state space. -/
def interpret (B : Block S) (M : Model S) (rank : Rank M B.members)
    (h : B.Terminates M rank) : Call B.members M.primitives.Value → M.primitives.Value :=
  (measure rank).wf.fix fun state recur =>
    (B.body state.symbol).eval M rank (rank state) state.args recur (h state)

/-- Extend the given model with the total recursive interpretations. -/
def model (B : Block S) (M : Model S) (rank : Rank M B.members)
    (h : B.Terminates M rank) : Model B.signature where
  primitives := M.primitives
  interpret := fun {k} f args =>
    if hm : B.members.arity f.val = some k then B.interpret M rank h ⟨k, ⟨f.val, hm⟩, args⟩
    else M.interpret ⟨f.val, by
      have hf := f.property
      cases he : B.members.arity f.val <;> simp_all [signature]⟩ args

end Block

/-- The body as an ordinary ACL2 term over the extended signature. -/
def Body.toTerm (B : Block S) : Body S B.members n → Term B.signature n
  | .base term => term.map B.inclusion
  | .call f args => .app (B.symbol f) (fun i => (args i).map B.inclusion)
  | .apply context args => (context.map B.inclusion).subst (fun i => toTerm B (args i))
  | .ite test yes no => .ite (test.map B.inclusion) (toTerm B yes) (toTerm B no)

def Block.equation (B : Block S) {k : Nat} (f : B.members.Symbol k) : Sentence B.signature :=
  definitionEquation (B.symbol f) ((B.body f).toTerm B)

end Silmaril.Logic.ACL2.Recursive
