module

public import Silmaril.Logic.Egg.Core.Explanation
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Fin

@[expose] public section
namespace Silmaril.Logic.Egg.Core.Flat
open Silmaril.Logic.Institution.Examples

/-- A ranked, single-sorted signature. Names are the actual operator data, not
an untrusted map from printed aliases to unrelated typed operators. -/
abbrev signature : Signature := ⟨Unit, fun _ _ _ => String⟩
abbrev context (n : Nat) : Fin n → signature.S := fun _ => ()
abbrev Term (n : Nat) := EQ.Term signature (context n) ()

/-- Fix the unique sort profile explicitly, including for nullary operators. -/
def node {n k : Nat} (name : String) (args : Fin k → Term n) : Term n :=
  .app (w := context k) name args

theorem node_ext {n k : Nat} {name : String} {a b : Fin k → Term n}
    (h : ∀ i, a i = b i) : node name a = node name b := congrArg (node name) (funext h)

/-- An exposed finite enumeration for kernel reduction of source bytes. -/
def listFn {α : Type} : {k : Nat} → (Fin k → α) → List α
  | 0, _ => []
  | k+1, f => f 0 :: listFn (fun i : Fin k => f i.succ)

def joinWith (sep : String) : List String → String
  | [] => ""
  | [x] => x
  | x :: y :: xs => x ++ sep ++ joinWith sep (y :: xs)

/-- Decimal variable indices without an opaque imported string formatter. -/
def digit : Nat → String
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
  | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"

def decimalAux : Nat → Nat → String
  | 0, _ => ""
  | fuel+1, n => if n < 10 then digit n else decimalAux fuel (n / 10) ++ digit (n % 10)

def decimal (n : Nat) : String := decimalAux (n+1) n

/-- Canonical pattern variables have distinct spellings ?v0, ?v1, ... . -/
def render {n : Nat} : {s : signature.S} → EQ.Term signature (context n) s → String
  | _, .var i => "?v" ++ decimal i.val
  | _, .app name args =>
    match listFn (fun i => render (args i)) with
    | [] => name
    | xs => "(" ++ name ++ " " ++ joinWith " " xs ++ ")"

def symbols {n : Nat} : {s : signature.S} → EQ.Term signature (context n) s → List (String × Nat)
  | _, .var _ => []
  | _, .app (n := k) name args => (name, k) :: (listFn (fun i => symbols (args i))).flatten

/-- Occurrences in the typed pattern. Requiring every scope variable in the LHS
prevents an invisible unused binder from changing rule meaning on empty carriers. -/
def variableIndices {n : Nat} : {s : signature.S} → EQ.Term signature (context n) s → List Nat
  | _, .var i => [i.val]
  | _, .app _ args => (listFn (fun i => variableIndices (args i))).flatten

/-- Operators/rules are simple unquoted atoms; reserved annotations and variable
spellings cannot be overloaded. Whitespace variants are deliberately rejected. -/
def atomValid (s : String) : Bool :=
  !s.isEmpty && s.toList.head? != some '?' && s != "Rewrite=>" && s != "Rewrite<=" &&
    s.toList.all (fun c => !c.isWhitespace && c != '(' && c != ')' && c != '"')

def symbolsValid (xs : List (String × Nat)) : Bool :=
  xs.all (fun x => atomValid x.1 && xs.all (fun y => x.1 != y.1 || x.2 == y.2))

structure NamedRule where
  name : String
  rule : Rule signature

namespace NamedRule

def render (r : NamedRule) : String :=
  "(rule " ++ r.name ++ " " ++ Flat.render r.rule.conclusion.lhs ++ " " ++
    Flat.render r.rule.conclusion.rhs ++ ")\n"

def symbols (r : NamedRule) : List (String × Nat) :=
  Flat.symbols r.rule.conclusion.lhs ++ Flat.symbols r.rule.conclusion.rhs

end NamedRule

def ruleText (rs : List NamedRule) : String := joinWith "" (rs.map NamedRule.render)
def ruleSet (rs : List NamedRule) : Set (Rule signature) := {r | ∃ x ∈ rs, x.rule = r}

def tableValid (rs : List NamedRule) : Bool :=
  (rs.map NamedRule.name).eraseDups.length == rs.length &&
  rs.all (fun r => atomValid r.name && r.rule.guards.isEmpty &&
    (List.range r.rule.scope).all (fun i => (variableIndices r.rule.conclusion.lhs).contains i) &&
    ((List.range r.rule.scope).map decimal).eraseDups.length == r.rule.scope) &&
  symbolsValid ((rs.map NamedRule.symbols).flatten)

/-- Typed candidate replay. Every rule reference selects a member of the whole
bound table. Guarded raw rewrites are unsupported, rather than trusted. -/
inductive Step (rs : List NamedRule) {n : Nat} : Term n → Term n → Type where
  | refl (t : Term n) : Step rs t t
  | congr (name : String) {k : Nat} (a b : Fin k → Term n)
      (children : ∀ i, Step rs (a i) (b i)) :
      Step rs (.app name a) (.app name b)
  | forward (r : NamedRule) (member : r ∈ rs)
      (δ : Fin r.rule.scope → Term n) (unguarded : r.rule.guards = [])
      (a b : Term n)
      (source : Pattern.instantiate δ r.rule.conclusion.lhs = a)
      (target : Pattern.instantiate δ r.rule.conclusion.rhs = b) : Step rs a b
  | backward (r : NamedRule) (member : r ∈ rs)
      (δ : Fin r.rule.scope → Term n) (unguarded : r.rule.guards = [])
      (a b : Term n)
      (source : Pattern.instantiate δ r.rule.conclusion.rhs = a)
      (target : Pattern.instantiate δ r.rule.conclusion.lhs = b) : Step rs a b

namespace Step
variable {rs : List NamedRule} {n : Nat} {a b : Term n}

def render : {a b : Term n} → Step rs a b → String
  | _, _, .refl t => Flat.render t
  | _, _, .congr name _ _ cs =>
    match listFn (fun i => render (cs i)) with
    | [] => name
    | xs => "(" ++ name ++ " " ++ joinWith " " xs ++ ")"
  | _, _, .forward r _ _ _ _ b _ _ => "(Rewrite=> " ++ r.name ++ " " ++
      Flat.render b ++ ")"
  | _, _, .backward r _ _ _ _ b _ _ => "(Rewrite<= " ++ r.name ++ " " ++
      Flat.render b ++ ")"

/-- No imported assertion or rule-name oracle enters the existing certificate. -/
theorem certificate : {a b : Term n} → Step rs a b → Explanation (ruleSet rs) ∅ a b
  | _, _, .refl t => .refl t
  | _, _, .congr name a b cs => .congr name a b (fun i => certificate (cs i))
  | _, _, .forward r member δ h _ _ source target => by
    rw [← source, ← target]
    exact .rewrite r.rule (show r.rule ∈ ruleSet rs from ⟨r, member, rfl⟩) δ
      (by intro e he; rw [h] at he; cases he)
  | _, _, .backward r member δ h _ _ source target => by
    rw [← source, ← target]
    exact .symm (.rewrite r.rule (show r.rule ∈ ruleSet rs from ⟨r, member, rfl⟩) δ
      (by intro e he; rw [h] at he; cases he))

end Step

inductive Trace (rs : List NamedRule) : Term 0 → Term 0 → Type where
  | done (a : Term 0) : Trace rs a a
  | cons {a b c : Term 0} (step : Step rs a b) (tail : Trace rs b c) : Trace rs a c

namespace Trace
variable {rs : List NamedRule} {a b : Term 0}

def lines : {a b : Term 0} → Trace rs a b → String
  | _, _, .done _ => ""
  | _, _, .cons step tail => step.render ++ "\n" ++ lines tail

def render (t : Trace rs a b) : String := Flat.render a ++ "\n" ++ t.lines

def symbols : {a b : Term 0} → Trace rs a b → List (String × Nat)
  | _, _, .done a => Flat.symbols a
  | _, _, .cons (b := b) _ tail => Flat.symbols b ++ symbols tail

theorem certificate : {a b : Term 0} → Trace rs a b → Explanation (ruleSet rs) ∅ a b
  | _, _, .done a => .refl a
  | _, _, .cons step tail => .trans step.certificate tail.certificate

end Trace

/-- Exact, complete source binding. A generated candidate is accepted only after
kernel checks of the entire trace, rule templates, both endpoint files, names,
consistent arities and the unsupported-guard boundary. No hashing oracle is used. -/
structure Replay (rs : List NamedRule) (a b : Term 0)
    (proofText rulesText startText endText : String) where
  trace : Trace rs a b
  proof_eq : trace.render = proofText
  rules_eq : ruleText rs = rulesText
  start_eq : render a ++ "\n" = startText
  end_eq : render b ++ "\n" = endText
  table_valid : tableValid rs = true
  symbols_valid : symbolsValid
    (symbols a ++ trace.symbols ++ (rs.map NamedRule.symbols).flatten) = true

end Silmaril.Logic.Egg.Core.Flat
