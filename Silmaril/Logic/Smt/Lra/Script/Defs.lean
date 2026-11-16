module

public import Silmaril.Logic.Smt.Lra.Defs
public import Silmaril.Logic.Smt.SExpr.Defs

/-! Strict executable piecewise-affine Bool/Real single-query source subset. Failed
parsing is an error; only successfully decoded scripts become sentences. -/

@[expose] public section
namespace Silmaril.Logic.Smt.Lra.Script
open CategoryTheory Silmaril.Inst
abbrev Expr := Silmaril.Logic.Smt.SE
inductive SortCode where
  | real | bool
  deriving DecidableEq, BEq
structure Declaration where
  name : String
  sort : SortCode
  deriving DecidableEq
abbrev Environment := List Declaration
inductive Packed where
  | real (term : Term)
  | bool (formula : Formula)
  deriving DecidableEq

def Packed.real? : Packed → Option Term | .real t => some t | _ => none
def Packed.bool? : Packed → Option Formula | .bool p => some p | _ => none

def natural? (s : String) : Option Nat := do
  let cs := s.toList
  if cs.isEmpty || (cs.length > 1 && cs.head! == '0') then none
  else Silmaril.Logic.Smt.digits 10 Silmaril.Logic.Smt.decVal cs

def rational? (s : String) : Option ℚ :=
  let (whole, rest) := s.toList.span (fun c => c != '.')
  match rest with
  | [] => (natural? s).map (fun n => (n : ℚ))
  | _ :: fraction => do
      let n ← natural? (String.ofList whole)
      let f ← Silmaril.Logic.Smt.digits 10 Silmaril.Logic.Smt.decVal fraction
      pure ((n : ℚ) + (f : ℚ) / ((10 ^ fraction.length : Nat) : ℚ))

def validName (s : String) : Bool :=
  let initial := fun c : Char => c.isAlpha || "~!@$%^&*_-+=<>.?/".toList.contains c
  match s.toList with
  | [] => false
  | c :: cs => initial c && cs.all (fun c => initial c || c.isDigit) &&
      !["!", "_", "as", "let", "forall", "exists", "match", "par", "true", "false",
        "not", "and", "or", "=>", "xor", "=", "distinct", "ite", "+", "-", "*", "/",
        "<=", "<", ">=", ">", "Real", "Bool", "Int", "**", "div", "mod", "abs",
        "BINARY", "DECIMAL", "HEXADECIMAL", "NUMERAL", "STRING"].contains s

def sort? : Expr → Option SortCode
  | .atom "Real" => some .real
  | .atom "Bool" => some .bool
  | _ => none

def declaration? : Expr → Option Declaration
  | .list [.atom "declare-const", .atom n, s]
  | .list [.atom "declare-fun", .atom n, .list [], s] => do
      if !validName n then none else pure ⟨n, ← sort? s⟩
  | _ => none

def declarations? : List Expr → Option Environment
  | [] => some []
  | e :: es => do
      let d ← declaration? e
      let rest ← declarations? es
      if rest.any (fun x => x.name == d.name) then none else pure (d :: rest)

def plus (a b : Packed) : Option Packed := do
  pure (.real (.add (← a.real?) (← b.real?)))
def minus (a b : Packed) : Option Packed := do
  pure (.real (.add (← a.real?) (.neg (← b.real?))))
def multiply (a b : Packed) : Option Packed :=
  match a, b with
  | .real (.literal a), .real (.literal b) => some (.real (.literal (a * b)))
  | .real (.literal a), .real b => some (.real (.scale a b))
  | .real a, .real (.literal b) => some (.real (.scale b a))
  | _, _ => none

def binary (op : String) (a b : Packed) : Option Packed :=
  match op with
  | "+" => plus a b
  | "-" => minus a b
  | "*" => multiply a b
  | "/" => do
      let .literal q ← b.real? | none
      if q = 0 then none else
        let t ← a.real?
        pure (.real (match t with | .literal p => .literal (p / q) | t => .scale (1 / q) t))
  | "=" => match a, b with
      | .real a, .real b => some (.bool (.equal a b))
      | .bool a, .bool b => some (.bool (.iff a b))
      | _, _ => none
  | "distinct" => match a, b with
      | .real a, .real b => some (.bool (.not (.equal a b)))
      | .bool a, .bool b => some (.bool (.not (.iff a b)))
      | _, _ => none
  | "<=" => do pure (.bool (.le (← a.real?) (← b.real?)))
  | "<" => do pure (.bool (.lt (← a.real?) (← b.real?)))
  | ">=" => do pure (.bool (.le (← b.real?) (← a.real?)))
  | ">" => do pure (.bool (.lt (← b.real?) (← a.real?)))
  | "and" => do pure (.bool (.and (← a.bool?) (← b.bool?)))
  | "or" => do pure (.bool (.or (← a.bool?) (← b.bool?)))
  | "=>" => do pure (.bool (.or (.not (← a.bool?)) (← b.bool?)))
  | "xor" => do pure (.bool (.not (.iff (← a.bool?) (← b.bool?))))
  | _ => none

/-- Conditional branches must have the same sort and the guard must be Boolean.
Boolean conditionals elaborate into existing connectives; Real conditionals retain their tree. -/
def conditional (guard yes no : Packed) : Option Packed := do
  let g ← guard.bool?
  match yes, no with
  | .real a, .real b => pure (.real (.ite g a b))
  | .bool a, .bool b => pure (.bool (.or (.and g a) (.and (.not g) b)))
  | _, _ => none

def apply? (op : String) : List Packed → Option Packed
  | [a] => match op with
      | "-" => do
          let t ← a.real?
          pure (.real (match t with | .literal q => .literal (-q) | t => .neg t))
      | "not" => do pure (.bool (.not (← a.bool?)))
      | _ => none
  | [a, b] => binary op a b
  | a :: b :: rest =>
      if op == "ite" then
        match rest with
        | [c] => conditional a b c
        | _ => none
      else if ["+", "-", "*", "and", "or"].contains op then do
        rest.foldlM (binary op) (← binary op a b)
      else none
  | _ => none

def decodeFuel? (E : Environment) : Nat → Expr → Option Packed
  | 0, _ => none
  | _ + 1, .atom s =>
      if s == "true" then some (.bool (.boolean true))
      else if s == "false" then some (.bool (.boolean false))
      else match rational? s with
        | some q => some (.real (.literal q))
        | none => do
            let d ← E.find? (fun d => d.name == s)
            pure (match d.sort with | .real => .real (.variable s) | .bool => .bool (.variable s))
  | fuel + 1, .list (.atom op :: args) => do
      apply? op (← args.mapM (decodeFuel? E fuel))
  | _, _ => none

mutual
 def expressionFuel : Expr → Nat
  | .atom _ => 1
  | .list xs => expressionsFuel xs + 1
 def expressionsFuel : List Expr → Nat
  | [] => 0
  | e :: es => expressionFuel e + expressionsFuel es
end

def decode? (E : Environment) (e : Expr) : Option Packed := decodeFuel? E (expressionFuel e) e
def formula? (E : Environment) (e : Expr) : Option Formula := decode? E e >>= Packed.bool?

structure Sentence where
  environment : Environment
  assertions : Problem
  deriving DecidableEq

def isDeclaration : Expr → Bool
  | .list (.atom "declare-const" :: _) | .list (.atom "declare-fun" :: _) => true
  | _ => false

def assertionCommands? : List Expr → Option (List Expr)
  | [.list [.atom "check-sat"]] | [.list [.atom "check-sat"], .list [.atom "exit"]] => some []
  | .list [.atom "assert", e] :: rest => (assertionCommands? rest).map (e :: ·)
  | _ => none

def decodeBody? (forms : List Expr) : Option Sentence := do
  let E ← declarations? (forms.takeWhile isDeclaration)
  let assertions ← assertionCommands? (forms.dropWhile isDeclaration)
  pure ⟨E, ← assertions.mapM (formula? E)⟩

def decodeForms? : List Expr → Option Sentence
  | .list [.atom "set-logic", .atom "QF_LRA"] :: rest => decodeBody? rest
  | _ => none

def parse? (text : String) : Option Sentence :=
  Silmaril.Logic.Smt.readForms text.toUTF8.data.toList >>= decodeForms?

structure Accepted where
  text : String
  sentence : Sentence
  parsed : parse? text = some sentence

def accept? (text : String) : Option Accepted :=
  match h : parse? text with
  | none => none
  | some s => some ⟨text, s, h⟩

noncomputable def TextHolds (text : String) (M : Model) : Prop :=
  ∃ s, parse? text = some s ∧ s.assertions.Holds M
noncomputable def Accepted.Holds (s : Accepted) (M : Model) : Prop := TextHolds s.text M
noncomputable def Accepted.Sat (s : Accepted) : Prop := ∃ M, s.Holds M
noncomputable def Accepted.Unsat (s : Accepted) : Prop := ¬ s.Sat
noncomputable def Accepted.Entails (s : Accepted) (p : Formula) : Prop :=
  ∀ M, s.Holds M → p.Holds M

noncomputable def plain : Plain (Disc Unit) where
  Sen _ := Accepted
  map _ := id
  map_id _ _ := rfl
  map_comp _ _ _ := rfl
  Mod _ := Model
  reduct _ := id
  reduct_id _ _ := rfl
  reduct_comp _ _ _ := rfl
  Sat M s := s.Holds M
  sat_map _ _ _ := Iff.rfl
noncomputable abbrev institution := plain.toInst
noncomputable abbrev room := plain.room ()
end Silmaril.Logic.Smt.Lra.Script
