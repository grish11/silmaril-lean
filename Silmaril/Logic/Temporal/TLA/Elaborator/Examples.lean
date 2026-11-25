module

import all Silmaril.Logic.Temporal.TLA.Elaborator.Defs
import Silmaril.Logic.Temporal.TLA.Elaborator.Thms
import Silmaril.Logic.Temporal.TLA.Kernel.Thms

/-! Handwritten surface trees for the pinned Quint exports and additional checks.
`import all` permits kernel reduction of the elaborator for these closed tests. -/

namespace Silmaril.Logic.Temporal.TLA.Elaborator.Examples

open Surface (Expr Ident Module ModuleUnit)

private def ref (name : Ident) : Expr := .ref (.operator (.ident name)) [] []
private def nat (n : Nat) : Expr := .literal (.natural n)
private def bin (op : String) (lhs rhs : Expr) : Expr := .infix (.symbol op) lhs rhs
private def prime (expr : Expr) : Expr := .postfix .prime expr
private def defn (name : Ident) (body : Expr) : ModuleUnit :=
  .definition (.operator .ordinary (.ident name []) body)

private def exports : List StandardModule := [.integers, .sequences, .finiteSets, .tlc, .apalache, .variants]

private def observe {signature : Signature} {Node : Type}
    (checked : Except Diagnostic (CheckedModule signature)) (domain : Kernel.Bounded signature.scope Node)
    (init step : Ident) : Option (List Node × List (Node × Node)) :=
  (do
    let checked ← checked
    let init ← checked.statePredicate init
    let step ← checked.stepPredicate step
    return (domain.initials signature.noRigid init, domain.transitions signature.noRigid step)).toOption

private def intState (signature : Signature) (value : Ident → Int) : Kernel.State signature.scope
  | .int, name => value name.val
  | .bool, _ => false

namespace BoundedCounter

private def source : Module where
  name := "BoundedCounter"
  extendsModules := ["Integers", "Sequences", "FiniteSets", "TLC", "Apalache", "Variants"]
  units :=
    [ .variables ["n"],
      defn "step" (bin "/\\" (bin "<" (ref "n") (nat 2))
        (bin ":=" (prime (ref "n")) (bin "+" (ref "n") (nat 1)))),
      defn "init" (bin "=" (ref "n") (nat 0)),
      defn "q_init" (ref "init"), defn "q_step" (ref "step") ]

private def signature : Signature := [("n", .int)]
private def state (n : Int) : Kernel.State signature.scope := intState signature (fun _ => n)
private def domain : Kernel.Bounded signature.scope Int := ⟨[0, 1, 2], state⟩
private def checked := elaborate exports signature source

example : observe checked domain "q_init" "q_step" = some ([0], [(0, 1), (1, 2)]) := by decide

example (n : Int) :
    (match checked.bind (·.stateDenotation "q_init") with
     | .ok init => init.eval signature.noRigid (state n)
     | .error _ => False) ↔ n = 0 := Iff.rfl

example (n m : Int) :
    (match checked >>= (·.actionDenotation "q_step") with
     | .ok step => step signature.noRigid (state n) (state m)
     | .error _ => False) ↔ n < 2 ∧ m = n + 1 := Iff.rfl

-- The computed lists agree with the elaborated General TLA denotations on the given domain.
example (n m : Int) :
    (n ∈ [0] ↔ n ∈ domain.states ∧ n = 0) ∧
    ((n, m) ∈ [(0, 1), (1, 2)] ↔ n ∈ domain.states ∧ m ∈ domain.states ∧ n < 2 ∧ m = n + 1) := by
  have initial := domain.mem_initials signature.noRigid
    ((checked >>= (·.statePredicate "q_init")).toOption.get (by decide)) n
  have transition := domain.mem_transitions signature.noRigid
    ((checked >>= (·.stepPredicate "q_step")).toOption.get (by decide)) n m
  exact ⟨initial, transition⟩

end BoundedCounter

namespace BitPair

private def source : Module where
  name := "BitPair"
  extendsModules := ["Integers", "Sequences", "FiniteSets", "TLC", "Apalache", "Variants"]
  units :=
    [ .variables ["x"], .variables ["y"],
      defn "init" (bin "/\\" (bin "=" (ref "x") (nat 0)) (bin "=" (ref "y") (nat 1))),
      defn "step" (.rigidQuant .exists (.bounded [⟨.names ["flip"], .setEnum [ref "FALSE", ref "TRUE"]⟩])
        (bin "/\\" (bin ":=" (prime (ref "x")) (ref "y"))
          (bin ":=" (prime (ref "y")) (.ifThenElse (ref "flip") (bin "-" (nat 1) (ref "x")) (ref "x"))))),
      defn "q_init" (ref "init"), defn "q_step" (ref "step") ]

private def signature : Signature := [("x", .int), ("y", .int)]
private def state (point : Int × Int) : Kernel.State signature.scope :=
  intState signature (fun name => if name == "x" then point.1 else point.2)
private def domain : Kernel.Bounded signature.scope (Int × Int) :=
  ⟨[(0, 0), (0, 1), (1, 0), (1, 1)], state⟩
private def checked := elaborate exports signature source

example : observe checked domain "q_init" "q_step" = some
    ([(0, 1)],
     [((0, 0), (0, 0)), ((0, 0), (0, 1)),
      ((0, 1), (1, 0)), ((0, 1), (1, 1)),
      ((1, 0), (0, 0)), ((1, 0), (0, 1)),
      ((1, 1), (1, 0)), ((1, 1), (1, 1))]) := by decide

-- Both right-hand sides use the source, for arbitrary integers as well as bits.
example (x y x' y' : Int) :
    (match checked >>= (·.actionDenotation "q_step") with
     | .ok step => step signature.noRigid (state (x, y)) (state (x', y'))
     | .error _ => False) ↔ x' = y ∧ (y' = x ∨ y' = 1 - x) := by
  change (∃ flip ∈ [false, true], x' = y ∧ y' = (if flip = true then 1 - x else x)) ↔ _
  constructor
  · rintro ⟨flip, _, hx, hy⟩
    cases flip
    · exact ⟨hx, .inl hy⟩
    · exact ⟨hx, .inr hy⟩
  · rintro ⟨hx, hy | hy⟩
    · exact ⟨false, by simp, hx, hy⟩
    · exact ⟨true, by simp, hx, hy⟩

end BitPair

namespace Toggle

-- This module uses Boolean variables and primes a whole state-level alias.
private def source : Module := ⟨"Toggle", [],
  [ .variables ["flag", "other"],
    defn "Init" (.prefix .negation (ref "flag")),
    defn "View" (.ifThenElse (ref "flag") (ref "FALSE") (ref "TRUE")),
    defn "Next" (bin "=" (prime (ref "View")) (ref "flag")) ]⟩

private def signature : Signature := [("flag", .bool), ("other", .bool)]
private def state (point : Bool × Bool) : Kernel.State signature.scope
  | .bool, name => if name.val == "flag" then point.1 else point.2
  | .int, _ => (0 : Int)
private def domain : Kernel.Bounded signature.scope (Bool × Bool) :=
  ⟨[(false, false), (false, true), (true, false), (true, true)], state⟩

-- The other variable is free at each successor.
example : observe (elaborate [] signature source) domain "Init" "Next" = some
    ([(false, false), (false, true)],
     [((false, false), (true, false)), ((false, false), (true, true)),
      ((false, true), (true, false)), ((false, true), (true, true)),
      ((true, false), (false, false)), ((true, false), (false, true)),
      ((true, true), (false, false)), ((true, true), (false, true))]) := by decide

end Toggle

namespace Rejections

private def diagnostic {α : Type} : Except Diagnostic α → Option Diagnostic
  | .error e => some e
  | .ok _ => none

private def check (units : List ModuleUnit) (signature : Signature := []) (extendsModules : List Ident := []) :=
  elaborate exports signature ⟨"Rejections", extendsModules, units⟩

example : diagnostic (check [] [] ["Unresolved"]) = some (.unresolvedImport "Unresolved") := by decide
example : diagnostic (elaborate [] [] ⟨"M", ["Apalache"], []⟩) =
    some (.unresolvedImport "Apalache") := by decide
example : diagnostic (check [] [] ["Integers", "Integers"]) = some (.duplicateImport "Integers") := by decide
example : diagnostic (check [.variables ["x"]]) = some (.missingSort "x") := by decide
example : diagnostic (check [] [("x", .bool)]) = some (.unexpectedSort "x") := by decide
example : diagnostic (check [.variables ["x"]] [("x", .int), ("x", .bool)]) =
    some (.duplicateSort "x") := by decide
example : diagnostic (check [defn "P" (ref "TRUE"), defn "P" (ref "FALSE")]) =
    some (.conflictingName "P") := by decide
example : diagnostic (check [defn "Len" (nat 0)] [] ["Sequences"]) = some (.conflictingName "Len") := by decide
example : diagnostic (check [defn "P" (ref "Later"), defn "Later" (ref "TRUE")]) =
    some (.inDefinition "P" (.unknownName "Later")) := by decide
example : diagnostic (check [defn "P" (.ref (.operator (.ident "TRUE")) [.expr (nat 0)] [])]) =
    some (.inDefinition "P" (.arityMismatch "TRUE" 0 1)) := by decide
example : diagnostic (check [defn "P" (bin "=" (nat 0) (ref "FALSE"))]) =
    some (.inDefinition "P" (.typeMismatch .int .bool)) := by decide
example : diagnostic (check [defn "P" (bin ":=" (prime (ref "TRUE")) (ref "FALSE"))]) =
    some (.inDefinition "P" (.requiresImport ":=" .apalache)) := by decide
example : diagnostic (check [defn "P" (bin "::=" (prime (ref "TRUE")) (ref "FALSE"))] [] ["Apalache"]) =
    some (.inDefinition "P" (.unsupportedOperator "::=")) := by decide
example : diagnostic (check [defn "P" (bin "+" (nat 0) (nat 1))] [] ["Apalache"]) =
    some (.inDefinition "P" (.requiresImport "+" .integers)) := by decide
example : diagnostic (check [defn "P" (prime (ref "TRUE")), defn "Q" (prime (ref "P"))]) =
    some (.inDefinition "Q" .primeOfAction) := by decide
example : diagnostic (check [defn "P" (prime (ref "TRUE"))] >>= (·.statePredicate "P")) =
    some (.actionInState "P") := by decide
example : diagnostic (check [defn "P" (nat 0)] >>= (·.stepPredicate "P")) =
    some (.typeMismatch .bool .int) := by decide
example : diagnostic (check [defn "P" (.rigidQuant .exists
      (.bounded [⟨.names ["TRUE"], .setEnum [ref "FALSE"]⟩]) (ref "TRUE"))]) =
    some (.inDefinition "P" (.conflictingName "TRUE")) := by decide
example : diagnostic (check [defn "P" (.rigidQuant .exists
      (.bounded [⟨.names ["v"], .setEnum [ref "FALSE", nat 0]⟩]) (ref "v"))]) =
    some (.inDefinition "P" (.typeMismatch .bool .int)) := by decide
example : diagnostic (check [defn "P" (.action .square (ref "TRUE") (nat 0))]) =
    some (.inDefinition "P" (.unsupportedExpression "action bracket")) := by decide
example : diagnostic (check [defn "P" (.fairness .weak (nat 0) (ref "TRUE"))]) =
    some (.inDefinition "P" (.unsupportedExpression "fairness")) := by decide
example : diagnostic (check [defn "P" (bin ":=" (nat 1) .oldValue)] [] ["Apalache"]) =
    some (.inDefinition "P" (.unsupportedExpression "EXCEPT or @")) := by decide
example : diagnostic (check [defn "Init" (ref "TRUE"), .assumption none (ref "FALSE")]) =
    some (.unsupportedDeclaration "ASSUME") := by decide
example : diagnostic (check [.definition (.operator .ordinary (.ident "P" [.ident "x" 0]) (ref "x"))]) =
    some (.unsupportedDeclaration "definition other than a nullary identifier operator") := by decide

-- Apalache's operator admits ordinary scalar equality even without a primed left-hand side.
example : ((check [defn "P" (bin ":=" (nat 0) (nat 1))] [] ["Apalache"] >>= (·.statePredicate "P")).map
    (fun p => p.check (Signature.noRigid []) (intState [] (fun _ => 0)))).toOption = some false := by decide

end Rejections

end Silmaril.Logic.Temporal.TLA.Elaborator.Examples
