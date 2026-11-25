module

import Lean.Data.Json
public import Silmaril.Logic.Temporal.TLA.Import.Defs
import Silmaril.Logic.Temporal.TLA.Kernel.Thms
meta import Silmaril.Logic.Temporal.TLA.Import.Defs

open Lean Silmaril.Logic.Temporal.TLA
open Silmaril.Logic.Temporal.TLA.Import

deriving instance Repr for Kernel.Scalar, Elaborator.Diagnostic, Import.Diagnostic

private def fixtures : System.FilePath := "tests/semantics/tla-quint"

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def requireOk {ε α : Type} [Repr ε] (context : String) : Except ε α → IO α
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"{context}: {reprStr cause}")

private def readModule (profile : Profile) (file : System.FilePath) :
    IO (StateAction profile.signature) := do
  let source ← IO.FS.readFile file
  requireOk file.toString (importModule profile source)

private structure Oracle where
  variables : List String
  states : List (List Int)
  initial : List (List Int)
  transitions : List (List Int × List Int)
  deriving FromJson

private def intValuation (signature : Elaborator.Signature) (variables : List String)
    (row : List Int) : Kernel.State signature.scope :=
  let values := variables.zip row
  -- The fixture checks ensure every Int name has a value and no Bool names occur.
  fun
    | .int, name => (values.lookup name.val).getD 0
    | .bool, _ => false

private def checkGraph {signature : Elaborator.Signature} {Node : Type} [BEq Node] [Repr Node]
    (label : String) (imported : StateAction signature) (domain : Kernel.Bounded signature.scope Node)
    (expectedInitial : List Node) (expectedSteps : List (Node × Node)) : IO Unit := do
  let ρ := signature.noRigid
  -- Certify the computed lists against their General TLA meanings on this domain.
  let initial : {nodes : List Node // ∀ n, n ∈ nodes ↔
      n ∈ domain.states ∧ imported.initial.toStatePred.eval ρ (domain.valuation n)} :=
    ⟨domain.initials ρ imported.initial, domain.mem_initials ρ imported.initial⟩
  let steps : {edges : List (Node × Node) // ∀ s t, (s, t) ∈ edges ↔
      s ∈ domain.states ∧ t ∈ domain.states ∧
        imported.step.toAction ρ (domain.valuation s) (domain.valuation t)} :=
    ⟨domain.transitions ρ imported.step, domain.mem_transitions ρ imported.step⟩
  check (initial.val.isPerm expectedInitial)
    s!"{label}: initial states {reprStr initial.val}, expected {reprStr expectedInitial}"
  check (steps.val.isPerm expectedSteps)
    s!"{label}: transitions {reprStr steps.val}, expected {reprStr expectedSteps}"
  IO.println s!"{label}: {domain.states.length} states, {initial.val.length} initial, \
    {domain.states.length ^ 2} ordered pairs, {steps.val.length} transitions"

private def checkExport (name : String) (signature : Elaborator.Signature) (oracle : Oracle) :
    IO (StateAction signature × Kernel.Bounded signature.scope (List Int)) := do
  check ((oracle.variables.map (·, Kernel.Scalar.int)).isPerm signature)
    s!"{name}: oracle variable columns disagree with the signature"
  check (oracle.states.all (fun row => row.length == oracle.variables.length))
    s!"{name}: a state row disagrees with the oracle variable columns"
  let imported ← readModule (.quintApalache0624 signature) (fixtures / s!"{name}.tla")
  let domain := ⟨oracle.states, intValuation signature oracle.variables⟩
  checkGraph s!"{name} raw" imported domain oracle.initial oracle.transitions
  return (imported, domain)

private def counterSignature : Elaborator.Signature := [("n", .int)]

private def checkCounterBracket (imported : StateAction counterSignature)
    (domain : Kernel.Bounded counterSignature.scope (List Int)) (oracle : Oracle) : IO Unit := do
  -- This observation reads the counter's sole state coordinate.
  let observe := Kernel.Term.flex (Γ := counterSignature.scope) (a := .int) ⟨"n", rfl⟩
  let bracketed := { imported with step := imported.step.bracket observe }
  let selfLoops := domain.states.map (fun state => (state, state))
  checkGraph "BoundedCounter full-state bracket" bracketed domain oracle.initial
    (oracle.transitions ++ selfLoops)

private def checkLatch : IO Unit := do
  let profile : Profile := ⟨[("flag", .bool)], [], "Init", "Next"⟩
  let imported ← readModule profile (fixtures / "Latch.tla")
  let valuation (flag : Bool) : Kernel.State profile.signature.scope
    | .bool, _ => flag
    | .int, _ => (0 : Int)
  checkGraph "Latch raw" imported ⟨[false, true], valuation⟩ [false]
    [(false, true), (true, false)]

private def expectFailure (label : String) (profile : Profile) (source : String)
    (accepts : Import.Diagnostic → Bool) : IO Unit :=
  match importModule profile source with
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly accepted")
  | .error cause => check (accepts cause) s!"{label}: unexpected diagnostic {reprStr cause}"

private def checkErrors : IO Unit := do
  let profile := Profile.quintApalache0624 counterSignature
  let header := "---- MODULE Rejected ----\n"
  let declarations := "VARIABLE n\nq_init == n = 0\nq_step == n' = 1\n"
  let complete := header ++ declarations ++ "====\n"
  expectFailure "missing terminator" profile (header ++ declarations) (fun
    | .parse cause => cause.kind == .syntax && cause.span.start.line == 5 &&
        cause.span.start.column == 1 && cause.span.start == cause.span.stop &&
        cause.message == "expected a module terminator (====)"
    | _ => false)
  expectFailure "unresolved library" profile (header ++ "EXTENDS Local\n" ++ declarations ++ "====\n")
    (fun | .elaborate (.unresolvedImport "Local") => true | _ => false)
  expectFailure "missing variable sort" (.quintApalache0624 []) complete
    (fun | .elaborate (.missingSort "n") => true | _ => false)
  expectFailure "unchecked assumption" profile (header ++ declarations ++ "ASSUME FALSE\n====\n")
    (fun | .elaborate (.unsupportedDeclaration "ASSUME") => true | _ => false)
  expectFailure "assignment operator without EXTENDS Apalache" profile
    (header ++ "VARIABLE n\nq_init == n = 0\nq_step == n' := 1\n====\n")
    (fun | .elaborate (.inDefinition "q_step" (.requiresImport ":=" .apalache)) => true | _ => false)
  expectFailure "action selected as initialization" { profile with initial := "q_step" } complete
    (fun | .initial "q_step" (.actionInState "q_step") => true | _ => false)
  expectFailure "missing step operator" { profile with step := "Next" } complete
    (fun | .step "Next" (.unknownName "Next") => true | _ => false)
  IO.println "TLA+ import diagnostics passed"

public def main : IO Unit := do
  let oracle ← requireOk "oracle.json" (Json.parse (← IO.FS.readFile (fixtures / "oracle.json")))
  let counter ← requireOk "BoundedCounter oracle" (oracle.getObjValAs? Oracle "BoundedCounter")
  let bits ← requireOk "BitPair oracle" (oracle.getObjValAs? Oracle "BitPair")
  let (imported, domain) ← checkExport "BoundedCounter" counterSignature counter
  -- The reversed signature exercises column lookup by name.
  let _ ← checkExport "BitPair" [("y", .int), ("x", .int)] bits
  checkCounterBracket imported domain counter
  checkLatch
  checkErrors
