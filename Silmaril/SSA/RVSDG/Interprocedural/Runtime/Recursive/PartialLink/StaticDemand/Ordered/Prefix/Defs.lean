module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Thms

/-! A typed plan for one φ seed followed by ordered λ bindings and a λ export. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix

open Continuation.Partial.Executable (Actions)
open Isomorphism.RecursiveCall.Numbered (linkedLambda)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {table : MemberSummaries V S} {imports : Ports (Ty V S)}
variable {fn : Function V S}

/-- The linker locals and exact guards used when specifying local resolution.
The fold supplies the membership tables and the transport proofs. -/
structure Scope (m : Machine.{u, v, w} Op) where
  past : List (Ports (Ty V S))
  table : MemberSummaries V S
  localsL : Locals m.Val past
  localsR : Locals m.Val past
  guardL : Guard m table
  guardR : Guard m table

def Scope.seed (family : StaticDemand.Family Op table imports)
    (inputsL inputsR : Tuple m.Val imports) : Scope m :=
  let groupL := family.captures.read inputsL PUnit.unit
  let groupR := family.captures.read inputsR PUnit.unit
  ⟨[memberPorts table.members], table, (family.references groupL, PUnit.unit),
    (family.references groupR, PUnit.unit), family.guard groupL, family.guard groupR⟩

namespace Scope

variable (scope : Scope m)

structure Checked (actions : Actions m σ) where
  state : CheckedPrefix actions scope.table scope.localsL scope.localsR
  left : state.dispatch.left = scope.guardL
  right : state.dispatch.right = scope.guardR

def add (binding : Binding Op scope.table imports scope.past fn)
    (inputsL inputsR : Tuple m.Val imports) : Scope m :=
  ⟨scope.past ++ [[fn.port]], prepend binding.summary scope.table,
    scope.localsL.snoc (.cons (binding.value inputsL scope.localsL) .nil),
    scope.localsR.snoc (.cons (binding.value inputsR scope.localsR) .nil),
    binding.extendGuard scope.guardL inputsL scope.localsL, binding.extendGuard scope.guardR inputsR scope.localsR⟩

def skip (definition : LambdaTerm Op imports scope.past fn)
    (inputsL inputsR : Tuple m.Val imports) : Scope m :=
  ⟨scope.past ++ [[fn.port]], scope.table,
    scope.localsL.snoc (.cons (linkedLambda definition.toGraph inputsL scope.localsL) .nil),
    scope.localsR.snoc (.cons (linkedLambda definition.toGraph inputsR scope.localsR) .nil),
    scope.guardL, scope.guardR⟩

end Scope

/-- The final export is the sole port of the last physical λ binding. -/
def lastPort (fn : Function V S) : (past : List (Ports (Ty V S))) →
    (i : Fin (past ++ [[fn.port]]).length) × Port ((past ++ [[fn.port]])[i]) fn.port
  | [] => ⟨(0 : Fin 1), .head⟩
  | _ :: rest => ⟨(lastPort fn rest).1.succ, (lastPort fn rest).2⟩

def lastExport (past : List (Ports (Ty V S))) (fn : Function V S) :
    Wires imports (past ++ [[fn.port]]) [fn.port] :=
  .cons (.output (lastPort fn past).1 (lastPort fn past).2) .nil

set_option genSizeOf false in
/-- A plan is indexed by the actual module tail. Each admitted λ supplies
only local resolution on its actual captured tuple and all formal inputs.
Skipped λs link normally but contribute no checked callable to the table. -/
inductive Plan (inputsL inputsR : Tuple m.Val imports) :
    (scope : Scope m) → (exported : MemberSummary V S) → {sigs : List (Ports (Ty V S))} →
    ModuleTerm Op imports scope.past sigs [exported.fn.port] → Type (max u v w + 1) where
  | finish {scope : Scope m} {fn : Function V S}
      (binding : Binding Op scope.table imports scope.past fn)
      (left : binding.resolved scope.guardL inputsL scope.localsL)
      (right : binding.resolved scope.guardR inputsR scope.localsR) :
      Plan inputsL inputsR scope binding.summary (.bind (.lambda binding.term) (.ret (lastExport scope.past fn)))
  | lambda {scope : Scope m} {exported : MemberSummary V S} {fn : Function V S}
      {sigs : List (Ports (Ty V S))}
      (binding : Binding Op scope.table imports scope.past fn)
      (left : binding.resolved scope.guardL inputsL scope.localsL)
      (right : binding.resolved scope.guardR inputsR scope.localsR)
      {rest : ModuleTerm Op imports (scope.past ++ [[fn.port]]) sigs [exported.fn.port]}
      (next : Plan inputsL inputsR (scope.add binding inputsL inputsR) exported rest) :
      Plan inputsL inputsR scope exported (.bind (.lambda binding.term) rest)
  | finishDirect {scope : Scope m} {fn : Function V S}
      (binding : Binding Op scope.table imports scope.past fn) :
      Plan inputsL inputsR scope binding.summary (.bind (.lambda binding.term) (.ret (lastExport scope.past fn)))
  | lambdaDirect {scope : Scope m} {exported : MemberSummary V S} {fn : Function V S}
      {sigs : List (Ports (Ty V S))}
      (binding : Binding Op scope.table imports scope.past fn)
      {rest : ModuleTerm Op imports (scope.past ++ [[fn.port]]) sigs [exported.fn.port]}
      (next : Plan inputsL inputsR (scope.add binding inputsL inputsR) exported rest) :
      Plan inputsL inputsR scope exported (.bind (.lambda binding.term) rest)
  | skipLambda {scope : Scope m} {exported : MemberSummary V S} {fn : Function V S}
      {sigs : List (Ports (Ty V S))}
      (definition : LambdaTerm Op imports scope.past fn)
      {rest : ModuleTerm Op imports (scope.past ++ [[fn.port]]) sigs [exported.fn.port]}
      (next : Plan inputsL inputsR (scope.skip definition inputsL inputsR) exported rest) :
      Plan inputsL inputsR scope exported (.bind (.lambda definition) rest)

/-- The computed table, selected static slot, and exact successful link
outcomes for the two inputs. -/
structure Export (actions : Actions m σ) (summary : MemberSummary V S)
    (left right : Outcome m σ [summary.fn.port]) where
  earlier : MemberSummaries V S
  dispatch : Dispatch actions (prepend summary earlier)
  targetL : m.Val summary.fn.port
  targetR : m.Val summary.fn.port
  capsL : Tuple m.Val summary.captures
  capsR : Tuple m.Val summary.captures
  store : σ
  linkedL : left = .linked (.cons targetL .nil) store
  linkedR : right = .linked (.cons targetR .nil) store
  resolvedL : dispatch.left (0 : Fin (earlier.members.length + 1)) targetL capsL
  resolvedR : dispatch.right (0 : Fin (earlier.members.length + 1)) targetR capsR

def Export.relink {actions : Actions m σ} {summary : MemberSummary V S}
    {left right actualL actualR : Outcome m σ [summary.fn.port]} (receipt : Export actions summary left right)
    (linkL : actualL = left) (linkR : actualR = right) : Export actions summary actualL actualR where
  earlier := receipt.earlier
  dispatch := receipt.dispatch
  targetL := receipt.targetL
  targetR := receipt.targetR
  capsL := receipt.capsL
  capsR := receipt.capsR
  store := receipt.store
  linkedL := linkL.trans receipt.linkedL
  linkedR := linkR.trans receipt.linkedR
  resolvedL := receipt.resolvedL
  resolvedR := receipt.resolvedR

def seededGraph (family : StaticDemand.Family Op table imports)
    {sigs : List (Ports (Ty V S))} {outs : Ports (Ty V S)}
    (tail : ModuleTerm Op imports [memberPorts table.members] sigs outs) :
    Omega Op imports outs (memberPorts table.members :: sigs) :=
  OmegaTerm.toGraph ⟨.bind (.phi family.group) tail⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix
