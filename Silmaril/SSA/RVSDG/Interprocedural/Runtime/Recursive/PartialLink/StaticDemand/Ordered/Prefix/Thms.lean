module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Direct.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Link

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix

open Continuation.Partial.Executable (Actions)
open NestedTheta.Liveness (Demand)
open Isomorphism.RecursiveCall.Numbered (linkedLambda)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {table : MemberSummaries V S} {imports outs : Ports (Ty V S)}
variable {past sigs : List (Ports (Ty V S))} {fn : Function V S}
variable {actions : Actions m σ}

theorem add_preserves_guards {localsL localsR : Locals m.Val past}
    (earlier : CheckedPrefix actions table localsL localsR) (binding : Binding Op table imports past fn)
    (inputsL inputsR : Tuple m.Val imports)
    (left : binding.resolved earlier.dispatch.left inputsL localsL)
    (right : binding.resolved earlier.dispatch.right inputsR localsR)
    {next : CheckedPrefix actions (prepend binding.summary table)
      (localsL.snoc (.cons (binding.value inputsL localsL) .nil))
      (localsR.snoc (.cons (binding.value inputsR localsR) .nil))}
    (added : earlier.addLambda binding inputsL inputsR left right = some next) :
    next.dispatch.left = binding.extendGuard earlier.dispatch.left inputsL localsL ∧
      next.dispatch.right = binding.extendGuard earlier.dispatch.right inputsR localsR :=
  Proofs.added_guards earlier binding inputsL inputsR left right added

theorem link_finish (binding : Binding Op table imports past fn) (actions : Actions m σ) (unitId : Nat)
    (inputs : Tuple m.Val imports) (locals : Locals m.Val past) (store : σ) :
    Isomorphism.RecursiveCall.Numbered.Prefix.linkTerm actions unitId inputs locals (.bind (.lambda binding.term) (.ret (lastExport past fn))) store =
      .linked (.cons (binding.value inputs locals) .nil) store :=
  Proofs.finish_link binding actions unitId inputs locals store

theorem link_skip (definition : LambdaTerm Op imports past fn) (actions : Actions m σ) (unitId : Nat)
    (inputs : Tuple m.Val imports) (locals : Locals m.Val past)
    (rest : ModuleTerm Op imports (past ++ [[fn.port]]) sigs outs) (store : σ) :
    Isomorphism.RecursiveCall.Numbered.Prefix.linkTerm actions unitId inputs locals (.bind (.lambda definition) rest) store =
      Isomorphism.RecursiveCall.Numbered.Prefix.linkTerm actions unitId inputs (locals.snoc (.cons (linkedLambda definition.toGraph inputs locals) .nil))
        rest store :=
  Proofs.skip_link definition actions unitId inputs locals rest store

theorem link_seededGraph (family : StaticDemand.Family Op table imports) (actions : Actions m σ) (unitId : Nat)
    (inputs : Tuple m.Val imports) (tail : ModuleTerm Op imports [memberPorts table.members] sigs outs) (store : σ) :
    Executable.link actions unitId (seededGraph family tail) inputs store =
      Isomorphism.RecursiveCall.Numbered.Prefix.linkTerm actions unitId inputs (past := [memberPorts table.members])
        (family.references (family.captures.read inputs PUnit.unit), PUnit.unit)
        tail store :=
  Proofs.seed_link family actions unitId inputs tail store

variable {scope : Scope m}

/-- Check one λ's typed capture positions and transport its local evidence
from the plan's guards to the guards computed by the ordered admission. -/
@[expose] def Scope.Checked.add (checked : scope.Checked actions)
    (binding : Binding Op scope.table imports scope.past fn) (inputsL inputsR : Tuple m.Val imports)
    (left : binding.resolved scope.guardL inputsL scope.localsL)
    (right : binding.resolved scope.guardR inputsR scope.localsR) :
    Option ((scope.add binding inputsL inputsR).Checked actions) :=
  let resolvedL : binding.resolved checked.state.dispatch.left inputsL scope.localsL := checked.left.symm ▸ left
  let resolvedR : binding.resolved checked.state.dispatch.right inputsR scope.localsR := checked.right.symm ▸ right
  match h : checked.state.addLambda binding inputsL inputsR resolvedL resolvedR with
  | none => none
  | some state =>
    let guards := add_preserves_guards checked.state binding inputsL inputsR resolvedL resolvedR h
    some ⟨state, guards.1.trans (congrArg (fun g => binding.extendGuard g inputsL scope.localsL) checked.left),
      guards.2.trans (congrArg (fun g => binding.extendGuard g inputsR scope.localsR) checked.right)⟩

/-- Use the same admission step with a synthesized local certificate. -/
@[expose] def Scope.Checked.addDirect (checked : scope.Checked actions)
    (binding : Binding Op scope.table imports scope.past fn) (inputsL inputsR : Tuple m.Val imports)
    (routes : Direct.Routes inputsL inputsR scope) :
    Option ((scope.add binding inputsL inputsR).Checked actions) :=
  match Direct.synthesize checked routes binding.captures (fn := fn) binding.body with
  | none => none
  | some resolved => checked.add binding inputsL inputsR resolved.down.1 resolved.down.2

@[expose] def Scope.Checked.skip (checked : scope.Checked actions)
    (definition : LambdaTerm Op imports scope.past fn) (inputsL inputsR : Tuple m.Val imports) :
    (scope.skip definition inputsL inputsR).Checked actions :=
  ⟨⟨checked.state.dispatch, checked.state.left.snoc (fun _ => none), checked.state.right.snoc (fun _ => none)⟩,
    checked.left, checked.right⟩

@[expose] def Scope.Checked.export (binding : Binding Op scope.table imports scope.past fn)
    (inputsL inputsR : Tuple m.Val imports) (checked : (scope.add binding inputsL inputsR).Checked actions)
    (unitId : Nat) (store : σ) :
    Export actions binding.summary
      (Isomorphism.RecursiveCall.Numbered.Prefix.linkTerm actions unitId inputsL scope.localsL
        (.bind (.lambda binding.term) (.ret (lastExport scope.past fn))) store)
      (Isomorphism.RecursiveCall.Numbered.Prefix.linkTerm actions unitId inputsR scope.localsR
        (.bind (.lambda binding.term) (.ret (lastExport scope.past fn))) store) where
  earlier := scope.table
  dispatch := checked.state.dispatch
  targetL := binding.value inputsL scope.localsL
  targetR := binding.value inputsR scope.localsR
  capsL := binding.captures.read inputsL scope.localsL
  capsR := binding.captures.read inputsR scope.localsR
  store := store
  linkedL := link_finish binding actions unitId inputsL scope.localsL store
  linkedR := link_finish binding actions unitId inputsR scope.localsR store
  resolvedL := by rw [checked.left]; exact ⟨rfl, rfl⟩
  resolvedR := by rw [checked.right]; exact ⟨rfl, rfl⟩

/-- Build the table in the order of the actual module. Each checked λ
uses one `addLambda` step. Skipped positions stay empty in the reused
linker membership table. -/
@[expose] def Plan.walk (actions : Actions m σ) (unitId : Nat) (inputsL inputsR : Tuple m.Val imports)
    (store : σ) : {scope : Scope m} → {summary : MemberSummary V S} → {sigs : List (Ports (Ty V S))} →
    {tail : ModuleTerm Op imports scope.past sigs [summary.fn.port]} →
    (plan : Plan inputsL inputsR scope summary tail) → scope.Checked actions →
    (routes : Direct.Routes inputsL inputsR scope := fun _ => none) →
    Option (Export actions summary (Isomorphism.RecursiveCall.Numbered.Prefix.linkTerm actions unitId inputsL scope.localsL tail store)
      (Isomorphism.RecursiveCall.Numbered.Prefix.linkTerm actions unitId inputsR scope.localsR tail store))
  | _, _, _, _, .finish binding left right, checked, _ =>
    (checked.add binding inputsL inputsR left right).map fun added =>
      Scope.Checked.export binding inputsL inputsR added unitId store
  | scope, _, _, _, .lambda binding left right (rest := rest) next, checked, routes => do
    let added ← checked.add binding inputsL inputsR left right
    let receipt ← walk actions unitId inputsL inputsR store next added (routes.add binding)
    pure (receipt.relink (binding.link_step actions unitId inputsL scope.localsL rest store)
      (binding.link_step actions unitId inputsR scope.localsR rest store))
  | _, _, _, _, .finishDirect binding, checked, routes =>
    (checked.addDirect binding inputsL inputsR routes).map fun added =>
      Scope.Checked.export binding inputsL inputsR added unitId store
  | scope, _, _, _, .lambdaDirect binding (rest := rest) next, checked, routes => do
    let added ← checked.addDirect binding inputsL inputsR routes
    let receipt ← walk actions unitId inputsL inputsR store next added (routes.add binding)
    pure (receipt.relink (binding.link_step actions unitId inputsL scope.localsL rest store)
      (binding.link_step actions unitId inputsR scope.localsR rest store))
  | scope, _, _, _, .skipLambda definition (rest := rest) next, checked, routes =>
    (walk actions unitId inputsL inputsR store next (checked.skip definition inputsL inputsR) (routes.skip definition)).map fun receipt =>
      receipt.relink (link_skip definition actions unitId inputsL scope.localsL rest store)
        (link_skip definition actions unitId inputsR scope.localsR rest store)
termination_by structural _ _ _ _ plan _ _ => plan

/-- Recover the computed ordered table and exact successful link outcomes
at the selected λ export. The plan chooses supplied or synthesized local
resolution for each checked binding. -/
@[expose] def Plan.admit (family : StaticDemand.Family Op table imports) (actions : Actions m σ)
    (unitId : Nat) (inputsL inputsR : Tuple m.Val imports) (store : σ)
    {summary : MemberSummary V S} {tail : ModuleTerm Op imports [memberPorts table.members] sigs [summary.fn.port]}
    (plan : Plan inputsL inputsR (Scope.seed family inputsL inputsR) summary tail)
    (readyL : family.Ready (family.captures.read inputsL PUnit.unit))
    (readyR : family.Ready (family.captures.read inputsR PUnit.unit)) :
    Option (Export actions summary (Executable.link actions unitId (seededGraph family tail) inputsL store)
      (Executable.link actions unitId (seededGraph family tail) inputsR store)) :=
  let checked : (Scope.seed family inputsL inputsR).Checked actions :=
    ⟨CheckedPrefix.seed actions family (family.captures.read inputsL PUnit.unit)
      (family.captures.read inputsR PUnit.unit) readyL readyR, rfl, rfl⟩
  (plan.walk actions unitId inputsL inputsR store checked (Direct.Routes.seed family inputsL inputsR)).map fun receipt =>
    receipt.relink (link_seededGraph family actions unitId inputsL tail store)
      (link_seededGraph family actions unitId inputsR tail store)

/-- Successful admission feeds the selected slot and exact linked values
straight into the existing finite-prefix theorem. -/
theorem Export.linked_prefixes_agree {summary : MemberSummary V S}
    (demand : Demand) (fuel after unitId : Nat) (graph : Omega Op imports [summary.fn.port] sigs)
    (inputsL inputsR : Tuple m.Val imports) (argsL argsR : Tuple m.Val summary.fn.args) (initial : σ)
    (receipt : Export actions summary (Executable.link actions unitId graph inputsL initial)
      (Executable.link actions unitId graph inputsR initial))
    (agree : InputsAgree (m := m) summary demand (prependContext argsL receipt.capsL)
      (prependContext argsR receipt.capsR)) :
    ∃ left right,
      Executable.run actions fuel unitId graph inputsL .head argsL initial = .ok left ∧
      Executable.run actions fuel unitId graph inputsR .head argsR initial = .ok right ∧
      PrefixObservationsAgree actions demand after left right :=
  receipt.dispatch.linked_prefixes_agree (0 : Fin (receipt.earlier.members.length + 1))
    demand fuel after unitId graph .head inputsL inputsR argsL argsR initial
    receipt.linkedL receipt.linkedR receipt.resolvedL receipt.resolvedR agree

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix
