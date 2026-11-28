module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Correct

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered

open NestedTheta.Liveness (Demand)
open Continuation.Partial.Executable (Actions)
open Isomorphism.RecursiveCall.Numbered
open Isomorphism.RecursiveCall.Numbered.Prefix (Row memberRow)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {table : MemberSummaries V S} {imports exports : Ports (Ty V S)}
variable {past sigs : List (Ports (Ty V S))} {fn : Function V S} {actions : Actions m σ}

theorem Dispatch.seed_transport (family : StaticDemand.Family Op table imports)
    (groupL groupR : Tuple m.Val family.context)
    (readyL : family.Ready groupL) (readyR : family.Ready groupR) :
    ∀ i fL fR capsL capsR,
      family.guard groupL i fL capsL → family.guard groupR i fR capsR →
      CallAgrees actions (table.at i) fL fR capsL capsR :=
  Proofs.seed_transport family groupL groupR readyL readyR

/-- Admit all slots of the linked φ seed, including unexported members.
A synthesized family can enter directly via `Family.Template.admit`. -/
@[expose] def CheckedPrefix.seed (actions : Actions m σ) (family : StaticDemand.Family Op table imports)
    (groupL groupR : Tuple m.Val family.context) (readyL : family.Ready groupL) (readyR : family.Ready groupR) :
    CheckedPrefix (past := [memberPorts table.members]) actions table
      (family.references groupL, PUnit.unit) (family.references groupR, PUnit.unit) where
  dispatch := ⟨family.guard groupL, family.guard groupR, Dispatch.seed_transport family groupL groupR readyL readyR⟩
  left := ⟨memberRow table.members (family.memberValue groupL)
    (fun i => .callable i _ (family.capturedAt groupL i) ⟨rfl, rfl⟩), PUnit.unit⟩
  right := ⟨memberRow table.members (family.memberValue groupR)
    (fun i => .callable i _ (family.capturedAt groupR i) ⟨rfl, rfl⟩), PUnit.unit⟩

/-- Use one typed λ body with the actual captures read at each placement. -/
theorem Dispatch.lambda_transport_withCaptures (earlier : Dispatch actions table) (binding : Binding Op table imports past fn)
    {pastR : List (Ports (Ty V S))} (capturesR : Wires imports pastR binding.context)
    (inputsL inputsR : Tuple m.Val imports) (localsL : Locals m.Val past) (localsR : Locals m.Val pastR)
    (resolvedL : binding.resolved earlier.left inputsL localsL)
    (resolvedR : (binding.withCaptures capturesR).resolved earlier.right inputsR localsR) :
    ∀ i fL fR capsL capsR,
      binding.extendGuard earlier.left inputsL localsL i fL capsL →
      (binding.withCaptures capturesR).extendGuard earlier.right inputsR localsR i fR capsR →
      CallAgrees actions ((prepend binding.summary table).at i) fL fR capsL capsR :=
  Proofs.lambda_transport earlier binding capturesR inputsL inputsR localsL localsR resolvedL resolvedR

theorem Dispatch.lambda_transport (earlier : Dispatch actions table) (binding : Binding Op table imports past fn)
    (inputsL inputsR : Tuple m.Val imports) (localsL localsR : Locals m.Val past)
    (resolvedL : binding.resolved earlier.left inputsL localsL)
    (resolvedR : binding.resolved earlier.right inputsR localsR) :
    ∀ i fL fR capsL capsR,
      binding.extendGuard earlier.left inputsL localsL i fL capsL →
      binding.extendGuard earlier.right inputsR localsR i fR capsR →
      CallAgrees actions ((prepend binding.summary table).at i) fL fR capsL capsR :=
  earlier.lambda_transport_withCaptures binding binding.captures inputsL inputsR localsL localsR resolvedL resolvedR

theorem Known.weaken {ty : Ty V S} {value : m.Val ty} {guard : Guard m table}
    (binding : Binding Op table imports past fn) (inputs : Tuple m.Val imports) (locals : Locals m.Val past) :
    Known guard value → Known (binding.extendGuard guard inputs locals) value
  | .ordinary value plain => .ordinary value plain
  | .callable i f caps checked =>
    Known.callable (table := prepend binding.summary table) (guard := binding.extendGuard guard inputs locals)
      i.succ f caps checked

@[expose] def Binding.checkedRow {guard : Guard m table} (binding : Binding Op table imports past fn)
    (inputs : Tuple m.Val imports) (locals : Locals m.Val past) :
    Row (Known (binding.extendGuard guard inputs locals)) (.cons (binding.value inputs locals) .nil)
  | _, .head => some ⟨Known.callable (table := prepend binding.summary table)
      (guard := binding.extendGuard guard inputs locals) (0 : Fin (table.members.length + 1))
      (binding.value inputs locals) (binding.captures.read inputs locals) ⟨rfl, rfl⟩⟩
  | _, .tail p => nomatch p

/-- Check actual capture origins against the checked imports and earlier link prefix, then
attach the computed summary and extend the saved-suffix transport. The
caller supplies the static target/capture resolution proof for all
formals. The new λ cannot name its own slot in its body. -/
@[expose] def CheckedPrefix.addLambdaWithImports {localsL localsR : Locals m.Val past}
    (earlier : CheckedPrefix actions table localsL localsR) (binding : Binding Op table imports past fn)
    (inputsL inputsR : Tuple m.Val imports)
    (importedL : Row (Known earlier.dispatch.left) inputsL)
    (importedR : Row (Known earlier.dispatch.right) inputsR)
    (resolvedL : binding.resolved earlier.dispatch.left inputsL localsL)
    (resolvedR : binding.resolved earlier.dispatch.right inputsR localsR) :
    Option (CheckedPrefix actions (prepend binding.summary table)
      (localsL.snoc (.cons (binding.value inputsL localsL) .nil))
      (localsR.snoc (.cons (binding.value inputsR localsR) .nil))) :=
  if (checkWires (entry := inputsL) (earlier.left.availableWithImports Known.ordinary importedL) binding.captures).isSome &&
      (checkWires (entry := inputsR) (earlier.right.availableWithImports Known.ordinary importedR) binding.captures).isSome then
    let dispatch : Dispatch actions (prepend binding.summary table) :=
      ⟨binding.extendGuard earlier.dispatch.left inputsL localsL, binding.extendGuard earlier.dispatch.right inputsR localsR,
        Dispatch.lambda_transport earlier.dispatch binding inputsL inputsR localsL localsR resolvedL resolvedR⟩
    some ⟨dispatch, (earlier.left.lift (Known.weaken binding inputsL localsL)).snoc (binding.checkedRow inputsL localsL),
      (earlier.right.lift (Known.weaken binding inputsR localsR)).snoc (binding.checkedRow inputsR localsR)⟩
  else none

/-- Check actual capture origins against the earlier link prefix, then
attach the computed summary and extend the saved-suffix transport. The
caller supplies the static target/capture resolution proof for all
formals. The new λ cannot name its own slot in its body. -/
@[expose] def CheckedPrefix.addLambda {localsL localsR : Locals m.Val past}
    (earlier : CheckedPrefix actions table localsL localsR) (binding : Binding Op table imports past fn)
    (inputsL inputsR : Tuple m.Val imports)
    (resolvedL : binding.resolved earlier.dispatch.left inputsL localsL)
    (resolvedR : binding.resolved earlier.dispatch.right inputsR localsR) :
    Option (CheckedPrefix actions (prepend binding.summary table)
      (localsL.snoc (.cons (binding.value inputsL localsL) .nil))
      (localsR.snoc (.cons (binding.value inputsR localsR) .nil))) :=
  earlier.addLambdaWithImports binding inputsL inputsR (fun _ => none) (fun _ => none) resolvedL resolvedR

/-- The term linker adds exactly the λ value used to index the checked row. -/
theorem Binding.link_step (binding : Binding Op table imports past fn)
    (actions : Actions m σ) (unitId : Nat) (inputs : Tuple m.Val imports) (locals : Locals m.Val past)
    (rest : ModuleTerm Op imports (past ++ [[fn.port]]) sigs exports) (store : σ) :
    Prefix.linkTerm actions unitId inputs locals (.bind (.lambda binding.term) rest) store =
      Prefix.linkTerm actions unitId inputs (locals.snoc (.cons (binding.value inputs locals) .nil)) rest store := by
  rw [Prefix.linkTerm_bind]
  rfl

/-- Compare the actual selected export after successful linkage to one
common store. Resolve the selected values at a common static slot and
check agreement on its computed capture/formal reads. -/
theorem Dispatch.linked_prefixes_agree (checked : Dispatch actions table) (i : Fin table.members.length)
    (demand : Demand) (fuel after unitId : Nat) (graph : Omega Op imports exports sigs)
    (port : Port exports (table.at i).fn.port)
    (inputsL inputsR : Tuple m.Val imports) (argsL argsR : Tuple m.Val (table.at i).fn.args) (initial : σ)
    {outsL outsR : Tuple m.Val exports} {middle : σ} {capsL capsR : Tuple m.Val (table.at i).captures}
    (linkedL : Executable.link actions unitId graph inputsL initial = .linked outsL middle)
    (linkedR : Executable.link actions unitId graph inputsR initial = .linked outsR middle)
    (dispatchL : checked.left i (outsL.get port) capsL) (dispatchR : checked.right i (outsR.get port) capsR)
    (agree : InputsAgree (m := m) (table.at i) demand (prependContext argsL capsL) (prependContext argsR capsR)) :
    ∃ left right,
      Executable.run actions fuel unitId graph inputsL port argsL initial = .ok left ∧
      Executable.run actions fuel unitId graph inputsR port argsR initial = .ok right ∧
      PrefixObservationsAgree actions demand after left right :=
  Proofs.linked checked i demand fuel after unitId graph port inputsL inputsR argsL argsR initial
    linkedL linkedR dispatchL dispatchR agree

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered
