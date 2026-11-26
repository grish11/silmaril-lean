module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Defs

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Proofs

open Continuation.Partial.Executable (Actions)
open Isomorphism.RecursiveCall.Numbered (linkedLambda)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {table : MemberSummaries V S} {imports outs : Ports (Ty V S)}
variable {past sigs : List (Ports (Ty V S))} {fn : Function V S}
variable {actions : Actions m σ}

theorem added_guards {localsL localsR : Locals m.Val past}
    (earlier : CheckedPrefix actions table localsL localsR) (binding : Binding Op table imports past fn)
    (inputsL inputsR : Tuple m.Val imports)
    (left : binding.resolved earlier.dispatch.left inputsL localsL)
    (right : binding.resolved earlier.dispatch.right inputsR localsR)
    {next : CheckedPrefix actions (prepend binding.summary table)
      (localsL.snoc (.cons (binding.value inputsL localsL) .nil))
      (localsR.snoc (.cons (binding.value inputsR localsR) .nil))}
    (added : earlier.addLambda binding inputsL inputsR left right = some next) :
    next.dispatch.left = binding.extendGuard earlier.dispatch.left inputsL localsL ∧
      next.dispatch.right = binding.extendGuard earlier.dispatch.right inputsR localsR := by
  unfold CheckedPrefix.addLambda at added
  split at added
  · cases added
    exact ⟨rfl, rfl⟩
  · cases added

theorem last_read (inputs : Tuple m.Val imports) (locals : Locals m.Val past)
    (value : m.Val fn.port) :
    (lastExport past fn).read inputs (locals.snoc (.cons value .nil)) = .cons value .nil := by
  induction past with
  | nil => rfl
  | cons _ tail ih => exact ih locals.2

theorem finish_link (binding : Binding Op table imports past fn) (actions : Actions m σ) (unitId : Nat)
    (inputs : Tuple m.Val imports) (locals : Locals m.Val past) (store : σ) :
    Isomorphism.RecursiveCall.Numbered.Prefix.linkTerm actions unitId inputs locals
      (.bind (.lambda binding.term) (.ret (lastExport past fn))) store =
      .linked (.cons (binding.value inputs locals) .nil) store := by
  rw [binding.link_step]
  exact congrArg (fun values => Outcome.linked values store) (last_read inputs locals _)

theorem skip_link (definition : LambdaTerm Op imports past fn) (actions : Actions m σ) (unitId : Nat)
    (inputs : Tuple m.Val imports) (locals : Locals m.Val past)
    (rest : ModuleTerm Op imports (past ++ [[fn.port]]) sigs outs) (store : σ) :
    Isomorphism.RecursiveCall.Numbered.Prefix.linkTerm actions unitId inputs locals
      (.bind (.lambda definition) rest) store =
    Isomorphism.RecursiveCall.Numbered.Prefix.linkTerm actions unitId inputs
      (locals.snoc (.cons (linkedLambda definition.toGraph inputs locals) .nil)) rest store := by
  rw [Isomorphism.RecursiveCall.Numbered.Prefix.linkTerm_bind]
  rfl

theorem seed_link (family : StaticDemand.Family Op table imports) (actions : Actions m σ) (unitId : Nat)
    (inputs : Tuple m.Val imports) (tail : ModuleTerm Op imports [memberPorts table.members] sigs outs)
    (store : σ) :
    Executable.link actions unitId (seededGraph family tail) inputs store =
      Isomorphism.RecursiveCall.Numbered.Prefix.linkTerm actions unitId inputs (past := [memberPorts table.members])
        (family.references (family.captures.read inputs PUnit.unit), PUnit.unit) tail store :=
  (Isomorphism.RecursiveCall.Numbered.Prefix.linkTerm_bind (past := []) actions unitId inputs
    PUnit.unit (.phi family.group) tail store).trans rfl

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Proofs
