module

import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Analysis.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Admission.Prefix.Graph.Defs
import Silmaril.SSA.RVSDG.Interprocedural.Terms.Thms
meta import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Analysis.Thms
meta import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Admission.Prefix.Graph.Defs

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Groups.Regression

open NestedTheta.Liveness
open Continuation.Partial.Executable (Actions Observation observe runFor)
open Ordered.Prefix (Plan Scope lastExport seededGraph)

private abbrev T := Ty Unit Unit
private abbrev num : T := .value (.data ())
private abbrev single := [num]
private abbrev pair := [num, num]
private abbrev memberFn : Function Unit Unit := ⟨[], single⟩
private abbrev exportFn : Function Unit Unit := ⟨single, pair⟩

private inductive Op : Dialect (ValueSort Unit Unit) Unit
  | read (blocking : Bool) : Op single single
  | finish : Op [] []

private def machine : Machine Op where
  Data _ := Nat
  State _ := Unit
  primitive
    | .read _, value => value
    | .finish, _ => .nil

private def one (n : Nat) : Tuple machine.Val single := .cons (.data n) .nil

private def actions : Actions machine Nat where
  step
    | .read blocking, value@(.cons (.data n) .nil) => fun store =>
      let n : Nat := n
      if blocking && n == 0 then none else some (value, store + n)
    | .finish, _ => fun store => some (.nil, store + 10)

private abbrev singleSlot : MemberSummaries Unit Unit :=
  ⟨[memberFn], fun _ => single, fun _ _ => [.arg 0], fun _ _ _ _ _ needed => needed⟩

private theorem onlyMember (i : Fin 1) : i = 0 := Fin.ext (Nat.lt_one_iff.mp i.isLt)

private abbrev groupPorts := memberPorts singleSlot.members

private def memberBody (blocking : Bool) :
    Code Op [memberFn.port, num] [] [single] single true (some singleSlot) :=
  .primitive (.read blocking) (.cons (.arg (.tail .head)) .nil)
    (.ret (.cons (.output (0 : Fin 1) .head) .nil))

private def group (blocking : Bool) (capture : Port pair num) : Family Op singleSlot pair where
  context := single
  captures := .cons (.arg capture) .nil
  memberWires i := by
    refine Fin.cases ?_ (fun j => j.elim0) i
    exact .cons (.arg (.tail .head)) (.cons (.arg .head) .nil)
  sigs := fun _ => [single]
  body i := by
    refine Fin.cases ?_ (fun j => j.elim0) i
    exact memberBody blocking
  closed := by
    intro i demand
    obtain rfl := onlyMember i
    have eq : ((memberBody blocking).plan demand).live = [.arg 1] := by
      cases h : demand 0 <;>
        simp [memberBody, Code.plan, DemandPlan.prepend, transfer, selectWires, Wires.addresses, Origin.address,
          Demand.observes, Port.index, definedAt, h]
    change (∀ p, p < 1 → Address.arg p ∉ ((memberBody blocking).plan demand).live) ∧
      ∀ p, Address.arg (1 + p) ∈ ((memberBody blocking).plan demand).live → Address.arg p ∈ [.arg 0]
    rw [eq]
    simp only [List.mem_singleton, Address.arg.injEq]
    exact ⟨by omega, by omega⟩

private def first := group false .head

private def second : GroupBinding Op singleSlot pair [groupPorts] :=
  { family := group true (.tail .head), captures := by exact .cons (.arg (.tail .head)) .nil }

private theorem ready (blocking : Bool) (capture : Port pair num) (value : Tuple machine.Val single) :
    (group blocking capture).Ready (m := machine) value := by
  intro i
  obtain rfl := onlyMember i
  refine ⟨?_, fun _ _ _ => trivial⟩
  cases value with
  | cons v rest => cases rest; rfl

private abbrev both := Ordered.append singleSlot singleSlot
private abbrev past := [groupPorts, groupPorts]
private abbrev context := [memberFn.port, num, memberFn.port, num]
private abbrev entry := context ++ exportFn.args

private abbrev firstSlot := leftIndex singleSlot singleSlot (0 : Fin 1)
private abbrev secondSlot := rightIndex singleSlot singleSlot (0 : Fin 1)

private def exportBody : Code Op entry [] [single, single, []] pair true (some both) :=
  .familyCall (table := both) firstSlot .head (.cons (.arg (.tail .head)) .nil) .nil
    (.familyCall (table := both) secondSlot (.tail (.tail .head))
      (.cons (.arg (.tail (.tail (.tail .head)))) .nil) .nil
      (.primitive .finish .nil
        (.ret (.cons (.output (0 : Fin 3) .head) (.cons (.output (1 : Fin 3) .head) .nil)))))

private def exportBinding : Ordered.Binding Op both pair past exportFn where
  context := context
  captures := .cons (.output (0 : Fin 2) .head) (.cons (.arg .head)
    (.cons (.output (1 : Fin 2) .head) (.cons (.arg (.tail .head)) .nil)))
  sigs := [single, single, []]
  body := exportBody

private def tail : ModuleTerm Op pair [groupPorts] [groupPorts, [exportFn.port]] [exportFn.port] :=
  .bind (.phi second.term) (.bind (.lambda exportBinding.term) (.ret (lastExport past exportFn)))

private def numbered := seededGraph first tail

private def imported (b : Nat) : Tuple machine.Val pair := .cons (.data (2 : Nat)) (one b)

open Isomorphism.RecursiveCall.Numbered (OrdinaryOutputs decidePort instructionCode)
open Isomorphism.RecursiveCall.Numbered.Prefix (GraphPlan admitGraph)

local instance : DecidableEq T := decidePort

private def primitiveKeys : NestedTheta.Equality.OpcodeCode Op where
  Key := Nat
  encode
    | .read false => 0
    | .read true => 1
    | .finish => 2
  injective := by
    intro _ _ x y equal
    cases x <;> cases y <;> try (first | rfl | cases equal)
    rename_i a b
    cases a <;> cases b <;> first | rfl | cases equal

private abbrev keys := instructionCode primitiveKeys

private instance : DecidableEq keys.Key :=
  show DecidableEq (Sum Nat (Ports T × Ports T)) from inferInstance

private theorem ordinary : OrdinaryOutputs Op := by
  intro _ _ opcode
  cases opcode <;> rfl

private def alignment : GraphPlan numbered numbered :=
  .seed (.phi (.lambda .done))

-- The same numbered module is accepted by paired isomorphism admission.
#guard (admitGraph keys actions Eq ordinary 83 83 (imported 3) (imported 3)
  numbered numbered alignment (fn := exportFn) .head 20 20).isSome

private def exportScope (b : Nat) := (Scope.seed first (imported b) (imported b)).addGroup second (imported b) (imported b)

private theorem resolved (b : Nat) :
    exportBinding.resolved (exportScope b).guardL (imported b) (exportScope b).localsL := by
  intro args locals
  exact ⟨⟨rfl, rfl⟩, fun _ => ⟨⟨rfl, rfl⟩, fun _ _ => trivial⟩⟩

private def plan (b : Nat) :
    Plan (imported b) (imported b) (Scope.seed first (imported b) (imported b)) exportBinding.summary tail :=
  .phi (scope := Scope.seed first (imported b) (imported b)) second
    (ready true (.tail .head) _) (ready true (.tail .head) _)
    (.finish (scope := exportScope b) exportBinding (resolved b) (resolved b))

private def admitted (b : Nat) :=
  (plan b).analyzeNumbered first actions 83 numbered (imported b) (imported b) 20
    (by exact OmegaTerm.toTerm_toGraph _) (ready false .head _) (ready false .head _)

private def analysis (b : Nat) := (admitted b).get (by rfl)
private def demanded : Demand := fun _ => true

#guard (analysis 3).liveCapture demanded (.tail .head)
#guard (analysis 3).liveCapture demanded (.tail (.tail (.tail .head)))
#guard !(analysis 3).liveFormal demanded .head

example : Address.arg 1 ∈ ((analysis 3).problem demanded).mayOut 0 :=
  ((analysis 3).mem_liveIn_iff demanded _).1 (by decide)

example : Address.arg 3 ∈ ((analysis 3).problem demanded).mayOut 0 :=
  ((analysis 3).mem_liveIn_iff demanded _).1 (by decide)

private def run (fuel b spare : Nat) :=
  Executable.run actions fuel 83 numbered (imported b) .head (one spare) 20

example (fuel after b : Nat) :
    ∃ left right, run fuel b 4 = .ok left ∧ run fuel b 40 = .ok right ∧
      PrefixObservationsAgree actions demanded after left right :=
  (analysis b).linked_prefixes_agree demanded fuel after (one 4) (one 40) (fun _ _ => rfl)
    (fun p live => by
      cases p with
      | head => exact False.elim (Bool.noConfusion live)
      | tail p => nomatch p)

private def returned : Observation machine Nat pair → Option (Nat × Nat × Nat)
  | .returned (.cons (.data a) (.cons (.data b) .nil)) store => some (a, b, store)
  | _ => none

private def blocked (spare : Nat) : Option (Nat × Nat) :=
  match run 64 0 spare with
  | .ok (.blocked ⟨⟨_, _, .read true, _, _, .cons (.data n) .nil⟩, _⟩ store) => some (n, store)
  | _ => none

private def resumed (spare : Nat) : Option (Nat × Nat × Nat) :=
  match run 64 0 spare with
  | .ok (.blocked ⟨⟨_, _, .read true, _, _, _⟩, stack⟩ _) =>
    returned (observe actions (runFor actions 64 ⟨.returned (one 7) stack, 50⟩))
  | _ => none

#guard (run 64 3 4).toOption.bind returned == some (2, 3, 35)
#guard (run 64 3 40).toOption.bind returned == some (2, 3, 35)
#guard blocked 4 == some (0, 22)
#guard blocked 40 == some (0, 22)
#guard resumed 4 == some (2, 7, 60)
#guard resumed 40 == some (2, 7, 60)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Groups.Regression
