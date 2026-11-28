module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Deletion.Defs
import Silmaril.SSA.SeaOfNodes.GVN.Elimination.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Deletion

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GVN
open Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Deletion
open GVN.Elimination (splitOrigin read_splitOrigin)
open Diamond (Dataflow Model Signature Ty Val ValueSort dataPorts sortValue)
open Silmaril.SSA.RVSDG (Locals Origin Tuple Wires extend)

universe u v w

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {args : List (Ty Data)} {past target sigs : List (List (Ty Data))}
variable {out : ValueSort Data}
variable (m : Model.{u,v,w} Op) (entry : Tuple (Val m.value) args)

theorem wires_read {route : Route args past target}
    {old : Locals (Val m.value) past} {new : Locals (Val m.value) target}
    (agree : route.Agrees m entry old new) {ports : List (Ty Data)}
    (wires : Wires args past ports) {mapped : Wires args target ports}
    (routed : route.wires? wires = some mapped) :
    wires.read entry old = mapped.read entry new := by
  induction wires with
  | nil =>
    obtain rfl := Option.some.inj routed
    rfl
  | cons wire tail ih =>
    cases headRoute : route wire with
    | none => simp [Route.wires?, headRoute] at routed
    | some head =>
      cases tailRoute : route.wires? tail with
      | none => simp [Route.wires?, headRoute, tailRoute] at routed
      | some rest =>
        have eq : Tuple.cons head rest = mapped := by
          simpa [Route.wires?, headRoute, tailRoute] using routed
        subst mapped
        exact congrArg₂ Tuple.cons (agree wire head headRoute) (ih tailRoute)

private theorem push_agrees {route : Route args past target}
    {old : Locals (Val m.value) past} {new : Locals (Val m.value) target}
    (agree : route.Agrees m entry old new) {head : List (Ty Data)}
    (next : Tuple (Val m.value) head) :
    Route.Agrees (route.push head) m entry (old.snoc next) (new.snoc next) := by
  intro t wire mapped routed
  have read := read_splitOrigin wire m entry old next
  cases split : splitOrigin head wire with
  | inl prior =>
    cases priorRoute : route prior with
    | none => simp [Route.push, split, priorRoute] at routed
    | some shortened =>
      have eq : weaken head shortened = mapped := by
        simpa [Route.push, split, priorRoute] using routed
      subst mapped
      simp only [split] at read
      exact read.symm.trans ((agree prior shortened priorRoute).trans
        (read_weaken shortened m entry new next).symm)
  | inr port =>
    have eq : newest port = mapped := by simpa [Route.push, split] using routed
    subst mapped
    simp only [split] at read
    exact read.symm.trans (read_newest port m entry new next).symm

private theorem drop_agrees {head : List (Ty Data)} (locals : Locals (Val m.value) past)
    (next : Tuple (Val m.value) head) :
    Route.Agrees (drop (args := args) head) m entry (locals.snoc next) locals := by
  intro t wire mapped routed
  have read := read_splitOrigin wire m entry locals next
  cases split : splitOrigin head wire with
  | inl prior =>
    have eq : prior = mapped := by simpa [drop, split] using routed
    subst mapped
    simpa only [split] using read.symm
  | inr port => simp [drop, split] at routed

private theorem suffix_agrees (flow : Dataflow Op args past sigs) (route : Route args past target)
    (old : Locals (Val m.value) past) (new : Locals (Val m.value) target)
    (agree : route.Agrees m entry old new) {suffix : Dataflow Op args target sigs}
    {finalRoute : Route args (extend past sigs) (extend target sigs)}
    (routed : routeSuffix? flow route = some (suffix, @finalRoute)) :
    finalRoute.Agrees m entry (flow.eval m entry old) (suffix.eval m entry new) := by
  induction flow generalizing target with
  | nil =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj routed)
    exact agree
  | @cons past sigs ins out opcode operands rest ih =>
    cases mapped : route.wires? operands with
    | none => simp [routeSuffix?, mapped] at routed
    | some wires =>
      cases tail : routeSuffix? rest (route.push [.value out]) with
      | none => simp [routeSuffix?, mapped, tail] at routed
      | some pair =>
        obtain ⟨shortened, shortenedRoute⟩ := pair
        have shape : ((.cons opcode wires shortened, @shortenedRoute) :
            Dataflow Op args target ([.value out] :: sigs) ×
              Route args (extend past ([.value out] :: sigs)) (extend target ([.value out] :: sigs))) =
            (suffix, @finalRoute) := by
          simpa [routeSuffix?, mapped, tail] using routed
        cases shape
        let next : Tuple (Val m.value) [.value out] := .cons (m.run opcode (operands.read entry old)) .nil
        have sameInputs := wires_read m entry agree operands mapped
        have sameNext : Tuple.cons (F := Val m.value) (t := .value out)
            (m.run opcode (wires.read entry new)) .nil = next :=
          congrArg (fun values => Tuple.cons (F := Val m.value) (t := .value out)
            (m.run opcode values) .nil) sameInputs.symm
        simp only [Dataflow.eval]
        erw [sameNext]
        intro t wire replacement found
        exact ih (route.push [.value out]) (old.snoc next) (new.snoc next)
          (push_agrees m entry agree next) tail wire replacement found

variable {flow : Dataflow Op args past sigs}

theorem erase_agrees (candidate : Producer flow out) (locals : Locals (Val m.value) past)
    {erasure : Erasure Op args past sigs} (accepted : erase? candidate = some erasure) :
    Route.Agrees erasure.route m entry (flow.eval m entry locals) (erasure.flow.eval m entry locals) := by
  induction candidate with
  | @here past sigs ins out opcode operands rest =>
    cases suffix : routeSuffix? rest (drop [(.value out : Ty Data)]) with
    | none => simp [erase?, suffix] at accepted
    | some pair =>
      obtain ⟨shortened, route⟩ := pair
      have shape : (⟨_, shortened, @route, rfl⟩ : Erasure Op args past ([.value out] :: sigs)) = erasure := by
        simpa [erase?, suffix] using accepted
      subst erasure
      let next : Tuple (Val m.value) [.value out] := .cons (m.run opcode (operands.read entry locals)) .nil
      intro t wire replacement found
      exact suffix_agrees m entry rest _ (locals.snoc next) locals
        (drop_agrees m entry locals next) suffix wire replacement found
  | @later past sigs ins out result opcode operands rest candidate ih =>
    cases cut : erase? candidate with
    | none => simp [erase?, cut] at accepted
    | some tail =>
      have shape : (⟨_, .cons opcode operands tail.flow, @tail.route, congrArg Nat.succ tail.shorter⟩ :
          Erasure Op args past ([.value out] :: sigs)) = erasure := by
        simpa [erase?, cut] using accepted
      subst erasure
      intro t wire replacement found
      exact ih (locals.snoc (.cons (m.run opcode (operands.read entry locals)) .nil))
        cut wire replacement found

variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {removed : ValueSort Data}
variable {loop : Loop.Graph Op inputs carried entrySigs headerSigs out}
variable {candidate : Producer loop.header removed}
variable {rewritten : DeletedLoop Op inputs carried entrySigs out}

private theorem admitted (accepted : delete? loop candidate = some rewritten) :
    ∃ erasure predicate feedback result,
      erase? candidate = some erasure ∧
      erasure.route loop.predicate = some predicate ∧
      Route.wires? erasure.route (loop.phiInputs .backedge) = some feedback ∧
      erasure.route loop.result = some result ∧
      rebuild loop erasure predicate feedback result = rewritten := by
  cases cut : erase? candidate with
  | none => simp [delete?, cut] at accepted
  | some erasure =>
    cases guard : erasure.route loop.predicate with
    | none => simp [delete?, cut, guard] at accepted
    | some predicate =>
      cases backedge : Route.wires? erasure.route (loop.phiInputs .backedge) with
      | none => simp [delete?, cut, guard, backedge] at accepted
      | some feedback =>
        cases exit : erasure.route loop.result with
        | none => simp [delete?, cut, guard, backedge, exit] at accepted
        | some result =>
          exact ⟨erasure, predicate, feedback, result, rfl, guard, backedge, exit,
            by simpa [delete?, cut, guard, backedge, exit] using accepted⟩

theorem delete_size (accepted : delete? loop candidate = some rewritten) :
    rewritten.headerSigs.length + 1 = headerSigs.length := by
  obtain ⟨erasure, _, _, _, _, _, _, _, rfl⟩ := admitted accepted
  exact erasure.shorter

theorem delete_initial (accepted : delete? loop candidate = some rewritten)
    (input : Tuple (Val m.value) (dataPorts inputs)) :
    rewritten.graph.initial m input = loop.initial m input := by
  obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := admitted accepted
  rfl

theorem delete_step (accepted : delete? loop candidate = some rewritten)
    (input : Tuple (Val m.value) (dataPorts inputs)) (old : Tuple (Val m.value) (dataPorts carried)) :
    rewritten.graph.step m input old = loop.step m input old := by
  obtain ⟨erasure, predicate, feedback, result, cut, guard, backedge, exit, rfl⟩ := admitted accepted
  let args := Loop.appendTuple old input
  have agree : Route.Agrees erasure.route m args
      (loop.header.eval m args PUnit.unit) (erasure.flow.eval m args PUnit.unit) :=
    erase_agrees m args candidate PUnit.unit cut
  have guardEq := agree loop.predicate predicate guard
  have backedgeEq := wires_read m args agree (loop.phiInputs .backedge) backedge
  have exitEq := agree loop.result result exit
  let outcome (reads : sortValue m.value .predicate ×
      Tuple (Val m.value) (dataPorts carried) × sortValue m.value out) :
      sortValue m.value out ⊕ Tuple (Val m.value) (dataPorts carried) :=
    if reads.1.down then .inr reads.2.1 else .inl reads.2.2
  exact (congrArg outcome (congrArg₂ Prod.mk guardEq (congrArg₂ Prod.mk backedgeEq exitEq))).symm

theorem delete_eval (accepted : delete? loop candidate = some rewritten)
    (input : Tuple (Val m.value) (dataPorts inputs)) (budget : Nat) :
    rewritten.graph.evalBackedges m budget input = loop.evalBackedges m budget input := by
  have steps := delete_step m accepted input
  have evalFromEq (fuel : Nat) (old : Tuple (Val m.value) (dataPorts carried)) :
      rewritten.graph.evalFrom m input fuel old = loop.evalFrom m input fuel old := by
    induction fuel generalizing old with
    | zero => simp only [Loop.Graph.evalFrom, steps]
    | succ fuel ih =>
      simp only [Loop.Graph.evalFrom, steps]
      cases loop.step m input old with
      | inl _ => rfl
      | inr next => exact ih next
  unfold Loop.Graph.evalBackedges
  rw [delete_initial m accepted input]
  exact evalFromEq budget _

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Deletion
