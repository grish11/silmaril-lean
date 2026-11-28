module

public import Silmaril.SSA.SeaOfNodes.Pure.Deletion.Defs

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.Deletion

open Silmaril.SSA.SeaOfNodes
open Diamond (Dataflow Signature Ty ValueSort)
open GVN (Producer)
open GVN.Cyclic.Deletion (Erasure Route drop erase? routeSuffix?)
open Pure.Deletion
open Silmaril.SSA.RVSDG (Wires extend)

universe u v

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {args ports : List (Ty Data)} {past sigs target : List (List (Ty Data))}
variable {out : ValueSort Data} {flow : Dataflow Op args past sigs}
variable {candidate : Producer flow out} {outputs : Wires args (extend past sigs) ports}

theorem delete?_eq_some_iff {result : Result Op args ports past sigs} :
    delete? candidate outputs = some result ↔
      erase? candidate = some result.erasure ∧
        Route.wires? result.erasure.route outputs = some result.outputs := by
  cases result with
  | mk erasure packet =>
    simp only [delete?, Option.bind_eq_some_iff, Option.map_eq_some_iff]
    constructor
    · rintro ⟨cut, erased, mapped, routed, eq⟩
      cases eq
      exact ⟨erased, routed⟩
    · rintro ⟨erased, routed⟩
      exact ⟨erasure, erased, packet, routed, rfl⟩

private theorem routeSuffix?_opcode_order (route : Route args past target)
    {shortened : Dataflow Op args target sigs}
    {finalRoute : Route args (extend past sigs) (extend target sigs)}
    (routed : routeSuffix? flow route = some (shortened, @finalRoute)) :
    opcodes shortened = opcodes flow := by
  induction flow generalizing target with
  | nil =>
    cases routed
    rfl
  | @cons past sigs ins out opcode operands rest ih =>
    cases mapped : Route.wires? route operands with
    | none => simp [routeSuffix?, mapped] at routed
    | some wires =>
      cases tail : routeSuffix? rest (Route.push route [.value out]) with
      | none => simp [routeSuffix?, mapped, tail] at routed
      | some pair =>
        obtain ⟨shortenedTail, tailRoute⟩ := pair
        simp only [routeSuffix?, mapped, tail, Option.bind_some, Option.map_some, Option.some.injEq] at routed
        rw [← (Prod.mk.inj routed).1]
        exact congrArg (List.cons ⟨ins, out, opcode⟩) (ih (Route.push route [.value out]) tail)

theorem erase?_opcode_order {erasure : Erasure Op args past sigs}
    (accepted : erase? candidate = some erasure) :
    opcodes erasure.flow = (opcodes flow).eraseIdx (position candidate) := by
  induction candidate with
  | @here past sigs ins out opcode operands rest =>
    cases routed : routeSuffix? rest (drop [(.value out : Ty Data)]) with
    | none => simp [erase?, routed] at accepted
    | some pair =>
      obtain ⟨shortened, route⟩ := pair
      simp only [erase?, routed, Option.map_some, Option.some.injEq] at accepted
      subst erasure
      exact routeSuffix?_opcode_order _ routed
  | @later past sigs ins out result opcode operands rest candidate ih =>
    cases cut : erase? candidate with
    | none => simp [erase?, cut] at accepted
    | some tail =>
      simp only [erase?, cut, Option.map_some, Option.some.injEq] at accepted
      subst erasure
      exact congrArg (List.cons ⟨ins, out, opcode⟩) (ih cut)

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.Deletion
