module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked.Defs
import Silmaril.SSA.RVSDG.NestedTheta.Equality.Thms

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked.Proofs

open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy WordOp word)
open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow ValueSort)
open Silmaril.SSA.SeaOfNodes.Loop (Graph)
open Silmaril.SSA.RVSDG (Origin Wires)
open Silmaril.SSA.RVSDG.NestedTheta.Equality (addresses_injective)

private theorem origin_eq {args : List PortTy} {past : List (List PortTy)} {t : PortTy}
    {left right : Origin args past t} (h : left.address = right.address) : left = right := by
  let lhs : Wires args past [t] := .cons left .nil
  let rhs : Wires args past [t] := .cons right .nil
  have addresses : lhs.addresses = rhs.addresses := congrArg List.singleton h
  exact congrArg (fun w : Wires args past [t] => w.get .head) (addresses_injective lhs rhs addresses)

theorem schedule_eq {args : List PortTy} (body : Dataflow WordOp args [] headerSigs)
    (p : Profile) (update : Wires args [] [.value word, .value word])
    (guard : Wires args [[.value word], [.value word]] [.value word, .value word])
    (decoded : decodeSchedule body = some p)
    (addresses : scheduleAddresses body = scheduleAddresses (schedule p update guard)) :
    body = schedule p update guard := by
  cases body with
  | cons opcode stepArgs rest =>
    cases rest with
    | cons bound limitArgs rest =>
      cases rest with
      | cons test guardArgs rest =>
        cases rest
        cases opcode <;> cases bound <;> cases test <;>
          simp only [decodeSchedule, decodeUpdate, decodeLimit, decodeGuard,
            reduceCtorEq] at decoded
        all_goals
          obtain rfl := Option.some.inj decoded
          simp only [schedule, scheduleAddresses, Update.source, Guard.source,
            List.cons.injEq] at addresses
          obtain ⟨op, limit, cmp, _⟩ := addresses
          cases addresses_injective _ _ op
          cases addresses_injective _ _ limit
          cases addresses_injective _ _ cmp
          rfl

private theorem graph_eq {inputs carried : List (ValueSort Unit)}
    {g h : Graph WordOp inputs carried [] headerSigs word} (header : g.header = h.header)
    (phi : g.phiInputs = h.phiInputs) (pred : g.predicate = h.predicate)
    (result : g.result = h.result) : g = h := by
  cases g with
  | mk pre body operands predA resultA =>
    cases h with
    | mk pre' body' operands' predB resultB =>
      cases pre
      cases pre'
      cases header
      cases phi
      cases pred
      cases result
      rfl

theorem graph_eq_of_provenance {inputs carried : List (ValueSort Unit)}
    {g h : Graph WordOp inputs carried [] headerSigs word}
    (header : g.header = h.header) (agree : provenance g = provenance h) : g = h := by
  refine graph_eq header ?_ (origin_eq (congrArg Provenance.predicate agree))
    (origin_eq (congrArg Provenance.result agree))
  funext edge
  cases edge with
  | entry => exact addresses_injective _ _ (congrArg Provenance.entry agree)
  | backedge => exact addresses_injective _ _ (congrArg Provenance.feedback agree)

theorem decode_schedule {args : List PortTy} (p : Profile)
    (update : Wires args [] [.value word, .value word])
    (guard : Wires args [[.value word], [.value word]] [.value word, .value word]) :
    decodeSchedule (schedule p update guard) = some p := by
  rcases p with ⟨op, limit, cmp⟩
  cases op <;> cases cmp <;> rfl

private theorem decode_canonical (p : Profile) : decodeSchedule p.graph.header = some p := by
  rcases p with ⟨update, limit, guard⟩
  cases update <;> cases guard <;> rfl

theorem recognize_eq_some_iff (g : WordLoop) (p : Profile) :
    recognize g = some p ↔ g = p.graph := by
  constructor
  · intro accepted
    cases decode : decodeSchedule g.header with
    | none => simp [recognize, decode] at accepted
    | some candidate =>
      simp only [recognize, decode] at accepted
      split at accepted
      · rename_i agree
        obtain rfl := Option.some.inj accepted
        refine graph_eq_of_provenance ?_ agree
        exact schedule_eq g.header candidate
          (.cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail .head)) .nil))
          (.cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil))
          decode (congrArg Provenance.producers agree)
      · cases accepted
  · rintro rfl
    simp [recognize, decode_canonical]

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked.Proofs
