module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked.Phi.Defs

/-! # A guarded feedback row over an arbitrary i64 bank -/

@[expose] public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows

open Silmaril.Machine.Lir (Memory Word ofBool)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (State)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg WordOp model)
open Silmaril.SSA.RVSDG (Address Origin Port Wires extend)
open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow)
open Silmaril.SSA.SeaOfNodes.GVN (keepOrigin newest weaken)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA

structure Plan (arity : Nat) where
  entry : ArgumentColumn arity arity
  copies : ArgumentColumn arity arity
  updates : List (FeedbackUpdate arity)
  guardIndex : Fin updates.length
  comparison : Guard
  limit : Word
  exitSlot : Fin arity

/-- Copies and the exit projection use old bank slot numbers. The guard
origin names a computed producer, whose destination must match the
declared guard destination. -/
structure Spec where
  entry : List Nat
  copies : List Nat
  updates : List FeedbackSpec
  guardOrigin : Address
  guardDestination : Nat
  comparison : Guard
  limit : Word
  exitSlot : Nat

def checkPlan (arity : Nat) (spec : Spec) : Option (Plan arity) := do
  let entry ← checkColumn arity arity spec.entry
  let copies ← checkColumn arity arity spec.copies
  let updates ← checkFeedbackRow arity spec.updates
  let .output index 0 := spec.guardOrigin | none
  if inside : index < updates.length then
    if updates[index].destination.val = spec.guardDestination then
      if exit : spec.exitSlot < arity then
        some ⟨entry, copies, updates, ⟨index, inside⟩, spec.comparison, spec.limit, ⟨spec.exitSlot, exit⟩⟩
      else none
    else none
  else none

theorem extend_append (past sigs tail : List (List PortTy)) :
    extend past (sigs ++ tail) = extend (extend past sigs) tail := by
  induction sigs generalizing past with
  | nil => rfl
  | cons _ _ ih => exact ih _

def appendFlow {args : List PortTy} {tail : List (List PortTy)} :
    {past sigs : List (List PortTy)} → Dataflow WordOp args past sigs →
    Dataflow WordOp args (extend past sigs) tail → Dataflow WordOp args past (sigs ++ tail)
  | _, _, .nil, rest => rest
  | _, _, .cons op wires next, rest => .cons op wires (appendFlow next rest)

def joinedOrigin {args : List PortTy} {past sigs tail : List (List PortTy)} {t : PortTy}
    (wire : Origin args (extend (extend past sigs) tail) t) :
    Origin args (extend past (sigs ++ tail)) t :=
  (extend_append past sigs tail).symm ▸ wire

theorem extend_rowSigs {fields : Nat} (updates : List (FeedbackUpdate fields)) (past : List (List PortTy)) :
    extend past (rowSigs updates) = past ++ List.replicate updates.length [wordPort] := by
  induction updates generalizing past with
  | nil => simp [rowSigs, extend]
  | cons _ rest ih =>
    rw [rowSigs, extend, ih, List.length_cons, List.replicate_succ, List.append_assoc]
    rfl

abbrev guardSigs : List (List PortTy) := [[wordPort], [.value .predicate]]

variable {arity : Nat} (p : Plan arity)

abbrev Plan.rowPast := extend [] (rowSigs p.updates)

abbrev Plan.sigs := rowSigs p.updates ++ guardSigs

def Plan.row : Dataflow WordOp (bankArgs arity) [] (rowSigs p.updates) :=
  rowSuffixAt (argumentPort arity) [] p.updates

def Plan.guardWire : Origin (bankArgs arity) p.rowPast wordPort :=
  let index : Fin p.rowPast.length := ⟨p.guardIndex.val, by simp [extend_rowSigs]⟩
  .output index (by
    have mem : p.rowPast[index] ∈ p.rowPast := List.getElem_mem _
    have replicated : p.rowPast[index] ∈ List.replicate p.updates.length [wordPort] := by
      simpa only [extend_rowSigs, List.nil_append] using mem
    exact (List.eq_of_mem_replicate replicated).symm ▸ Port.head)

def Plan.test : Dataflow WordOp (bankArgs arity) p.rowPast guardSigs :=
  .cons (.const p.limit) .nil
    (.cons p.comparison.source (.cons (weaken [wordPort] p.guardWire) (.cons (newest .head) .nil)) .nil)

def Plan.feedbackColumn : Wires (bankArgs arity) p.rowPast (wordPorts arity) :=
  rowColumnAt (argumentPort arity) [] p.updates (p.copies.map fun _ wire =>
    match wire with
    | .arg slot => .arg (suffixPort (wordPorts arity) slot)
    | .output i _ => i.elim0)

def Plan.graph : BankGraph arity p.sigs where
  preheader := .nil
  header := appendFlow p.row p.test
  phiInputs
    | .entry => p.entry
    | .backedge => p.feedbackColumn.map fun _ wire =>
      joinedOrigin (past := []) (sigs := rowSigs p.updates) (tail := guardSigs) (keepOrigin p.test wire)
  predicate := joinedOrigin (past := []) (sigs := rowSigs p.updates) (tail := guardSigs) (newest .head)
  result := .arg (suffixPort (wordPorts arity) (argumentPort arity p.exitSlot))

def Plan.guardValue (old : WordTuple arity) : Word :=
  p.updates[p.guardIndex].evalAt (argumentPort arity) old

def Plan.guardWord (old : WordTuple arity) : Word :=
  ofBool (p.comparison.target.eval (p.guardValue old) p.limit)

def Plan.exitValue (old : WordTuple arity) : Word :=
  old.get (argumentPort arity p.exitSlot)

def Plan.nextBank (input old : WordTuple arity) : WordTuple arity :=
  let args := appendTuple old input
  p.feedbackColumn.read args (p.row.eval model args PUnit.unit)

def Plan.rowFrame (fr : Frame Reg) (old : WordTuple arity) : Frame Reg :=
  rowFrameAt (argumentPort arity) old 0 fr p.updates

def Plan.testFrame (fr : Frame Reg) (old : WordTuple arity) : Frame Reg :=
  ((p.rowFrame fr old).set (.node p.updates.length) p.limit).set
    (.node (p.updates.length + 1)) (p.guardWord old)

def Plan.successor (input old : WordTuple arity) (fr : Frame Reg) (mem : Memory) : State Reg :=
  let after := p.testFrame fr old
  if p.guardWord old = 0 then
    ⟨⟨0, 2, 0⟩, after.set .phi (p.exitValue old), [], mem⟩
  else
    ⟨⟨0, 1, 0⟩, bindWords arity after (p.nextBank input old), [], mem⟩

def lowerChecked (arity : Nat) (spec : Spec) : Option Checked.Phi.Targets :=
  (checkPlan arity spec).bind fun p =>
    if (lowerBankFunc p.graph).WellFormed then some (lowerBank p.graph, Generic.lower p.graph) else none

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
