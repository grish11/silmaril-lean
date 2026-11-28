module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Reindex.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Thms

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Proofs

open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy WordOp)
open Silmaril.SSA.RVSDG (Address Origin Port Tuple Wires)
open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow)

variable {arity : Nat} {entrySigs sigs : List (List PortTy)}

private theorem supported_reindex (mapping : InputMap arity) {past : List (List PortTy)}
    (flow : Dataflow WordOp (wordPorts arity) past sigs) :
    supported (mapCaptureFlow mapping flow) = supported flow := by
  induction flow with
  | nil => rfl
  | cons op _ _ ih => cases op <;> simp only [mapCaptureFlow, supported, ih]

private theorem computed_reindex (mapping : InputMap arity) {past : List (List PortTy)}
    {ports : List PortTy} (entry : Wires (wordPorts arity) past ports) :
    (mapping.column entry).addresses.any isComputedEntry = entry.addresses.any isComputedEntry := by
  induction entry with
  | nil => rfl
  | cons w _ ih =>
    cases w <;> simp only [InputMap.column, mapColumn, mapOrigin, Tuple.map, Wires.addresses, Origin.address,
      List.any_cons, isComputedEntry] at ih ⊢ <;> rw [ih]

theorem port_index_lt {n : Nat} {t : PortTy} (port : Port (wordPorts n) t) :
    port.index < n := by
  induction n with
  | zero => cases port
  | succ n ih => cases port with
    | head => exact Nat.zero_lt_succ n
    | tail t => exact Nat.succ_lt_succ (ih t)

private theorem argument_index (i : Fin arity) : (argumentPort arity i).index = i.val := by
  induction arity with
  | zero => exact i.elim0
  | succ n ih => cases i using Fin.cases with
    | zero => rfl
    | succ i => exact congrArg Nat.succ (ih i)

-- The placeholder index of a producer is in range because a column with
-- a computed entry is nonempty. The checker still reads the actual entry
-- column when it constructs the preheader.
private theorem placeholder_checked (pos : 0 < arity) {past : List (List PortTy)} {width : Nat}
    (entry : Wires (wordPorts arity) past (wordPorts width)) :
    ∃ c, checkColumn arity width (entry.addresses.map entryPlaceholder) = some c ∧
      c.addresses = (entry.addresses.map entryPlaceholder).map Address.arg := by
  induction width with
  | zero => cases entry; exact ⟨.nil, rfl, rfl⟩
  | succ width ih =>
    cases entry with
    | cons w restWires =>
      let tail : Wires (wordPorts arity) past (wordPorts width) := restWires
      have bounded : entryPlaceholder w.address < arity := by
        cases w with
        | arg p => exact port_index_lt p
        | output _ _ => exact pos
      obtain ⟨rest, found, addresses⟩ := ih tail
      refine ⟨.cons (.arg (argumentPort arity ⟨entryPlaceholder w.address, bounded⟩)) rest, ?_, ?_⟩
      · change (if inside : entryPlaceholder w.address < arity then
            (checkColumn arity width (tail.addresses.map entryPlaceholder)).map
              (Tuple.cons (.arg (argumentPort arity ⟨entryPlaceholder w.address, inside⟩)))
          else none) = _
        simp [bounded, found]
      · change Address.arg (argumentPort arity ⟨entryPlaceholder w.address, bounded⟩).index :: rest.addresses =
          Address.arg (entryPlaceholder w.address) :: (tail.addresses.map entryPlaceholder).map Address.arg
        rw [argument_index, addresses]

private theorem arguments_map (raw : List Nat) :
    (raw.map Address.arg).mapM Native.Decode.argument = some raw := by
  induction raw with
  | nil => rfl
  | cons i rest ih => simp [List.mapM_cons, Native.Decode.argument, ih]

private theorem decode_reentry {code : Native.GraphCode} {oldRaw : List Nat} {spec : Spec}
    (addresses : code.entry = oldRaw.map Address.arg)
    (decoded : Native.Decode.spec arity code = some spec) (raw : List Nat) :
    spec.entry = oldRaw ∧
      Native.Decode.spec arity {code with entry := raw.map Address.arg} = some {spec with entry := raw} := by
  rcases code with ⟨header, entry, feedback, predicate, result⟩
  change entry = _ at addresses
  subst entry
  change spec.entry = oldRaw ∧
    Native.Decode.spec arity ⟨header, raw.map Address.arg, feedback, predicate, result⟩ = _
  unfold Native.Decode.spec at decoded ⊢
  generalize header.reverse = rev at decoded ⊢
  split at decoded
  next =>
    simp only [arguments_map] at decoded
    obtain ⟨updates, hUpdates, rest⟩ := Option.bind_eq_some_iff.mp decoded
    obtain ⟨guard, hGuard, rest⟩ := Option.bind_eq_some_iff.mp rest
    obtain ⟨operand, hOperand, rest⟩ := Option.bind_eq_some_iff.mp rest
    obtain ⟨entry, hEntry, rest⟩ := Option.bind_eq_some_iff.mp rest
    obtain rfl := Option.some.inj hEntry
    obtain ⟨copies, hCopies, rest⟩ := Option.bind_eq_some_iff.mp rest
    obtain ⟨exit, hExit, result⟩ := Option.bind_eq_some_iff.mp rest
    obtain rfl := (Option.some.inj result).symm
    refine ⟨rfl, ?_⟩
    simp only [arguments_map, bind, Option.bind, hUpdates, hGuard, hOperand, hCopies, hExit]
  next => cases decoded

private theorem plan_reentry {spec : Spec} {row : Rows.Plan arity}
    {oldCol newCol : ArgumentColumn arity arity}
    (oldEntry : checkColumn arity arity spec.entry = some oldCol)
    (checked : Rows.checkPlan arity spec = some row) {raw : List Nat}
    (newEntry : checkColumn arity arity raw = some newCol) :
    Rows.checkPlan arity {spec with entry := raw} = some {row with entry := newCol} := by
  unfold Rows.checkPlan at checked ⊢
  obtain ⟨column, found, rest⟩ := Option.bind_eq_some_iff.mp checked
  obtain rfl := Option.some.inj (found.symm.trans oldEntry)
  refine Option.bind_eq_some_iff.mpr ⟨newCol, newEntry, ?_⟩
  obtain ⟨copies, hCopies, rest⟩ := Option.bind_eq_some_iff.mp rest
  refine Option.bind_eq_some_iff.mpr ⟨copies, hCopies, ?_⟩
  obtain ⟨updates, hUpdates, rest⟩ := Option.bind_eq_some_iff.mp rest
  refine Option.bind_eq_some_iff.mpr ⟨updates, hUpdates, ?_⟩
  obtain ⟨guard, hGuard, rest⟩ := Option.bind_eq_some_iff.mp rest
  refine Option.bind_eq_some_iff.mpr ⟨guard, hGuard, ?_⟩
  obtain ⟨operand, hOperand, rest⟩ := Option.bind_eq_some_iff.mp rest
  refine Option.bind_eq_some_iff.mpr ⟨operand, hOperand, ?_⟩
  split at rest
  next bounds =>
    rw [dite_eq_left bounds]
    obtain ⟨exit, hExit, result⟩ := Option.bind_eq_some_iff.mp rest
    obtain rfl := (Option.some.inj result).symm
    exact Option.bind_eq_some_iff.mpr ⟨exit, hExit, rfl⟩
  next => cases rest

private theorem native_reentry {g : SourceWithEntry arity entrySigs sigs}
    {oldCol newCol : ArgumentColumn arity arity} {oldRaw raw : List Nat} {spec : Spec} {row : Rows.Plan arity}
    (oldChecked : checkColumn arity arity oldRaw = some oldCol)
    (oldAddresses : oldCol.addresses = oldRaw.map Address.arg)
    (newChecked : checkColumn arity arity raw = some newCol)
    (newAddresses : newCol.addresses = raw.map Address.arg)
    (recognized : Native.recognize (bodyGraph g oldCol) = some spec)
    (plan : Rows.checkPlan arity spec = some row) :
    Native.recognize (bodyGraph g newCol) = some {spec with entry := raw} ∧
      Rows.checkPlan arity {spec with entry := raw} = some {row with entry := newCol} := by
  unfold Native.recognize at recognized ⊢
  obtain ⟨candidate, decoded, valid⟩ := Option.bind_eq_some_iff.mp recognized
  obtain ⟨original, checked, equal⟩ := Option.bind_eq_some_iff.mp valid
  split at equal
  next exactCode =>
    have sameSpec := Option.some.inj equal
    subst candidate
    have sameRow := Option.some.inj (checked.symm.trans plan)
    subst original
    obtain ⟨rawEntry, decodeNew⟩ := decode_reentry (code := Native.graphCode (bodyGraph g oldCol))
      oldAddresses decoded raw
    have checkNew := plan_reentry (rawEntry.symm ▸ oldChecked) checked newChecked
    have inputs : Native.graphCode (bodyGraph g newCol) =
        {Native.graphCode (bodyGraph g oldCol) with entry := raw.map Address.arg} := by
      change Native.GraphCode.mk _ newCol.addresses _ _ _ = _
      rw [newAddresses]
      rfl
    have newCode : Native.graphCode (bodyGraph g newCol) =
        Native.graphCode ({row with entry := newCol} : Rows.Plan arity).graph :=
      congrArg (fun c : Native.GraphCode => {c with entry := newCol.addresses}) exactCode
    have decodeMapped : Native.Decode.spec arity (Native.graphCode (bodyGraph g newCol)) =
        some {spec with entry := raw} := by
      rw [inputs]
      exact decodeNew
    refine ⟨Option.bind_eq_some_iff.mpr ⟨_, decodeMapped, Option.bind_eq_some_iff.mpr ⟨_, checkNew, ?_⟩⟩,
      checkNew⟩
    exact ite_eq_left newCode
  next => cases equal

theorem recognize_mapCaptures (mapping : InputMap arity) {g : SourceWithEntry arity entrySigs sigs}
    {p : Plan arity entrySigs} (recognized : recognize g = some p) :
    ∃ column : ArgumentColumn arity arity, ∃ ok : supported (mapCaptureFlow mapping p.flow) = true,
      recognize (mapCaptures mapping g) =
        some ⟨mapCaptureFlow mapping p.flow, ok, mapping.column p.entry, {p.row with entry := column}⟩ := by
  let entry : EntryColumnWith arity entrySigs := g.phiInputs .entry
  have mapped := computed_reindex mapping entry
  have support := supported_reindex mapping g.preheader
  by_cases arithmetic : supported g.preheader = true
  · by_cases computes : entry.addresses.any isComputedEntry = true
    · have pos : 0 < arity := by
        cases arity with
        | zero =>
          have empty : entry = .nil := by cases entry; rfl
          rw [empty] at computes
          cases computes
        | succ n => exact Nat.zero_lt_succ n
      obtain ⟨oldCol, oldChecked, oldAddresses⟩ := placeholder_checked pos entry
      obtain ⟨newCol, newChecked, newAddresses⟩ := placeholder_checked pos (mapping.column entry)
      change (if h : supported g.preheader = true then
        if entry.addresses.any isComputedEntry = true then
          (checkColumn arity arity (entry.addresses.map entryPlaceholder)).bind fun col =>
            (Native.recognize (bodyGraph g col)).bind fun spec =>
              (Rows.checkPlan arity spec).map fun row => (⟨g.preheader, h, entry, row⟩ : Plan arity entrySigs)
        else none else none) = some p at recognized
      simp only [arithmetic, dite_true, computes, ite_true, oldChecked, Option.bind_some] at recognized
      obtain ⟨spec, found, makePlan⟩ := Option.bind_eq_some_iff.mp recognized
      obtain ⟨row, checked, exactPlan⟩ := Option.map_eq_some_iff.mp makePlan
      subst p
      obtain ⟨newNative, newPlan⟩ := native_reentry oldChecked oldAddresses newChecked newAddresses found checked
      have body : bodyGraph (mapCaptures mapping g) newCol = bodyGraph g newCol := rfl
      refine ⟨newCol, support.trans arithmetic, ?_⟩
      change (if h : supported (mapCaptureFlow mapping g.preheader) = true then
        if (mapping.column entry).addresses.any isComputedEntry = true then
          (checkColumn arity arity ((mapping.column entry).addresses.map entryPlaceholder)).bind fun col =>
            (Native.recognize (bodyGraph (mapCaptures mapping g) col)).bind fun spec =>
              (Rows.checkPlan arity spec).map fun row =>
                (⟨mapCaptureFlow mapping g.preheader, h, mapping.column entry, row⟩ : Plan arity entrySigs)
        else none else none) = _
      simp only [support.trans arithmetic, dite_true, mapped, computes, ite_true, newChecked,
        Option.bind_some, body, newNative, newPlan, Option.map_some]
    · have rejected : recognize g = none := by
        simp only [recognize, arithmetic, dite_true]
        exact ite_eq_right computes
      rw [rejected] at recognized
      cases recognized
  · simp [recognize, arithmetic] at recognized

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Proofs
