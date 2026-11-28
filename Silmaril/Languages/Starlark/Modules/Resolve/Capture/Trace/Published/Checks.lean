module

import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Defs

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published

open scoped Functions.Lowering.Quote
open Defaults
open Defaults.Nested.Sequence.Recursive (Site)
open Defaults.Nested.Sequence.Recursive.Call.Named (Mapping Operands)
open Functions (Program)

private def globals : List String := ["data", "worker", "late", "copy", "result", "after"]

private def int (n : Int) : Functions.Lowering.Expr := .atom (.scalar (.int n))

private def boxed (n : Int) : Functions.Lowering.Expr := .list [int n]

private def keywords : List PlainKeywordParameter :=
  [.defaulted ⟨"key", starlark%[data], Leaf.readOperand (globalSlot "data"), [globalSlot "data"]⟩]

private def worker : Site (moduleLex globals) keywords (some "rest") (some "extras") .global where
  name := "worker"
  target := by decide
  parameters := ⟨["first"], []⟩
  source := .seq (.assign "marked" starlark%[[44]])
    (.seq (.assign "probe" starlark%[key[0]]) (.ret (some starlark%[late])))
  binders := ["marked", "probe"]
  locals := ["marked", "probe"]
  collects := .seq (.assign _ _) (.seq (.assign _ _) (.ret _))
  localOrder := .keep (by decide) (.keep (by decide) .nil)
  body := ⟨.seq (.assignExpr (fileSlot "marked") (boxed 44))
    (.seq (.assignExpr (fileSlot "probe") (.index (Leaf.readOperand (fileSlot "key")) (int 0)))
      (.returnExpr (Leaf.readOperand (globalSlot "late")))), [fileSlot "key", globalSlot "late"]⟩
  free := [⟨globalSlot "late", globalSlot "late"⟩]
  selects := .owned (.owned (by decide)) (.module (.module (by decide) (by decide) (by decide)) .nil)
  defaults := []
  lexical := .nil

private def root : Root globals where
  keywords := keywords
  varargs := some "rest"
  kwargs := some "extras"
  site := worker
  lexical := .cons (.read (by decide) (.global (by decide) (by decide) (by decide))
    (.module (by decide) (by decide) (by decide))) .nil
  seed := #[]
  bodyTable := #[]
  children := []
  suite := .plain (.straight (.assign (by decide) (.list (.int 44))
    (.assign (by decide) (.index (.read (by decide) (.owned (by decide)) (.owned (by decide))) (.int 0))
      (.ret (.read (by decide) (.global (by decide) (by decide) (by decide))
        (.module (by decide) (by decide) (by decide)))))))

private inductive Mode where
  | success | bodyError | bindingError

private def mapping (mode : Mode) : Mapping (moduleLex globals) :=
  match mode with
  | .success =>
    ⟨[(.string "key", starlark%[data])], [(.atom (.string "key"), Leaf.readOperand (globalSlot "data"))],
      [globalSlot "data"], .entry (.string "key")
        (.plain (.read (by decide) (.global (by decide) (by decide) (by decide))
          (.module (by decide) (by decide) (by decide)))) .empty⟩
  | .bodyError =>
    ⟨[(.string "key", starlark%[8])], [(.atom (.string "key"), int 8)], [],
      .entry (.string "key") (.plain (.int 8)) .empty⟩
  | .bindingError =>
    ⟨[(.string "extra", starlark%[[62]])], [(.atom (.string "extra"), boxed 62)], [],
      .entry (.string "extra") (.plain (.list (.int 62))) .empty⟩

private def actuals : Operands (moduleLex globals) :=
  ⟨[("extra", starlark%[[61]])], [("extra", boxed 61)], [], .cons (.list (.int 61)) .nil, by decide⟩

private def invocation (mode : Mode) : Invocation globals where
  callee := "copy"
  calleeGlobal := by decide
  legal := by decide
  destination := "result"
  destinationGlobal := by decide
  arguments := [starlark%[[17]]]
  codes := [boxed 17]
  reads := []
  operands := .cons (.list (.int 17)) .nil
  keywords := actuals
  star := some (.list (.cons (.read (name := "data") (by decide)
    (.global (by decide) (by decide) (by decide)) (.module (by decide) (by decide) (by decide))) .nil))
  mapping := some (mapping mode)

private def commands (mode : Mode) : List Resolve.Command :=
  [.assign "data" starlark%[[31]], root.command, .assign "late" starlark%[data], .assign "copy" starlark%[worker],
   (invocation mode).source, .assign "after" starlark%[[99]]]

private def outputs (mode : Mode) : List Modules.Command :=
  [.exec (.assignExpr "data" (boxed 31)), .exec (.define "worker" 0),
   .exec (.assignExpr "late" (Leaf.readOperand (globalSlot "data"))),
   .exec (.assignExpr "copy" (Leaf.readOperand (globalSlot "worker"))),
   .exec (.assignExpr "result" (invocation mode).code), .exec (.assignExpr "after" (boxed 99))]

private def exports : Environment :=
  update (update (update (update (update (update (fun _ => none) "data" none)
    "worker" (some root.callable)) "late" none) "copy" (some root.callable)) "result" none) "after" none

private theorem plan (mode : Mode) : Plan globals (fun _ => none) (commands mode) #[] (outputs mode) root.table exports :=
  .assign (by decide) (.list (.int 31)) .forget
    (.define root
      (.assign (by decide) (.read (by decide) (.global (by decide) (by decide) (by decide))
        (.module (by decide) (by decide) (by decide))) .forget
        (.assign (by decide) (.read (by decide) (.global (by decide) (by decide) (by decide))
          (.module (by decide) (by decide) (by decide)))
          (.copy (name := "worker") rfl)
          (.invoke (invocation mode) root.callable rfl
            (.assign (by decide) (.list (.int 99)) .forget .done)))))

example (mode : Mode) {resolved : ResolvedModule} (checked : resolve (commands mode) = .ok resolved)
    (caller : Lists.State) :
    ∃ reached, ExecutesAll globals (enter resolved.source caller) (commands mode) reached ∧
      runModule (commands mode) (fun _ => none) caller = .ok (finish resolved.source caller reached) := by
  have certified : Plan (Trace.names (commands mode)) (fun _ => none) (commands mode) #[] (outputs mode) root.table exports := by
    cases mode <;> exact plan _
  obtain ⟨out, ran, _, _, exactResult, _⟩ := module_agrees certified checked (fun _ => none) caller
  exact ⟨out, by cases mode <;> exact ran, exactResult⟩

#guard
  match runModule (commands .success) (fun _ => none) {} with
  | .ok (.ok published final) =>
    match published.exports.lookup "worker", published.exports.lookup "copy", published.exports.lookup "data",
      published.exports.lookup "result" with
    | some (.function worker), some (.function copy), some (.list data), some (.list result) =>
      match final.heap[worker]?, final.heap[data]? with
      | some ⟨.function closure, true⟩, some ⟨.list [.scalar (.int 31)], true⟩ =>
        worker == copy && data == result &&
        closure.defaults == [(fileSlot "key", .list data)] &&
        (match closure.captures with
        | [capture] => final.heap[capture.address]? == some ⟨.binding (some (.list data)), false⟩
        | _ => false)
      | _, _ => false
    | _, _, _, _ => false
  | _ => false

private def fails (mode : Mode) (expected : Lists.Error) (allocated : List Int) (tupleCount dictCount : Nat) : Bool :=
  let caller : Lists.State := { iterators := [123] }
  match runModule (commands mode) (fun _ => none) caller, resolve (commands mode) with
  | .ok (.error (.runtime reached) final), .ok resolved =>
    let entered := enter resolved.source caller
    let cell name := (entered.slots (globalSlot name)).bind (fun slot => final.heap[slot.address]?)
    let lists := final.heap.toList.filterMap fun cell => match cell.contents with
      | .list [.scalar (.int value)] => some value
      | _ => none
    let tuples := final.heap.toList.countP fun cell => match cell.contents with | .tuple .. => true | _ => false
    let dicts := final.heap.toList.countP fun cell => match cell.contents with | .dict .. => true | _ => false
    let mutableData := match cell "data" with
      | some ⟨.binding (some (.list address)), false⟩ => final.heap[address]? == some ⟨.list [.scalar (.int 31)], false⟩
      | _ => false
    reached == expected && lists == allocated && tuples == tupleCount && dicts == dictCount && mutableData &&
    cell "result" == some ⟨.binding none, false⟩ && cell "after" == some ⟨.binding none, false⟩ &&
    (final.slots (globalSlot "copy")).isNone && final.iterators == [123]
  | _, _ => false

#guard fails .bodyError .indexTarget [31, 17, 61, 44] 1 2
#guard fails .bindingError (.multipleArgumentValues "extra") [31, 17, 61, 62] 0 1

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published
