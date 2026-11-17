module

public import Silmaril.Wasm.Component.DecoderBridge.Sem.Defs
public import Silmaril.Wasm.Component.InstTestsRef.Thms
public import Silmaril.Wasm.Component.DecoderBridge.Wire.Thms

/-!
# The two test binaries as instances of the open behavioural goals

`starts_of`, `trap_of`: the reference halves of `InstTestsRef.starts_agree` and `trap_agree`
follow from `Task.startAdequacyChecked` and `Task.failAdequacy` applied to the test binaries: their
hypotheses (both readings succeed, the REF reading is valid and, for `starts`, in the fragment
`InFrag` (`Wire.Thms.starts_inFrag`, a kernel check of the syntax) and passes the root checks
(`starts_rootChecked`, `decide +kernel`), the import is `f: func(u32)`, the first export is
`get`, the IR play) are discharged by the existing theorems, with no new run of either machine.
(`Task.startAdequacy`, without the root checks, is false: `DecoderBridge.ParamName`.) The conclusions are also proved unconditionally, by executing the reference machine
(`InstTestsRef.starts_agree`, `trap_agree`); so the two goals hold on these two binaries.
Neither goal is proved in general.
-/

public section

namespace Silmaril.Wasm.Component.DecoderBridge

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstTests Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Reference.Core3Adder (first)

/-- `starts.wasm` passes the reference machine's root checks. -/
theorem starts_rootChecked : RootChecked startsRef := by decide +kernel

/-- **`starts.wasm` is an instance of `Task.startAdequacyChecked`.** -/
theorem starts_of (h : Task.startAdequacyChecked) :
    (([some [toRefVal (.u32 42)]] : List (Option (List Value.Val))),
        ((), logOfCalls startsTrace)) ∈
      sessRunFrom first.prof (Host.ofEmbedder embL) hostConfigX startsRef (importArgs hostI)
        [("get", [])] :=
  h startsBytes startsComp startsRef startsTrace "get" [.u32 42] parse_starts decodeRef_starts
    starts_valid starts_inFrag starts_rootChecked rfl rfl (by simp [startsTrace]) (starts_inst _)

/-- **`trap.wasm` is an instance of `Task.failAdequacy`.** -/
theorem trap_of (h : Task.failAdequacy) :
    InstResult.traps ∈
      instBehaviours first.prof (Host.ofEmbedder embL) hostConfigX trapRef (importArgs hostI) :=
  h trapBytes trapComp trapRef parse_trap decodeRef_trap trap_valid rfl (trap_inst _)

end Silmaril.Wasm.Component.DecoderBridge
