module

public import Silmaril.Wasm.Game.HandleAccept.Writer.Sentinel.Thms
public import Silmaril.Wasm.Resource.Replay.Defs
import Silmaril.Wasm.Execution.Core.SpecProfile
import Silmaril.Proofs.Wasm.Game.HandleAccept.Writer.Replay
import Silmaril.Proofs.Wasm.Game.HandleAccept.Replay

/-!
# Sentinel-testing writer modules: examples

**Non-vacuity.** The soundness theorems of `Thms` bound the languages of `twoWordsZ` and
`twoWordsM` by the lists `(x x+1)`. Here they are shown non-empty by replaying `run(k)` on the
verified interpreter (`Silmaril.Wasm.Resource.replayExport`, kernel evaluation) with hosts
returning fresh handles that avoid the sentinel, and simulating the writer host (store
semantics) along the decoded trace
(`Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.mem_consWLang_of_replay`):

* `twoWordsZ`, sentinel `0`, handles `1, 2, 3, …` (`succScript`): `(0 1)` and `(5 6)`
  (`twoWordsZ_accepts_0`, `twoWordsZ_accepts_5`);
* `twoWordsM`, sentinel `-1`, handles `0, 1, 2, …` (`zeroScript`; the handle `0` is a valid
  handle under the sentinel `-1`): `(0 1)` and `(5 6)` (`twoWordsM_accepts_0`,
  `twoWordsM_accepts_5`).

**Failures.** With a host whose first answer is the sentinel (`failScript s`), the decoded
replay of `run(0)` is a trace of the module that receives the sentinel (`retAny`) and consists
of writes and export calls only: the module returned without calling `accept`. So this run
accepts nothing, under every policy without undefined writes (`twoWordsZ_fail_accepts_nothing`,
`twoWordsM_fail_accepts_nothing`, through `accepts_writeOrEnter`). A failure at the outer
`cons` (`lateFailScript`), after four successful allocations, likewise accepts nothing
(`twoWordsZ_lateFail_accepts_nothing`).

**Profiles.** Every profile `P` admitting the deterministic steps of the interpreter
(hypothesis `hP`); every specification profile `Profile.spec nd {}` (the `_spec` corollaries).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Writers.Sentinel

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Verify
  Silmaril.Wasm.Resource Silmaril.Formats Silmaril.Formats.Api Silmaril.Accept
  Silmaril.Accept.Handle Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Writers.Builders
open Silmaril.Proofs.Wasm.Game.HandleAccept.Writers (consWAsk consWAns mem_consWLang_of_replay)
open Silmaril.Proofs.Wasm.Game.HandleAccept.Replay (rdecG_mem_handleTraces)

/-! ## Hosts -/

/-- The `k`-th callout returns the handle `k` (so `0` first), except `accept`. -/
def zeroScript : Script := fun k h _ =>
  if h = twoIx.accept then [] else [Val.i32 (BitVec.ofNat 32 k)]

/-- The first callout returns the sentinel `s`, the `k`-th one after it the handle `k + 1`. -/
def failScript (s : BitVec 32) : Script := fun k h _ =>
  if h = twoIx.accept then [] else if k = 0 then [Val.i32 s] else [Val.i32 (BitVec.ofNat 32 (k + 1))]

/-- The fifth callout (the outer `cons`) returns the sentinel `s`. -/
def lateFailScript (s : BitVec 32) : Script := fun k h _ =>
  if h = twoIx.accept then [] else if k = 4 then [Val.i32 s] else [Val.i32 (BitVec.ofNat 32 (k + 1))]

/-- The `k`-th callout returns the fresh handle `k + 1`, except `accept`. -/
def succScript : Script := fun k h _ =>
  if h = twoIx.accept then [] else [Val.i32 (BitVec.ofNat 32 (k + 1))]

/-! ## Non-vacuity -/

section Positive

variable {P : Profile}
  (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
include hP

theorem twoWordsZ_accepts_0 {pol : Policy (BitVec 32)} (hs : pol.sentinel = some 0) :
    SExp2.ofAtoms [0, 1] ∈ moduleConsWLang P twoWordsZ twoIx pol :=
  mem_consWLang_of_replay twoWordsZ_instance hP twoIx (bad := fun r => decide (r = 0))
    (fun r h => by simp [hs] at h; simp [h]) succScript refFuel 8 ⟨0, by decide +kernel⟩ 0
    (by decide +kernel)

theorem twoWordsZ_accepts_5 {pol : Policy (BitVec 32)} (hs : pol.sentinel = some 0) :
    SExp2.ofAtoms [5, 6] ∈ moduleConsWLang P twoWordsZ twoIx pol :=
  mem_consWLang_of_replay twoWordsZ_instance hP twoIx (bad := fun r => decide (r = 0))
    (fun r h => by simp [hs] at h; simp [h]) succScript refFuel 8 ⟨0, by decide +kernel⟩ 5
    (by decide +kernel)

theorem twoWordsM_accepts_0 {pol : Policy (BitVec 32)} (hs : pol.sentinel = some (-1)) :
    SExp2.ofAtoms [0, 1] ∈ moduleConsWLang P twoWordsM twoIx pol :=
  mem_consWLang_of_replay twoWordsM_instance hP twoIx (bad := fun r => decide (r = -1))
    (fun r h => by simp [hs] at h; simp [h]) zeroScript refFuel 8 ⟨0, by decide +kernel⟩ 0
    (by decide +kernel)

theorem twoWordsM_accepts_5 {pol : Policy (BitVec 32)} (hs : pol.sentinel = some (-1)) :
    SExp2.ofAtoms [5, 6] ∈ moduleConsWLang P twoWordsM twoIx pol :=
  mem_consWLang_of_replay twoWordsM_instance hP twoIx (bad := fun r => decide (r = -1))
    (fun r h => by simp [hs] at h; simp [h]) zeroScript refFuel 8 ⟨0, by decide +kernel⟩ 5
    (by decide +kernel)

end Positive

theorem twoWordsZ_accepts_0_spec (nd : Bool) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = some 0) :
    SExp2.ofAtoms [0, 1] ∈ moduleConsWLang (Profile.spec nd {}) twoWordsZ twoIx pol :=
  twoWordsZ_accepts_0 (fun _ _ h => Step.deterministic_refines_spec nd h) hs

theorem twoWordsM_accepts_0_spec (nd : Bool) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = some (-1)) :
    SExp2.ofAtoms [0, 1] ∈ moduleConsWLang (Profile.spec nd {}) twoWordsM twoIx pol :=
  twoWordsM_accepts_0 (fun _ _ h => Step.deterministic_refines_spec nd h) hs

/-! ## Failures -/

section Failures

variable {P : Profile}
  (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
  {pol : Policy (BitVec 32)} (hw : pol.onWrite ≠ .ub)
include hP hw

/-- **A failed first write accepts nothing** (`twoWordsZ`): the replay of `run(0)` whose first
write returns the sentinel `0` is a trace of the module, receives the sentinel, and accepts
nothing (every policy without undefined writes). -/
theorem twoWordsZ_fail_accepts_nothing :
    ∃ t ∈ moduleTraces P twoWordsZ (consWDecAsk twoIx) (consWDecAns twoIx),
      retAny 0 t = true ∧ (writer (consW (BitVec 64)) pol).accepts t = ∅ :=
  ⟨_, rdecG_mem_handleTraces twoWordsZ_instance hP (some .enter) _ _ (consWAsk twoIx)
      (consWAns twoIx) (fun _ => rfl)
      (Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.consWDecAns_eq twoIx) (failScript 0)
      refFuel 8 ⟨0, by decide +kernel⟩ 0,
    by decide +kernel, accepts_writeOrEnter hw (List.all_eq_true.1 (by decide +kernel))⟩

/-- **A failed first write accepts nothing** (`twoWordsM`, sentinel `-1`). -/
theorem twoWordsM_fail_accepts_nothing :
    ∃ t ∈ moduleTraces P twoWordsM (consWDecAsk twoIx) (consWDecAns twoIx),
      retAny (-1) t = true ∧ (writer (consW (BitVec 64)) pol).accepts t = ∅ :=
  ⟨_, rdecG_mem_handleTraces twoWordsM_instance hP (some .enter) _ _ (consWAsk twoIx)
      (consWAns twoIx) (fun _ => rfl)
      (Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.consWDecAns_eq twoIx) (failScript (-1))
      refFuel 8 ⟨0, by decide +kernel⟩ 0,
    by decide +kernel, accepts_writeOrEnter hw (List.all_eq_true.1 (by decide +kernel))⟩

/-- **A failed last write accepts nothing** (`twoWordsZ`): the outer `cons` returns the
sentinel after four successful allocations. -/
theorem twoWordsZ_lateFail_accepts_nothing :
    ∃ t ∈ moduleTraces P twoWordsZ (consWDecAsk twoIx) (consWDecAns twoIx),
      t.length = 6 ∧ retAny 0 t = true ∧ (writer (consW (BitVec 64)) pol).accepts t = ∅ :=
  ⟨_, rdecG_mem_handleTraces twoWordsZ_instance hP (some .enter) _ _ (consWAsk twoIx)
      (consWAns twoIx) (fun _ => rfl)
      (Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.consWDecAns_eq twoIx) (lateFailScript 0)
      refFuel 8 ⟨0, by decide +kernel⟩ 0,
    by decide +kernel, by decide +kernel,
    accepts_writeOrEnter hw (List.all_eq_true.1 (by decide +kernel))⟩

end Failures

end Silmaril.Wasm.Game.HandleAccept.Writers.Sentinel
