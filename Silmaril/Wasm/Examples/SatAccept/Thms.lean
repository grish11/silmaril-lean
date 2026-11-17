module

public import Silmaril.Wasm.Examples.SatAccept.Defs
public import Silmaril.Wasm.Verify.FnSpec.Thms
public import Silmaril.Wasm.Game.SpecInst.Defs
public import Silmaril.Wasm.Game.Accept.Export.Defs
import Silmaril.Proofs.Wasm.Examples.SatAccept.Runs

/-!
# The SAT model-witness acceptor as a core Wasm module: theorems

Verified against Core 3.0 small-step execution at every numerics profile and every host
relation (partial correctness with safety: every run that ends returns normally and meets the
postcondition; no run traps). Proofs in `Silmaril.Proofs.Wasm.Examples.SatAccept`.

* **`cabi_realloc`** meets `reallocSpec` (`realloc_verified`): from any heap pointer `t` and for
  every alignment (also `0` and non-powers of two) it returns `(reallocRes t al n).1`, sets the
  heap pointer to `(reallocRes t al n).2` and changes nothing else. `reallocRes_ok`: the block
  returned lies in memory above `t` and the new pointer is its end, or the answer is `memBytes`
  with the pointer at `memBytes` (the non-overlap property: blocks returned within memory lie
  above every earlier block). `realloc_returns`: every returning run.
* **`check-stream`** meets `streamSpec` (`stream_verified`): with the stream words and the model
  words in memory it answers `satStream`, leaves memory unchanged and resets the heap pointer to
  `heapBase`; `stream_returns`: every returning run.
* **`check-nested`** meets `nestedSpec` (`nested_verified`): with the nested input in memory
  (`NestedIn`) it answers `satNested`; `nested_returns`: every returning run.
* What the loops compute: `satStream_eq`, `satNested_eq` (the answers as the model check
  `modelPre` and the stream run `streamRun`, resp. the clause checks `clauseOk`).
* **The instance** (`isSpecInstance`): `prog` validates, is allocated without a start function,
  and exports `cabi_realloc`, `check-stream` and `check-nested` as functions `0`, `1`, `2`
  (`export_realloc`, `export_stream`, `export_nested`) of type `[i32 i32 i32 i32] → [i32]`; its
  functions have the code of `prog` (`funcs_code`), memory address `0` and global address `1`
  (`funcs_mems`, `funcs_globals`); the heap pointer starts at `heapBase` (`globals`; global
  address `0` belongs to the auxiliary instance that evaluates constant expressions).

**Scope.** Total correctness (termination) is not shown, and no component-level (canonical
ABI) statement is made here.
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.SatAccept

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Verify Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Logic.VC (globalVal setGlobalIdx)
open Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Logic.SAT.Carrier (S32 satStream satNested)

/-! ## The functions -/

/-- **`cabi_realloc` meets its specification.** -/
theorem realloc_verified : Verified prog 0 reallocSpec :=
  ⟨_, rfl, Silmaril.Proofs.Wasm.Examples.SatAccept.realloc_vc⟩

/-- **`check-stream` meets its specification.** -/
theorem stream_verified : Verified prog 1 streamSpec :=
  ⟨_, rfl, Silmaril.Proofs.Wasm.Examples.SatAccept.stream_vc⟩

/-- **`check-nested` meets its specification.** -/
theorem nested_verified : Verified prog 2 nestedSpec :=
  ⟨_, rfl, Silmaril.Proofs.Wasm.Examples.SatAccept.nested_vc⟩

/-- **The allocator's non-overlap property.** -/
theorem reallocRes_ok (t al n : BitVec 32) :
    ReallocOk t n (reallocRes t al n).1 (reallocRes t al n).2 :=
  Silmaril.Proofs.Wasm.Examples.SatAccept.reallocRes_ok t al n

/-- The stream answer as the loops compute it. -/
theorem satStream_eq (P M : List S32) : satStream P M =
    (modelPre M M.length && (streamRun M P).1 && P.getLast?.all (· == 0)) :=
  Silmaril.Proofs.Wasm.Examples.SatAccept.satStream_eq P M

/-- The nested answer as the loops compute it. -/
theorem satNested_eq (N : List (List S32)) (M : List S32) :
    satNested N M = (modelPre M M.length && N.all (clauseOk M)) :=
  Silmaril.Proofs.Wasm.Examples.SatAccept.satNested_eq N M

variable {P : Profile} {host : HostSemantics Nat} {s : Store Nat} {a : Nat} {fi : FuncInst Nat}
  {ps rs : Validation.Ty (.list .val)} {ma : Nat} {mt : MemoryType} {B : ByteArray}

/-- **Every returning run of `cabi_realloc`**: the result and the heap pointer are
`reallocRes`, nothing else changes, and the block is fresh (`ReallocOk`). -/
theorem realloc_returns {o os al n t : BitVec 32} (hfi : s.funcs[a]? = some fi)
    (hc : fi.code = .wasm prog.funcs[0]) (he : Validation.Expand fi.type (.func ps rs))
    (hps : ps.length = 4) (hrs : rs.length = 1) (hg : globalVal s fi.module 0 = some (.i32 t))
    {s' : Store Nat} {f' : Frame} {res : List Val}
    (hs : Steps P host (invoke s a [.i32 o, .i32 os, .i32 al, .i32 n]) ⟨s', f', vals res⟩) :
    res = [.i32 (reallocRes t al n).1] ∧
      s' = setGlobalIdx s fi.module 0 (.i32 (reallocRes t al n).2) ∧
      ReallocOk t n (reallocRes t al n).1 (reallocRes t al n).2 :=
  Silmaril.Proofs.Wasm.Examples.SatAccept.realloc_returns hfi hc he hps hrs hg hs

/-- **Every returning run of `check-stream` answers `satStream`**, memory unchanged, heap
pointer reset. -/
theorem stream_returns {pp pl mp ml : BitVec 32} (hfi : s.funcs[a]? = some fi)
    (hc : fi.code = .wasm prog.funcs[1]) (he : Validation.Expand fi.type (.func ps rs))
    (hps : ps.length = 4) (hrs : rs.length = 1) (hmem : MemAt s fi.module ma mt B)
    (hsz : B.size = memBytes) (hP : pp.toNat + 4 * pl.toNat ≤ B.size)
    (hM : mp.toNat + 4 * ml.toNat ≤ B.size) (hg : (globalVal s fi.module 0).isSome)
    {s' : Store Nat} {f' : Frame} {res : List Val}
    (hs : Steps P host (invoke s a [.i32 pp, .i32 pl, .i32 mp, .i32 ml]) ⟨s', f', vals res⟩) :
    s' = setGlobalIdx s fi.module 0 (.i32 (BitVec.ofNat 32 heapBase)) ∧
      res = [.i32 (if satStream (wordsAt B pp.toNat pl.toNat) (wordsAt B mp.toNat ml.toNat)
        then 1 else 0)] :=
  Silmaril.Proofs.Wasm.Examples.SatAccept.stream_returns hfi hc he hps hrs hmem hsz hP hM hg hs

/-- **Every returning run of `check-nested` answers `satNested`**, memory unchanged, heap
pointer reset. -/
theorem nested_returns {pp pl mp ml : BitVec 32} (hfi : s.funcs[a]? = some fi)
    (hc : fi.code = .wasm prog.funcs[2]) (he : Validation.Expand fi.type (.func ps rs))
    (hps : ps.length = 4) (hrs : rs.length = 1) (hmem : MemAt s fi.module ma mt B)
    (hsz : B.size = memBytes) (hN : NestedIn B pp.toNat pl.toNat)
    (hM : mp.toNat + 4 * ml.toNat ≤ B.size) (hg : (globalVal s fi.module 0).isSome)
    {s' : Store Nat} {f' : Frame} {res : List Val}
    (hs : Steps P host (invoke s a [.i32 pp, .i32 pl, .i32 mp, .i32 ml]) ⟨s', f', vals res⟩) :
    s' = setGlobalIdx s fi.module 0 (.i32 (BitVec.ofNat 32 heapBase)) ∧
      res = [.i32 (if satNested (nestedAt B pp.toNat pl.toNat) (wordsAt B mp.toNat ml.toNat)
        then 1 else 0)] :=
  Silmaril.Proofs.Wasm.Examples.SatAccept.nested_returns hfi hc he hps hrs hmem hsz hN hM hg hs

/-! ## The instance -/

set_option maxRecDepth 100000

theorem isSpecInstance : IsSpecInstance prog specMT specInst specPrep.1 :=
  Silmaril.Proofs.Wasm.Examples.SatAccept.isSpecInstance

theorem export_realloc : exportFunc? specPrep.1.frame.module "cabi_realloc" = some 0 :=
  Silmaril.Proofs.Wasm.Examples.SatAccept.t_export_realloc

theorem export_stream : exportFunc? specPrep.1.frame.module "check-stream" = some 1 :=
  Silmaril.Proofs.Wasm.Examples.SatAccept.t_export_stream

theorem export_nested : exportFunc? specPrep.1.frame.module "check-nested" = some 2 :=
  Silmaril.Proofs.Wasm.Examples.SatAccept.t_export_nested

theorem funcs_code : specPrep.1.store.funcs.map FuncInst.code =
    [.wasm prog.funcs[0], .wasm prog.funcs[1], .wasm prog.funcs[2]] :=
  Silmaril.Proofs.Wasm.Examples.SatAccept.t_fcode

theorem funcs_mems : specPrep.1.store.funcs.map (fun fi => fi.module.mems) = [[0], [0], [0]] :=
  Silmaril.Proofs.Wasm.Examples.SatAccept.t_fmems

theorem funcs_globals :
    specPrep.1.store.funcs.map (fun fi => fi.module.globals) = [[1], [1], [1]] :=
  Silmaril.Proofs.Wasm.Examples.SatAccept.t_fglobals

theorem globals : specPrep.1.store.globals.map (·.value) =
    [.i32 (BitVec.ofNat 32 heapBase), .i32 (BitVec.ofNat 32 heapBase)] :=
  Silmaril.Proofs.Wasm.Examples.SatAccept.t_globals

end Silmaril.Wasm.Examples.SatAccept
