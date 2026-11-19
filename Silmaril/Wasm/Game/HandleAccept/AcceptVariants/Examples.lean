module

public import Silmaril.Wasm.Game.HandleAccept.AcceptVariants.Thms
public import Silmaril.Wasm.Resource.Replay.Defs
import Silmaril.Wasm.Execution.Core.SpecProfile
import Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.Replay

/-!
# Accept variants: non-vacuity

Each module is run on the verified interpreter (`Silmaril.Wasm.Resource.replayExport`, call
`run(k)`) with a scripted host, and the writer host is simulated along the decoded events
(`Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.mem_consXLang_of_replay`), for every
profile admitting the interpreter's deterministic steps (`hP`).

* **`errAccept`, success**: `word` returns `1`, `accept_err(1)` answers `0` (success, a valid
  handle): the word is accepted (`errAccept_accepts_word`, sentinel `0` or none).
* **`errAccept`, error branch**: `word` **fails** and returns the sentinel `0`, `accept_err(0)`
  answers `1` (an error: `0` denotes nothing), the module falls back to `nil()`, which returns
  `1`, and accepts it (`errAccept_accepts_nil`, policy with sentinel `0`). The decoded trace is
  `enter, write (atom k) [] 0, acceptErr 0 false, write nil [] 1, accept 1`.
* **`allAccept`**: fresh handles `1, 2, 3`; `accept_all()` accepts the whole constructed set
  `{k, nil, (k)}` (`allAccept_accepts`).
* **`batchAccept`**: the kept batch `{nil, (k)}` is accepted (`batchAccept_accepts`).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.AcceptVariants

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Verify
  Silmaril.Wasm.Resource Silmaril.Formats Silmaril.Accept.Handle

/-- A script answering the callouts in order. -/
def seqScript (answers : List (List Val)) : Script := fun k _ _ => answers.getD k []

/-- `word` succeeds with `1`; `accept_err(1)` reports success. -/
def errOkScript : Script := seqScript [[Val.i32 1], [Val.i32 0]]

/-- `word` fails with the sentinel `0`; `accept_err(0)` reports an error; `nil` returns `1`. -/
def errFailScript : Script := seqScript [[Val.i32 0], [Val.i32 1], [Val.i32 1], []]

/-- Fresh handles `1`, `2`, `3`, then the bulk accepts. -/
def allScript : Script := seqScript [[Val.i32 1], [Val.i32 2], [Val.i32 3], []]

/-- `word` → `1`, drop, `nil` → `2`, `cons` → `3`, keep. -/
def batchScript : Script := seqScript [[Val.i32 1], [], [Val.i32 2], [Val.i32 3], []]

section Positive

variable {P : Profile}
  (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
include hP

open Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants (mem_consXLang_of_replay)

theorem errAccept_accepts_word {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = some 0 ∨ pol.sentinel = none) :
    SExp2.atom 7 ∈ moduleConsXLang P errAccept variantsIx pol := by
  rcases hs with hs | hs <;>
  exact mem_consXLang_of_replay errAccept_instance hP variantsIx errOkScript refFuel 4
    ⟨0, by decide +kernel⟩ 7 (by rw [hs]; decide +kernel)

/-- **The error branch**: a failed write, an error status, the fallback `nil` accepted. -/
theorem errAccept_accepts_nil {pol : Policy (BitVec 32)} (hs : pol.sentinel = some 0) :
    SExp2.nil ∈ moduleConsXLang P errAccept variantsIx pol :=
  mem_consXLang_of_replay errAccept_instance hP variantsIx errFailScript refFuel 5
    ⟨0, by decide +kernel⟩ 7 (by rw [hs]; decide +kernel)

theorem allAccept_accepts {pol : Policy (BitVec 32)} (hs : pol.sentinel = some 0) :
    SExp2.atom 3 ∈ moduleConsXLang P allAccept variantsIx pol ∧
      SExp2.nil ∈ moduleConsXLang P allAccept variantsIx pol ∧
      SExp2.cons (.atom 3) .nil ∈ moduleConsXLang P allAccept variantsIx pol :=
  ⟨mem_consXLang_of_replay allAccept_instance hP variantsIx allScript refFuel 5
      ⟨0, by decide +kernel⟩ 3 (by rw [hs]; decide +kernel),
    mem_consXLang_of_replay allAccept_instance hP variantsIx allScript refFuel 5
      ⟨0, by decide +kernel⟩ 3 (by rw [hs]; decide +kernel),
    mem_consXLang_of_replay allAccept_instance hP variantsIx allScript refFuel 5
      ⟨0, by decide +kernel⟩ 3 (by rw [hs]; decide +kernel)⟩

theorem batchAccept_accepts {pol : Policy (BitVec 32)} (hs : pol.sentinel = some 0) :
    SExp2.nil ∈ moduleConsXLang P batchAccept variantsIx pol ∧
      SExp2.cons (.atom 3) .nil ∈ moduleConsXLang P batchAccept variantsIx pol :=
  ⟨mem_consXLang_of_replay batchAccept_instance hP variantsIx batchScript refFuel 6
      ⟨0, by decide +kernel⟩ 3 (by rw [hs]; decide +kernel),
    mem_consXLang_of_replay batchAccept_instance hP variantsIx batchScript refFuel 6
      ⟨0, by decide +kernel⟩ 3 (by rw [hs]; decide +kernel)⟩

end Positive

/-- The error branch at the specification profiles. -/
theorem errAccept_accepts_nil_spec (nd : Bool) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = some 0) :
    SExp2.nil ∈ moduleConsXLang (Profile.spec nd {}) errAccept variantsIx pol :=
  errAccept_accepts_nil (fun _ _ h => Step.deterministic_refines_spec nd h) hs

end Silmaril.Wasm.Game.HandleAccept.AcceptVariants
