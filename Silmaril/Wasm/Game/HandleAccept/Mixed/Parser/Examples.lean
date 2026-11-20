module

public import Silmaril.Wasm.Game.HandleAccept.Mixed.Parser.Thms
public import Silmaril.Wasm.Resource.Replay.Defs
import Silmaril.Wasm.Execution.Core.SpecProfile
import Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Replay

/-!
# A parser that builds its tree: examples (non-vacuity)

`listParse_sound` bounds the mixed relation of `listParse` by `listR`. Here it is shown
non-empty by running the module: the call `parse(7)` (candidate argument `7`) is replayed on the
verified interpreter **including its export answer**, with a host returning the fresh handles
`1, 2, 3` to `word`, `nil`, `cons` (`listScript`), by kernel evaluation: the module calls
`word(7) = 1`, `nil() = 2`, `cons(1, 2) = 3` and answers `3`. Simulating the mixed host (store
semantics) along the decoded events resolves `3` to `(7)` in the store the play built
(`Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.mem_moduleMixedRel_of_replay`).

**Profiles and policies.** Every profile `P` admitting the deterministic steps of the interpreter
(hypothesis `hP`; every specification profile `Profile.spec nd {}`, the `_spec` corollaries),
every writer policy whose sentinel, if any, is `0`, and every parsing policy with sentinel `0`.

* `listParse_relates_7`: `([7], (7))` is in the mixed relation of `listParse`;
* `listParse_rel_eq_7`: with `listParse_sound`, the relation restricted to the input `[7]` is
  exactly `{([7], (7))}`, for the policies of `listParse_sound`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Mixed.Parser

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Verify
  Silmaril.Wasm.Resource Silmaril.Formats Silmaril.Accept.Handle Silmaril.Accept.Parse
  Silmaril.Wasm.Game.HandleAccept.Mixed Silmaril.Wasm.Game.HandleAccept.Writers.Builders

/-- The host: the `k`-th callout returns the fresh handle `k + 1`, except `accept`, which
returns nothing. -/
def listScript : Script := fun k h _ =>
  if h = twoIx.accept then [] else [Val.i32 (BitVec.ofNat 32 (k + 1))]

section Positive

variable {P : Profile}
  (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
  {pol : Policy (BitVec 32)} (hs : ∀ r, pol.sentinel = some r → r = 0)
  {ppol : PPolicy (BitVec 32)} (h0 : ppol.sentinel = 0)
include hP hs h0

open Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed (mem_moduleMixedRel_of_replay)

theorem listParse_relates_7 :
    ([7], SExp2.ofAtoms [7]) ∈ moduleMixedRel P listParse twoIx listPix pol ppol :=
  mem_moduleMixedRel_of_replay listParse_instance hP twoIx listPix
    (bad := fun r => decide (r = 0)) (fun r h => by simp [hs r h]) (by simp [h0])
    listScript refFuel 8 ⟨0, by decide +kernel⟩ 7 (by decide +kernel)

end Positive

/-- **The relation at the input `[7]`** is exactly `([7], (7))`. -/
theorem listParse_rel_eq_7 {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
    {pol : Policy (BitVec 32)} (hsen : pol.sentinel = none) (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) {ppol : PPolicy (BitVec 32)} (h0 : ppol.sentinel = 0)
    (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) :
    {t | ([7], t) ∈ moduleMixedRel P listParse twoIx listPix pol ppol} = {SExp2.ofAtoms [7]} :=
  Set.eq_singleton_iff_unique_mem.2 ⟨listParse_relates_7 hP (fun r h => by simp [hsen] at h) h0,
    fun _ h => by obtain ⟨x, -, ⟨⟩, rfl⟩ := listParse_rel P hsen hw ha h0 hb ho h; rfl⟩

/-! ### At the specification profiles -/

theorem listParse_relates_7_spec (nd : Bool) {pol : Policy (BitVec 32)}
    (hs : ∀ r, pol.sentinel = some r → r = 0) {ppol : PPolicy (BitVec 32)}
    (h0 : ppol.sentinel = 0) :
    ([7], SExp2.ofAtoms [7]) ∈
      moduleMixedRel (Profile.spec nd {}) listParse twoIx listPix pol ppol :=
  listParse_relates_7 (fun _ _ h => Step.deterministic_refines_spec nd h) hs h0

end Silmaril.Wasm.Game.HandleAccept.Mixed.Parser
