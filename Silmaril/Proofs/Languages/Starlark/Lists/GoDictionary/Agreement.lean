module

public import Silmaril.Languages.Starlark.Lists.GoDictionary.Operational.Defs
import Silmaril.Languages.Starlark.Lists.Comparison.Thms
import Silmaril.Languages.Starlark.Binary64.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Lists (Heap Value)
open Silmaril.Languages.Starlark.Lists.GoDictionary

theorem intHash_toNat (value : Int) :
    (intHash value).toNat =
      (12582917 * ((if -(2 ^ 31) ≤ value ∧ value < 2 ^ 31
        then (value % 2 ^ 32).toNat else value.natAbs) + 3)) % 2 ^ 32 := by
  unfold intHash intLowWord
  split <;> simp [UInt32.toNat_ofNat]

theorem mixes_iff (increment : UInt32) (words : List UInt32) (hash mult out : UInt32) :
    Mixes increment words hash mult out ↔ mixFields increment words hash mult = out := by
  induction words generalizing hash mult with
  | nil =>
    constructor
    · intro h
      cases h
      rfl
    · intro h
      subst out
      exact .empty hash mult
  | cons word rest ih =>
    constructor
    · intro h
      cases h with
      | field h => exact (ih ..).mp h
    · intro h
      exact .field ((ih ..).mpr h)

private theorem fieldHashes_iff {next : Lists.Value → UInt32 → Prop}
    {hash : Lists.Value → Except Error UInt32}
    (agree : ∀ value word, next value word ↔ hash value = .ok word)
    (fields : List Lists.Value) (words : List UInt32) :
    FieldHashes next fields words ↔ fields.mapM hash = .ok words := by
  constructor
  · intro h
    induction h with
    | empty => rfl
    | field checked _ ih =>
      simp [List.mapM_cons, (agree ..).mp checked, ih, bind, Except.bind, pure, Except.pure]
  · intro ran
    induction fields generalizing words with
    | nil =>
      simp [pure, Except.pure] at ran
      subst words
      exact .empty
    | cons key rest ih =>
      cases h : hash key with
      | error error => simp [List.mapM_cons, h, bind, Except.bind] at ran
      | ok word =>
        cases tail : rest.mapM hash with
        | error error => simp [List.mapM_cons, h, tail, bind, Except.bind] at ran
        | ok hashes =>
          simp [List.mapM_cons, h, tail, bind, Except.bind, pure, Except.pure] at ran
          subst words
          exact .field ((agree ..).mpr h) (ih hashes tail)

theorem hashesAt_iff (heap : Heap) (depth : Nat) (key : Lists.Value) (out : UInt32) :
    HashesAt heap depth key out ↔ hashAt heap depth key = .ok out := by
  induction depth generalizing key out with
  | zero => simp [HashesAt, hashAt]
  | succ depth ih =>
    rw [HashesAt]
    constructor
    · intro ran
      cases ran with
      | none | boolean | integer => simp [hashAt, scalarHash]
      | floating decoded => simp [hashAt, scalarHash, (Binary64.decodes_iff_decode ..).mp decoded]
      | tuple read fields mixed =>
        simp [hashAt, read, (fieldHashes_iff ih ..).mp fields, tupleHash, (mixes_iff ..).mp mixed,
          bind, Except.bind, Except.mapError, pure, Except.pure]
    · intro ran
      cases key with
      | scalar value =>
        simp only [hashAt, Except.ok.injEq] at ran
        subst out
        cases value with
        | none => exact .none
        | bool flag => exact .boolean flag
        | int value => exact .integer value
        | float bits => exact .floating ((Binary64.decodes_iff_decode ..).mpr rfl)
      | tuple address =>
        cases cell : heap.tupleFields address with
        | error error => simp [hashAt, cell, bind, Except.bind, Except.mapError] at ran
        | ok fields =>
          cases done : fields.mapM (hashAt heap depth) with
          | error error => simp [hashAt, cell, done, bind, Except.bind, Except.mapError] at ran
          | ok words =>
            simp [hashAt, cell, done, bind, Except.bind, Except.mapError, pure, Except.pure] at ran
            exact .tuple cell ((fieldHashes_iff ih ..).mpr done) ((mixes_iff ..).mpr ran)
      | _ => simp [hashAt] at ran

theorem looksUp_iff (heap : Heap) (bucket : Bucket) (key : Lists.Value)
    (out : Except Error (UInt32 × Option (Row × Nat))) :
    LooksUp heap bucket key out ↔ lookupWithHash heap bucket key = out := by
  have probes := fun candidates =>
    Lists.Comparison.probes_iff_probe (fun (candidate : Row × Nat) =>
      Lists.Comparison.equalAt_iff heap Lists.Comparison.defaultDepth key candidate.1.key) candidates
  constructor
  · intro h
    cases h with
    | hashError rejected => simp [lookupWithHash, rejected, bind, Except.bind]
    | @probed hash result hashed tested =>
      have hashed' := (hashesAt_iff ..).mp hashed
      have tested' := (probes ..).mp tested
      cases result <;> simp [lookupWithHash, hashKey, hashed', tested',
        bind, Except.bind, Except.mapError, pure, Except.pure, Except.map]
  · intro h
    subst out
    cases hashed : hashKey heap key with
    | error error =>
      simpa [lookupWithHash, hashed, bind, Except.bind] using
        LooksUp.hashError (bucket := bucket) hashed
    | ok hash =>
      let candidates := bucket.candidates (storedHash hash)
      cases tested : Lists.Comparison.probe
          (fun candidate : Row × Nat => Lists.Comparison.equalAt heap Lists.Comparison.defaultDepth key candidate.1.key)
          candidates with
      | error error =>
        simpa [lookupWithHash, hashed, tested, candidates, bind, Except.bind, Except.mapError, Except.map] using
          LooksUp.probed ((hashesAt_iff ..).mpr hashed) ((probes candidates _).mpr tested)
      | ok selected =>
        simpa [lookupWithHash, hashed, tested, candidates, bind, Except.bind, Except.mapError, Except.map,
          pure, Except.pure] using
          LooksUp.probed ((hashesAt_iff ..).mpr hashed) ((probes candidates _).mpr tested)

end Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary
