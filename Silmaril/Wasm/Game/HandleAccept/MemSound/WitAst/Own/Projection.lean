module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Cons.Thms
public import Silmaril.Semantics.Accept.Host.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwn
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnMod
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnLive

/-!
# Owned resource handles: analysis of successful writer events

This module interprets the legacy writer trace projection. It is not an implementation of a
Core import: failure to project an event does not make the running export trap. For an actual
checked Core session, import `Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own`.

The resource-table semantics of `own<r>` payloads (`Own.Defs`): a raw `node` write is resolved
in the **current** resource table, which consumes the moved handles.

**Resolution** (explicit environment dependence):

* `resolveOp_congr`: **the resolution of a raw write reads the table only at the handles it
  moves** (`movedOp`), and the table after the move is the table with exactly those handles
  consumed (`resolveOp_some`);
* `resolveOp_dead`: a move consumes its handles; `resolveOp_of_dead`: a dead (moved, missing or
  foreign-type) handle does not resolve; `resolveOp_mono`: a table reached by moves resolves
  as the initial one wherever it resolves.

**Linearity** (trace dependence):

* `no_second_move`: **a consumed handle is never consumed again**: after a write moves `x`, at
  every later point of every run a write moving `x` does not resolve;
* `unresolved_step`: such a write is an invalid write: it gives no handle a meaning and accepts
  nothing unless the policy makes invalid writes undefined (`onWrite = .ub`);
* `run_congr`, `ownLang_congr`: **runs and the language depend on the initial table only at the
  handles the traces move** (`tmoved`);
* `ownLang_subset_via`: without undefined writes, the resource host is bounded by the stateless
  reading `viaRT` in the initial table; `ownLang_eq_of_linear`: on traces that move no handle
  twice it **is** the stateless reading;
* `linear_of_ob`: a trace whose moves (`ownGives`, after the `take`s of the initially owned
  handles) are accepted by the ownership protocol `Silmaril.Wasm.Resource.obProto` moves no
  handle twice, and only owned ones; so `ownLang_eq_of_ob`: on such traces the resource host
  is the stateless reading.

**Borrows** (`borrow_rejected`, `readVal_borrow`): a `borrow` is never decoded, and a `node`
call of a tag with a `borrow` payload field is no event: no stored tree holds a borrow.

**The projected language of `ownMod`**, for every profile, every resource table `rt₀` and every policy without
a sentinel or undefined behaviour, against every environment admitted by `hiReply`:

* `ownMod_sound`: it accepts only `res(rep)` for the representation `rep` of the live
  `own<0>` handle `1` of `rt₀` (`ownL rt₀`); `ownMod_dead`: **nothing when the table has no
  such handle** (dead, missing or of another resource type);
* `ownMod_live`: it accepts `res(rep)` when the handle is live (for every policy);
* `ownMod_lang`: **its language is exactly `{res(rep)}`**.

**The example `twiceMod`** (the handle `1` moved twice): `twice_traces` (its session's raw
trace), `twice_accepts`: under the resource host that trace accepts nothing, in every table,
for every policy without undefined behaviour; `twice_via`: the stateless reading accepts
`res(rep)` on it, so consumption is what rejects the double move.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept Silmaril.Accept.IO Silmaril.Accept.Handle
  Silmaril.Formats Silmaril.Formats.Api Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Cons Silmaril.Wasm.Game.HandleAccept.MemSound.Hi

/-! ## Resolution -/

variable {S : WitSig}

/-- **Resolution reads the table only at the moved handles.** -/
theorem resolveOp_congr {rt rt' : RT} {rop : ROp S} (h : ∀ x ∈ movedOp S rop, rt x = rt' x) :
    resolveOp S rt' rop =
      (resolveOp S rt rop).map fun p => (p.1, rt'.killAll (movedOp S rop)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwn.resolveOp_congr h

theorem resolveOp_some {rt rt' : RT} {rop : ROp S} {op : Op S}
    (h : resolveOp S rt rop = some (op, rt')) :
    (movedOp S rop).Nodup ∧ rt' = rt.killAll (movedOp S rop) ∧
      ∃ a, resolveVals rt (S.params rop.1) rop.2 = some a ∧ op = ⟨rop.1, a⟩ :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwn.resolveOp_some h

/-- **A move consumes its handles.** -/
theorem resolveOp_dead {rt rt' : RT} {rop : ROp S} {op : Op S}
    (h : resolveOp S rt rop = some (op, rt')) : ∀ x ∈ movedOp S rop, rt'.Dead x :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwn.resolveOp_dead h

/-- **A dead handle does not resolve.** -/
theorem resolveOp_of_dead {rt : RT} {rop : ROp S} {x : BitVec 32} (hx : x ∈ movedOp S rop)
    (hd : rt.Dead x) : resolveOp S rt rop = none :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwn.resolveOp_of_dead hx hd

theorem resolveOp_mono {rt rt₀ rt' : RT} {rop : ROp S} {op : Op S} (hle : rt.Le rt₀)
    (h : resolveOp S rt rop = some (op, rt')) :
    resolveOp S rt₀ rop = some (op, rt₀.killAll (movedOp S rop)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwn.resolveOp_mono hle h

/-! ## Linearity -/

variable {X : Type} {W : Writer (Op S) X} {pol : Policy (BitVec 32)}

/-- **A consumed handle is never consumed again**: after a write moves `x`, a later write moving
`x` does not resolve, at any point of any continuation. -/
theorem no_second_move {rt₀ : RT} {s₁ s₂ s₃ : OwnState X} {rop rop' : ROp S} {op : Op S}
    {es : List (WEv (ROp S) (BitVec 32))} {B : Set X} {x : BitVec 32}
    (hm : resolveOp S s₁.rt rop = some (op, s₂.rt)) (hx : x ∈ movedOp S rop)
    (hr : (ownHost W pol rt₀).Run s₂ es s₃ B) (hx' : x ∈ movedOp S rop') :
    resolveOp S s₃.rt rop' = none :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwn.no_second_move hm hx hr hx'

/-- **An unresolved write gives no handle a meaning**, and accepts nothing unless invalid writes
are undefined. -/
theorem unresolved_step {s s' : OwnState X} {rop : ROp S} {args : List (BitVec 32)}
    {r : BitVec 32} {A : Set X} (hs : OwnStep W pol s (.write rop args r) s' A)
    (hl : s.w.phase = .live) (hn : resolveOp S s.rt rop = none) :
    s'.w.store = s.w.store ∧ (A = ∅ ∨ pol.onWrite = .ub) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwn.unresolved_step hs hl hn

/-- **Runs depend on the table only at the handles they move.** -/
theorem run_congr {rt₀ rt₀' : RT} {es : List (WEv (ROp S) (BitVec 32))} {rt₁ rt₂ : RT}
    {w : WState (BitVec 32) X} {s : OwnState X} {A : Set X}
    (hr : (ownHost W pol rt₀).Run ⟨rt₁, w⟩ es s A) (h : ∀ x ∈ tmoved S es, rt₁ x = rt₂ x) :
    ∃ rt₂', (ownHost W pol rt₀').Run ⟨rt₂, w⟩ es ⟨rt₂', s.w⟩ A :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwn.run_congr hr h

/-- **The language depends on the initial table only at the moved handles.** -/
theorem ownLang_congr {rt₀ rt₀' : RT} {T : Set (List (WEv (ROp S) (BitVec 32)))}
    (h : ∀ t ∈ T, ∀ x ∈ tmoved S t, rt₀ x = rt₀' x) :
    ownLang W pol rt₀ T = ownLang W pol rt₀' T :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwn.ownLang_congr h

/-- **The stateless reading bounds the resource host** (no undefined writes). -/
theorem ownLang_subset_via (rt₀ : RT) (hw : pol.onWrite ≠ .ub)
    (T : Set (List (WEv (ROp S) (BitVec 32)))) :
    ownLang W pol rt₀ T ⊆ writerLang (viaRT W rt₀) pol T :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwn.ownLang_subset_via rt₀ hw T

/-- **On traces moving no handle twice, the resource host is the stateless reading.** -/
theorem ownLang_eq_of_linear (rt₀ : RT) (hw : pol.onWrite ≠ .ub)
    {T : Set (List (WEv (ROp S) (BitVec 32)))} (hT : ∀ t ∈ T, (tmoved S t).Nodup) :
    ownLang W pol rt₀ T = writerLang (viaRT W rt₀) pol T :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwn.ownLang_eq_of_linear rt₀ hw hT

/-- **A trace accepted by the ownership protocol moves no handle twice**, and only handles the
module owned initially. -/
theorem linear_of_ob {L₀ : List (BitVec 32)} {es : List (WEv (ROp S) (BitVec 32))}
    (hL : L₀.Nodup)
    (h : (Silmaril.Wasm.Resource.obProto (BitVec 32)).Accepts
      (L₀.map Silmaril.Wasm.Resource.OEv.take ++ ownGives S es)) :
    (tmoved S es).Nodup ∧ ∀ x ∈ tmoved S es, x ∈ L₀ :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwn.linear_of_ob hL h

/-- **Plays respecting the ownership protocol are valid**: on traces whose moves the protocol
accepts, the resource host is the stateless reading in the initial table. -/
theorem ownLang_eq_of_ob (rt₀ : RT) (hw : pol.onWrite ≠ .ub) {L₀ : List (BitVec 32)}
    (hL : L₀.Nodup) {T : Set (List (WEv (ROp S) (BitVec 32)))}
    (hT : ∀ t ∈ T, (Silmaril.Wasm.Resource.obProto (BitVec 32)).Accepts
      (L₀.map Silmaril.Wasm.Resource.OEv.take ++ ownGives S t)) :
    ownLang W pol rt₀ T = writerLang (viaRT W rt₀) pol T :=
  ownLang_eq_of_linear rt₀ hw fun t ht => (linear_of_ob hL (hT t ht)).1

/-! ## Borrows -/

/-- **A `borrow` is never decoded.** -/
theorem readVal_borrow (seg : Nat → Nat → Option (List UInt8)) (r : Nat) (bs : List UInt8) :
    readVal seg (.borrow r) bs = none := rfl

/-- **Borrow payloads are rejected in stored trees**: a decoded `node` call never names a tag
with a `borrow` payload field, so such a call is no event. -/
theorem borrow_rejected {tagOf : BitVec 32 → Option S.Tag} {o : Callout} {op : Op S}
    {hs : List (BitVec 32)} (h : Callout.witNode S tagOf o = some (op, hs)) (r : Nat) :
    PTy.borrow r ∉ S.params op.1 :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwn.witNode_borrow h r

/-- A payload vector with a `borrow` field has no value. -/
theorem vals_isEmpty_of_borrow {ps : List PTy} {r : Nat} (h : PTy.borrow r ∈ ps) :
    IsEmpty (PTy.Vals ps) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwn.vals_isEmpty_of_borrow h

/-! ## The example `ownMod` -/

/-- **`ownMod` accepts only `res(rep)`** for the representation of the live `own<0>` handle
`1` of the table. -/
theorem ownMod_sound (P : Profile) (rt₀ : RT) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    ownLang (astW ownSig.toAstSig) pol rt₀
      (witTraces (rawSig ownSig) ownRawTagOf P (ReplyEnvs hiReply) 0 ownMod {}) ⊆ ownL rt₀ :=
  (ownLang_subset_via rt₀ hw _).trans
    (rolesWriterLang_subset
      (fun _ _ h => Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.witAccept_isAccept h)
      (fun _ _ _ h => Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.witWrite_isWrite h)
      (fun ρ => by
        rw [hs]; exact Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnMod.own_sat P rt₀ ρ)
      (fun _ _ h => h) hw ha)

/-- **Without a live `own<0>` handle `1`, `ownMod` accepts nothing.** -/
theorem ownMod_dead (P : Profile) {rt₀ : RT} (hd : rt₀.lookup 0 1 = none)
    {pol : Policy (BitVec 32)} (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) :
    ownLang (astW ownSig.toAstSig) pol rt₀
      (witTraces (rawSig ownSig) ownRawTagOf P (ReplyEnvs hiReply) 0 ownMod {}) = ∅ := by
  refine Set.eq_empty_of_subset_empty fun t ht => ?_
  obtain ⟨rep, h, -⟩ := ownMod_sound P rt₀ hs hw ha ht
  rw [hd] at h
  cases h

/-- **`ownMod` accepts `res(rep)`** when `1` is a live `own<0>` handle with representation
`rep`, for every policy. -/
theorem ownMod_live (P : Profile) (pol : Policy (BitVec 32)) {rt₀ : RT} {rep : Nat}
    (h : rt₀.lookup 0 1 = some rep) :
    resTree rep ∈ ownLang (astW ownSig.toAstSig) pol rt₀
      (witTraces (rawSig ownSig) ownRawTagOf P (ReplyEnvs hiReply) 0 ownMod {}) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.WitOwn.ownMod_live P pol h

/-- **The language of `ownMod` is exactly `{res(rep)}`**: the tree holds the representation of
the moved handle, read from the table. -/
theorem ownMod_lang (P : Profile) {rt₀ : RT} {rep : Nat} (h : rt₀.lookup 0 1 = some rep)
    {pol : Policy (BitVec 32)} (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) :
    ownLang (astW ownSig.toAstSig) pol rt₀
      (witTraces (rawSig ownSig) ownRawTagOf P (ReplyEnvs hiReply) 0 ownMod {}) =
      {resTree rep} := by
  refine Set.Subset.antisymm (fun t ht => ?_) (Set.singleton_subset_iff.2 (ownMod_live P pol h))
  obtain ⟨rep', h', rfl⟩ := ownMod_sound P rt₀ hs hw ha ht
  rw [h] at h'
  cases h'
  rfl

/-! ## The example `twiceMod` -/

/-- **The raw writer trace of a session of `twiceMod`**: the handle `1` is moved twice. -/
theorem twice_traces (P : Profile) (q : BitVec 32) :
    [.enter, .write (rawRes 1) [] q, .write (rawRes 1) [] (q + 1), .accept (q + 1)] ∈
      witTraces (rawSig ownSig) ownRawTagOf P (ReplyEnvs hiReply) 0 twiceMod {} :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.WitOwn.twice_traces P q

/-- **Moving a handle twice yields no second tree**: under the resource host that trace accepts
nothing, in every table, for every policy without undefined behaviour. -/
theorem twice_accepts {X : Type} (W : Writer (Op ownSig) X) {pol : Policy (BitVec 32)}
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) (rt₀ : RT) (q : BitVec 32) :
    (ownHost W pol rt₀).accepts
      [.enter, .write (rawRes 1) [] q, .write (rawRes 1) [] (q + 1), .accept (q + 1)] = ∅ :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.WitOwn.twice_accepts W hw ha rt₀ q

/-- **The stateless reading ignores consumption**: on the same trace it accepts `res(rep)`. -/
theorem twice_via (pol : Policy (BitVec 32)) {rt₀ : RT} {rep : Nat}
    (h : rt₀.lookup 0 1 = some rep) (q : BitVec 32) (hq : pol.sentinel ≠ some q)
    (hq₁ : pol.sentinel ≠ some (q + 1)) :
    resTree rep ∈ (writer (viaRT (astW ownSig.toAstSig) rt₀) pol).accepts
      [.enter, .write (rawRes 1) [] q, .write (rawRes 1) [] (q + 1), .accept (q + 1)] :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.WitOwn.twice_via pol h q hq hq₁

end Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own
