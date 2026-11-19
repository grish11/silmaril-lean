module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Rivest.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Thms
public import Silmaril.Formats.SExp.Family.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.RivestLive

/-!
# Byte trees and Rivest canonical trees through linear memory: exact languages

For every profile, against every environment whose replies are admitted by `pairReply` (they
keep the code, may rewrite memory, return one `i32` from `blob` and `sexp` and nothing from
`accept`):

* `bpairMod_fixed_sound`: in every fixed environment and for every policy without a failure
  sentinel, the trees `bpairMod` accepts are `bpairTree`, the list of the byte strings `61` and
  `62`;
* `bpairMod_sound`, `bpairMod_live`, `bpairMod_lang`: its writer language (store semantics) is
  exactly `{bpairTree}` for every policy without a sentinel and without undefined behaviour
  (the lower bound for every policy);
* **family instances**: `bytes_bpairMod` (`ByteSExp`, atoms `List UInt8`) and
  `rivest_bpairMod` (`RivestSExp`, octet strings `Bytes`): the language is the image of the
  family's list `(61 62)` under the atom embedding (`bytesPair_map`, `rivestPair_map`);
* `rivestPair_dotted`: the dotted (cons-cell) form of `rivestPair` reads back to it.

Upper bounds are the Hoare-logic proof of `bpairMod` under the writer contract in every fixed
environment (`Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Rivest.bp_sat`) with the bridges
`memFixedLang_subset`/`memWriterLang_subset`; the lower bound is a traced session against the
counting host (`bp_traces`).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.Rivest

open Silmaril.Wasm Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Accept.Handle Silmaril.Formats
  Silmaril.Formats.Api Silmaril.Wasm.Game.HandleAccept.MemSound.Pair

/-- **In a fixed environment, `bpairMod` accepts only `bpairTree`.** -/
theorem bpairMod_fixed_sound (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp) :
    fixedLang (sexpW MemAtom) pol {ρ} (memTraces P (ReplyEnvs pairReply) 0 bpairMod {}) ⊆
      {bpairTree} :=
  memFixedLang_subset
    (by rw [hs]; exact Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Rivest.bp_sat P ρ)
    (fun _ _ h => h)

/-- **`bpairMod` accepts only `bpairTree`.** -/
theorem bpairMod_sound (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    memWriterLang P (ReplyEnvs pairReply) 0 bpairMod {} pol ⊆ {bpairTree} :=
  memWriterLang_subset
    (fun ρ => by rw [hs]; exact Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Rivest.bp_sat P ρ)
    (fun _ _ h => h) hw ha

/-- **`bpairMod` accepts `bpairTree`**, for every policy. -/
theorem bpairMod_live (P : Profile) (pol : Policy (BitVec 32)) :
    bpairTree ∈ memWriterLang P (ReplyEnvs pairReply) 0 bpairMod {} pol :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Rivest.bpairMod_live P pol

/-- **The writer language of `bpairMod` is `{bpairTree}`.** -/
theorem bpairMod_lang (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    memWriterLang P (ReplyEnvs pairReply) 0 bpairMod {} pol = {bpairTree} :=
  Set.Subset.antisymm (bpairMod_sound P hs hw ha) (Set.singleton_subset_iff.2 (bpairMod_live P pol))

theorem bytesPair_map : bytesPair.map bytesMem' = bpairTree :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Rivest.bytesPair_map

theorem rivestPair_map : rivestPair.map rivestMem = bpairTree :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Rivest.rivestPair_map

/-- **Byte trees**: the writer language of `bpairMod` is the list `(61 62)` of `ByteSExp`. -/
theorem bytes_bpairMod (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    memWriterLang P (ReplyEnvs pairReply) 0 bpairMod {} pol = {bytesPair.map bytesMem'} := by
  rw [bytesPair_map]; exact bpairMod_lang P hs hw ha

/-- **Rivest canonical trees**: the writer language of `bpairMod` is the list `(61 62)` of
`RivestSExp`. -/
theorem rivest_bpairMod (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    memWriterLang P (ReplyEnvs pairReply) 0 bpairMod {} pol = {rivestPair.map rivestMem} := by
  rw [rivestPair_map]; exact bpairMod_lang P hs hw ha

/-- The dotted form of `rivestPair` reads back to it. -/
theorem rivestPair_dotted : SExp2.toSExp? rivestPair.toSExp2 = some rivestPair :=
  SExp2.toSExp?_toSExp2 _

end Silmaril.Wasm.Game.HandleAccept.MemSound.Rivest
