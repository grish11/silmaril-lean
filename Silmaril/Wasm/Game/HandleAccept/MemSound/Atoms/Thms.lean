module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Atoms.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.AtomsLive

/-!
# Atom kinds through linear memory: soundness and non-vacuity

For every profile, `atomMod name` (the module of `hiMod` with the atom import `sexp.<name>`,
writing the bytes `68 69` and accepting the handle of `<name>(0, 2)`):

* `str_sound`, `str_live`, `str_lang`: through `string(ptr, len)` (`memRoles`), the writer
  language is `{"hi"}` (a string atom) for policies without undefined behaviour, and contains it
  for every policy;
* `blob_sound`, `blob_live`, `blob_lang`: through `blob(ptr, len)`, the byte string `68 69`;
* `kw_sound`, `kw_live`, `kw_lang`: through the new `keyword(ptr, len)` import (`kwRoles`, atoms
  `KwAtom`), the keyword `hi`.

Upper bounds are Hoare-logic proofs of the module under the closed-writes contract
(`Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Atoms.atom_sat`, proved once for every
decoder) and the closed-writes bridge for any roles (`rolesLang_subset_of_closed`); non-vacuity
is the traced session against the counting host (`atom_traces`), as for `hiMod`.
`atomMod_symbol`: `atomMod "symbol"` is `hiMod`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.Atoms

open Silmaril.Wasm Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Accept.Handle Silmaril.Formats
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi

theorem atomMod_symbol : atomMod "symbol" = hiMod := rfl

/-- `atomMod "string"` accepts only the string `"hi"`. -/
theorem str_sound (P : Profile) {pol : Policy (BitVec 32)} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) :
    memWriterLang P (ReplyEnvs hiReply) 0 (atomMod "string") {} pol ⊆ {.atom strAtom} :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Atoms.str_sound P ha hw

/-- `atomMod "string"` accepts the string `"hi"`. -/
theorem str_live (P : Profile) (pol : Policy (BitVec 32)) :
    .atom strAtom ∈ memWriterLang P (ReplyEnvs hiReply) 0 (atomMod "string") {} pol :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Atoms.str_live P pol

/-- **The writer language of `atomMod "string"` is `{"hi"}`.** -/
theorem str_lang (P : Profile) {pol : Policy (BitVec 32)} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) :
    memWriterLang P (ReplyEnvs hiReply) 0 (atomMod "string") {} pol = {.atom strAtom} :=
  Set.Subset.antisymm (str_sound P ha hw) (Set.singleton_subset_iff.2 (str_live P pol))

/-- `atomMod "blob"` accepts only the byte string `68 69`. -/
theorem blob_sound (P : Profile) {pol : Policy (BitVec 32)} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) :
    memWriterLang P (ReplyEnvs hiReply) 0 (atomMod "blob") {} pol ⊆ {.atom blobAtom} :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Atoms.blob_sound P ha hw

/-- `atomMod "blob"` accepts the byte string `68 69`. -/
theorem blob_live (P : Profile) (pol : Policy (BitVec 32)) :
    .atom blobAtom ∈ memWriterLang P (ReplyEnvs hiReply) 0 (atomMod "blob") {} pol :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Atoms.blob_live P pol

/-- **The writer language of `atomMod "blob"` is `{68 69}`.** -/
theorem blob_lang (P : Profile) {pol : Policy (BitVec 32)} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) :
    memWriterLang P (ReplyEnvs hiReply) 0 (atomMod "blob") {} pol = {.atom blobAtom} :=
  Set.Subset.antisymm (blob_sound P ha hw) (Set.singleton_subset_iff.2 (blob_live P pol))

/-- `atomMod "keyword"` accepts only the keyword `hi`. -/
theorem kw_sound (P : Profile) {pol : Policy (BitVec 32)} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) :
    kwWriterLang P (ReplyEnvs hiReply) 0 (atomMod "keyword") {} pol ⊆ {.atom kwAtom} :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Atoms.kw_sound P ha hw

/-- `atomMod "keyword"` accepts the keyword `hi`. -/
theorem kw_live (P : Profile) (pol : Policy (BitVec 32)) :
    .atom kwAtom ∈ kwWriterLang P (ReplyEnvs hiReply) 0 (atomMod "keyword") {} pol :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Atoms.kw_live P pol

/-- **The writer language of `atomMod "keyword"` is `{:hi}`.** -/
theorem kw_lang (P : Profile) {pol : Policy (BitVec 32)} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) :
    kwWriterLang P (ReplyEnvs hiReply) 0 (atomMod "keyword") {} pol = {.atom kwAtom} :=
  Set.Subset.antisymm (kw_sound P ha hw) (Set.singleton_subset_iff.2 (kw_live P pol))

end Silmaril.Wasm.Game.HandleAccept.MemSound.Atoms
