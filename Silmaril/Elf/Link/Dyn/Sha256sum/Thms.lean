module

public import Silmaril.Elf.Link.Dyn.Sha256sum.Defs
public import Silmaril.Elf.Link.Dyn.Sha256sum.Scope.Defs
public import Silmaril.Elf.Link.Dyn.Hello.Cert
import Silmaril.Proofs.Elf.Link.Dyn.Sha256sum.Basic

/-! # GNU `sha256sum`: the binding certificate

PROVED (standard axioms), for every `libcrypto.so.3`, `libc.so.6` and `ld.so` agreeing with the
chunks of `Sha256sum.Scope` (search scope `[sha256sum, libcrypto.so.3, libc.so.6,
ld-linux-x86-64.so.2]`, the breadth-first `DT_NEEDED` closure):

* `scope_facts`: the 134 lookups the 84 relocations need (67 in `libcrypto`, 64 in `libc`, 3 in
  `ld.so`), each kernel-checked on the sparse chunks;
* `sha_slots`: **the eager slot table** (`DF_BIND_NOW`) of all 84 relocations: 17 `RELATIVE`,
  `SHA256_Init/Update/Final` in `libcrypto`, the rest in `libc` (7 of them ifuncs: their value is
  the resolver's choice `ifn`), and the 3 weak undefined ones 0.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.Elf.Link.DynElf.Elf
open Silmaril.Elf.Link.Dyn.Glibc (factsHold facts_of)
open Silmaril.Elf.Link.Dyn.Hello (refsHold refsHold_sound exeFacts exeKnown_ok)
open Silmaril.X86.Link (Blob)

theorem crypto_info_sparse : dynInfo.run (sparseRead cryptoChunks) = some cryptoInfo :=
  Silmaril.Proofs.Elf.Link.Dyn.Sha256sum.crypto_info_sparse
theorem libc_info_sparse : dynInfo.run (sparseRead libcChunks) = some libcInfo :=
  Silmaril.Proofs.Elf.Link.Dyn.Sha256sum.libc_info_sparse
theorem ld_info_sparse : dynInfo.run (sparseRead ldChunks) = some ldInfo :=
  Silmaril.Proofs.Elf.Link.Dyn.Sha256sum.ld_info_sparse
theorem crypto_facts_sparse : factsHold cryptoChunks cryptoInfo cryptoFacts = true :=
  Silmaril.Proofs.Elf.Link.Dyn.Sha256sum.crypto_facts_sparse
theorem libc_facts_sparse : factsHold libcChunks libcInfo libcFacts = true :=
  Silmaril.Proofs.Elf.Link.Dyn.Sha256sum.libc_facts_sparse
theorem ld_facts_sparse : factsHold ldChunks ldInfo ldFacts = true :=
  Silmaril.Proofs.Elf.Link.Dyn.Sha256sum.ld_facts_sparse

theorem sha_info : dynInfo.run (blobRead shaFile) = some shaInfo :=
  Silmaril.Proofs.Elf.Link.Dyn.Sha256sum.sha_info
theorem sha_bindNow : shaInfo.bindNow = true :=
  Silmaril.Proofs.Elf.Link.Dyn.Sha256sum.sha_bindNow
theorem sha_refs_hold : refsHold shaFile shaInfo shaRefs = true :=
  Silmaril.Proofs.Elf.Link.Dyn.Sha256sum.sha_refs_hold

theorem sha_slots_K :
    slotsWith (resolveK [exeFacts shaRefs, cryptoFacts, libcFacts, ldFacts]) false shaFile shaInfo =
      some shaSlots :=
  Silmaril.Proofs.Elf.Link.Dyn.Sha256sum.sha_slots_K

theorem known_ok {f : Blob} {cs : List Chunk} {i : DynInfo} {T : List (Ref × Bool × Option Def)}
    (hi : dynInfo.run (sparseRead cs) = some i) (hT : factsHold cs i T = true) (hf : ChunksOf f cs) :
    Known.Ok ⟨f, i, T⟩ :=
  Silmaril.Proofs.Elf.Link.Dyn.Sha256sum.known_ok hi hT hf

/-- **The binding certificate of `sha256sum`**: the loader's eager slot table, for every scope
whose libraries agree with the chunks. -/
theorem sha_slots {Fk Fc Fl : Blob} (hk : ChunksOf Fk cryptoChunks) (hc : ChunksOf Fc libcChunks)
    (hl : ChunksOf Fl ldChunks) :
    slots [shaFile, Fk, Fc, Fl] false shaFile shaInfo = some shaSlots :=
  Silmaril.Proofs.Elf.Link.Dyn.Sha256sum.sha_slots hk hc hl

end Silmaril.Elf.Link.Dyn.Sha256sum
