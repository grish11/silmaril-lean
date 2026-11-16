module

public import Silmaril.Elf.Link.Dyn.Sha256sum.Defs
public import Silmaril.Elf.Link.Dyn.Sha256sum.Scope.Defs
public import Silmaril.Elf.Link.Dyn.Hello.Cert

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

theorem crypto_info_sparse : dynInfo.run (sparseRead cryptoChunks) = some cryptoInfo := by decide +kernel
theorem libc_info_sparse : dynInfo.run (sparseRead libcChunks) = some libcInfo := by decide +kernel
theorem ld_info_sparse : dynInfo.run (sparseRead ldChunks) = some ldInfo := by decide +kernel
theorem crypto_facts_sparse : factsHold cryptoChunks cryptoInfo cryptoFacts = true := by decide +kernel
theorem libc_facts_sparse : factsHold libcChunks libcInfo libcFacts = true := by decide +kernel
theorem ld_facts_sparse : factsHold ldChunks ldInfo ldFacts = true := by decide +kernel

theorem sha_info : dynInfo.run (blobRead shaFile) = some shaInfo := by decide +kernel
theorem sha_bindNow : shaInfo.bindNow = true := by decide +kernel
theorem sha_refs_hold : refsHold shaFile shaInfo shaRefs = true := by decide +kernel

/-- The eager slot table of `sha256sum` (objects: 0 the executable, 1 `libcrypto`, 2 `libc`,
3 `ld.so`). -/
def shaSlots : List (Nat × Val) :=
  [(0x9a10, .addr 0 15136),
   (0x9a18, .addr 0 15072),
   (0x9a20, .addr 0 29245),
   (0x9a40, .addr 0 29251),
   (0x9a60, .addr 0 29266),
   (0x9a80, .addr 0 29272),
   (0x9aa0, .addr 0 29279),
   (0x9ac0, .addr 0 29284),
   (0x9ae0, .addr 0 29291),
   (0x9b00, .addr 0 29295),
   (0x9b20, .addr 0 29300),
   (0x9b40, .addr 0 29307),
   (0x9b60, .addr 0 29312),
   (0x9b80, .addr 0 29317),
   (0xa008, .addr 0 40968),
   (0xa028, .addr 0 41056),
   (0xa030, .addr 0 40992),
   (0x9f98, .addr 2 0x2056a8),
   (0x9fa0, .addr 2 0x205378),
   (0x9fa8, .addr 2 0x472c0),
   (0x9fb0, .addr 2 0x2a200),
   (0x9fb8, .addr 2 0x2056b0),
   (0x9fc0, .addr 2 0x2056a0),
   (0x9fc8, .addr 2 0x204248),
   (0x9fd0, .addr 2 0x205370),
   (0x9fd8, .abs 0),
   (0x9fe0, .abs 0),
   (0x9fe8, .abs 0),
   (0x9dd8, .addr 2 0x137bf0),
   (0x9de0, .addr 2 0x88630),
   (0x9de8, .addr 2 0x2a6e0),
   (0x9df0, .ifunc 2 0xb4410),
   (0x9df8, .addr 2 0x39480),
   (0x9e00, .addr 2 0x3ba00),
   (0x9e08, .addr 2 0x91720),
   (0x9e10, .ifunc 2 0xb4dc0),
   (0x9e18, .ifunc 2 0xb1730),
   (0x9e20, .ifunc 2 0xb4ff0),
   (0x9e28, .addr 2 0x28820),
   (0x9e30, .addr 2 0x1172a0),
   (0x9e38, .addr 2 0x901c0),
   (0x9e40, .addr 2 0xc9a50),
   (0x9e48, .addr 1 0x33d3c0),
   (0x9e50, .addr 2 0x3bf80),
   (0x9e58, .addr 2 0x11b7f0),
   (0x9e60, .addr 2 0x90790),
   (0x9e68, .addr 2 0xc9cd0),
   (0x9e70, .addr 2 0x471f0),
   (0x9e78, .addr 2 0x3a6b0),
   (0x9e80, .addr 2 0x3a340),
   (0x9e88, .addr 2 0x85370),
   (0x9e90, .addr 2 0x3bf00),
   (0x9e98, .addr 2 0x8ea80),
   (0x9ea0, .addr 2 0x855d0),
   (0x9ea8, .addr 2 0x3b9c0),
   (0x9eb0, .ifunc 2 0xb5210),
   (0x9eb8, .addr 2 0x138120),
   (0x9ec0, .addr 2 0x3d820),
   (0x9ec8, .addr 2 0x858d0),
   (0x9ed0, .addr 2 0x85f40),
   (0x9ed8, .addr 2 0xade30),
   (0x9ee0, .addr 2 0x47ba0),
   (0x9ee8, .addr 2 0xad750),
   (0x9ef0, .addr 2 0x12e670),
   (0x9ef8, .addr 2 0x95120),
   (0x9f00, .addr 2 0x90880),
   (0x9f08, .ifunc 2 0x1379b0),
   (0x9f10, .ifunc 2 0xb32a0),
   (0x9f18, .addr 2 0x406f0),
   (0x9f20, .addr 2 0xee300),
   (0x9f28, .addr 2 0xae1a0),
   (0x9f30, .addr 2 0x136eb0),
   (0x9f38, .addr 2 0xf5ad0),
   (0x9f40, .addr 2 0x11e6c0),
   (0x9f48, .addr 2 0x91430),
   (0x9f50, .addr 1 0x33d410),
   (0x9f58, .addr 2 0x11b2a0),
   (0x9f60, .addr 2 0x137130),
   (0x9f68, .addr 2 0x91400),
   (0x9f70, .addr 2 0x91890),
   (0x9f78, .addr 2 0x86a20),
   (0x9f80, .addr 2 0x1169b0),
   (0x9f88, .addr 2 0x86c20),
   (0x9f90, .addr 1 0x33d630)]

theorem sha_slots_K :
    slotsWith (resolveK [exeFacts shaRefs, cryptoFacts, libcFacts, ldFacts]) false shaFile shaInfo =
      some shaSlots := by
  decide +kernel

theorem known_ok {f : Blob} {cs : List Chunk} {i : DynInfo} {T : List (Ref × Bool × Option Def)}
    (hi : dynInfo.run (sparseRead cs) = some i) (hT : factsHold cs i T = true) (hf : ChunksOf f cs) :
    Known.Ok ⟨f, i, T⟩ :=
  ⟨run_sparse hf hi, fun e he => facts_of hT hf e he⟩

/-- **The binding certificate of `sha256sum`**: the loader's eager slot table, for every scope
whose libraries agree with the chunks. -/
theorem sha_slots {Fk Fc Fl : Blob} (hk : ChunksOf Fk cryptoChunks) (hc : ChunksOf Fc libcChunks)
    (hl : ChunksOf Fl ldChunks) :
    slots [shaFile, Fk, Fc, Fl] false shaFile shaInfo = some shaSlots := by
  have := slots_of_known (ks := [⟨shaFile, shaInfo, exeFacts shaRefs⟩, ⟨Fk, cryptoInfo, cryptoFacts⟩,
      ⟨Fc, libcInfo, libcFacts⟩, ⟨Fl, ldInfo, ldFacts⟩])
    (by
      intro k hk'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk'
      rcases hk' with rfl | rfl | rfl | rfl
      · exact exeKnown_ok sha_info sha_refs_hold
      · exact known_ok crypto_info_sparse crypto_facts_sparse hk
      · exact known_ok libc_info_sparse libc_facts_sparse hc
      · exact known_ok ld_info_sparse ld_facts_sparse hl) sha_slots_K
  simpa using this

end Silmaril.Elf.Link.Dyn.Sha256sum
