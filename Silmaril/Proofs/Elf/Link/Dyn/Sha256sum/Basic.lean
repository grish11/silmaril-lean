module

public import Silmaril.Elf.Link.Dyn.Sha256sum.Defs
public import Silmaril.Elf.Link.Dyn.Sha256sum.Scope.Defs
public import Silmaril.Elf.Link.Dyn.Hello.Cert

@[expose] public section

/-! Proofs for `Silmaril.Elf.Link.Dyn.Sha256sum` (the header `Silmaril.Elf.Link.Dyn.Sha256sum.Thms` restates them). -/

namespace Silmaril.Proofs.Elf.Link.Dyn.Sha256sum

open Silmaril.Elf.Link.Dyn Silmaril.Elf.Link.Dyn.Sha256sum
open Silmaril.Elf.Link.DynElf
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

theorem sha_slots_K :
    slotsWith (resolveK [exeFacts shaRefs, cryptoFacts, libcFacts, ldFacts]) false shaFile shaInfo =
      some shaSlots := by
  decide +kernel

theorem known_ok {f : Blob} {cs : List Chunk} {i : DynInfo} {T : List (Ref × Bool × Option Def)}
    (hi : dynInfo.run (sparseRead cs) = some i) (hT : factsHold cs i T = true) (hf : ChunksOf f cs) :
    Known.Ok ⟨f, i, T⟩ :=
  ⟨run_sparse hf hi, fun e he => facts_of hT hf e he⟩

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

end Silmaril.Proofs.Elf.Link.Dyn.Sha256sum
