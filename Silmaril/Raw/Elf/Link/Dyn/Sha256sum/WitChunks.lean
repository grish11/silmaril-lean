module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.StdinRun
public import Silmaril.Raw.Elf.Link.Dyn.Proc.Witness

/-! # GNU `sha256sum` witness: library files, bases, slot table (non-vacuity, part 0) -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum.Wit

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access Region Permissions)
open Silmaril.X86.Link (Blob)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Proc.Witness

def Fk0 : Blob := blobOf cryptoChunks
def Fc0 : Blob := blobOf libcChunks
def Fl0 : Blob := blobOf ldChunks

theorem hFk : ChunksOf Fk0 cryptoChunks := by unfold ChunksOf; decide +kernel
theorem hFc : ChunksOf Fc0 libcChunks := by unfold ChunksOf; decide +kernel
theorem hFl : ChunksOf Fl0 ldChunks := by unfold ChunksOf; decide +kernel

def b0 : Word := 0x555555554000#64
def kb0 : Word := 0x7ffff7400000#64
def lb0 : Word := 0x7ffff7c00000#64
def ldb0 : Word := 0x7ffff7fc5000#64
def sp0 : Word := 0x7ffffffde000#64
def fs0 : Word := 0x7ffff7fb0000#64
def ifn0 : Word → Option Word := fun x => some x
def res0 : Word := 0#64

theorem b0_toNat : b0.toNat = 0x555555554000 := rfl
theorem kb0_toNat : kb0.toNat = 0x7ffff7400000 := rfl
theorem lb0_toNat : lb0.toNat = 0x7ffff7c00000 := rfl
theorem sp0_toNat : sp0.toNat = 0x7ffffffde000 := rfl
theorem fs0_toNat : fs0.toNat = 0x7ffff7fb0000 := rfl

/-- The slot table at these bases. -/
def T0 : List (Nat × Option Word) :=
  (shaSlots.mapM fun (e : Nat × Val) => (e.2.word [b0, kb0, lb0, ldb0] ifn0 res0).map fun w => (e.1, w)).getD []

theorem hT0 : shaSlots.mapM (fun (e : Nat × Val) => (e.2.word [b0, kb0, lb0, ldb0] ifn0 res0).map fun w => (e.1, w)) =
    some T0 := by decide +kernel

end Silmaril.Elf.Link.Dyn.Sha256sum.Wit
