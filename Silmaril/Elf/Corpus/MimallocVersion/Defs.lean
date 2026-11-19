module

public import Silmaril.Project.Shapes.SysV.Defs
public import Silmaril.X86.Open.Thms
public import Silmaril.Elf.Staged.CorpusVariants.Mimalloc.N219.Default.X8664.O0.Unstripped.LibmimallocSo21.Thms
public import Silmaril.Elf.Staged.CorpusVariants.Mimalloc.N219.Default.X8664.O3.Unstripped.LibmimallocSo21.Thms

/-!
# A concrete mimalloc function-equivalence problem

Two actual ELF functions, compiled at O0 and O3, must implement the same deterministic
System V boundary meaning. This is a problem statement, not a proof. Each code list is
bound to its ELF virtual address by a separate kernel-checked `CodeAt` theorem.

The shared observation is signed int32 result 219, termination to the first return,
callee-saved registers, and no writes outside eight bytes below the entry stack pointer.
There are no arguments, globals, heap effects, calls or environment services. Both sides
must be enterable; the common meaning is safe for the sole argument tuple. No source
safety, source-to-Core binding or semantic equivalence is assumed as a premise.
-/

@[expose] public section

namespace Silmaril.Elf.Corpus.MimallocVersion

noncomputable abbrev O0 := Silmaril.Elf.Staged.CorpusVariants.Mimalloc.N219.Default.X8664.O0.Unstripped.LibmimallocSo21.F
noncomputable abbrev O3 := Silmaril.Elf.Staged.CorpusVariants.Mimalloc.N219.Default.X8664.O3.Unstripped.LibmimallocSo21.F

def signature : Silmaril.X86.SystemV.CApi.Signature := ⟨[], some .int32⟩

def codeO0 : List (BitVec 8) := [0x55, 0x48, 0x89, 0xe5, 0xb8, 0xdb, 0, 0, 0, 0x5d, 0xc3]
def codeO3 : List (BitVec 8) := [0xb8, 0xdb, 0, 0, 0, 0xc3]

def placementO0 : Silmaril.Project.Shapes.Placement := ⟨0x11e2f, codeO0, 0⟩
def placementO3 : Silmaril.Project.Shapes.Placement := ⟨0xfaf0, codeO3, 0⟩

/-- A deterministic shared boundary meaning, not arbitrary unrelated source Core. -/
def versionMeaning : Silmaril.Project.Shapes.SysV.Meaning signature where
  Safe _ := True
  Returns _ r := r = (219 : BitVec 32)

/-- Both delivered variants return the same value in every allowed ABI context.
The `Implements` obligations also require entry nonvacuity, first-return total correctness
and preservation outside the permitted stack footprint. Neither obligation is proved here. -/
@[problem "silmaril.corpus.mimalloc.mi_version.variants"
  (title := "Delivered mimalloc O0 and O3 functions share a deterministic System V result")]
def Task.mi_version_equivalent : Prop :=
  Silmaril.Project.Shapes.SysV.Implements Silmaril.X86.Open.isa placementO0 signature 8 versionMeaning ∧
  Silmaril.Project.Shapes.SysV.Implements Silmaril.X86.Open.isa placementO3 signature 8 versionMeaning

end Silmaril.Elf.Corpus.MimallocVersion
