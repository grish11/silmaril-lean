module

public import Silmaril.Elf.Corpus.MimallocVersion.Thms
public import Silmaril.Elf.Staged.CorpusVariants.Mimalloc.N219.Default.X8664.O0.Stripped.LibmimallocSo21.Thms
public import Silmaril.Elf.Staged.CorpusVariants.Mimalloc.N219.Default.X8664.O0.Unstripped.LibmimallocSo21.Thms
public import Silmaril.Elf.Staged.CorpusVariants.Mimalloc.N219.Default.X8664.O1.Stripped.LibmimallocSo21.Thms
public import Silmaril.Elf.Staged.CorpusVariants.Mimalloc.N219.Default.X8664.O1.Unstripped.LibmimallocSo21.Thms
public import Silmaril.Elf.Staged.CorpusVariants.Mimalloc.N219.Default.X8664.O3.Stripped.LibmimallocSo21.Thms
public import Silmaril.Elf.Staged.CorpusVariants.Mimalloc.N219.Default.X8664.O3.Unstripped.LibmimallocSo21.Thms
public import Silmaril.Elf.Staged.CorpusVariants.Mimalloc.N219.Default.X8664.Og.Stripped.LibmimallocSo21.Thms
public import Silmaril.Elf.Staged.CorpusVariants.Mimalloc.N219.Default.X8664.Og.Unstripped.LibmimallocSo21.Thms

@[expose] public section
namespace Silmaril.Elf.Corpus.MimallocVersion.AllVariants
open Silmaril.Elf.Corpus.MimallocVersion

def codeO0Stripped : List (BitVec 8) := [0x55, 0x48, 0x89, 0xe5, 0xb8, 0xdb, 0x0, 0x0, 0x0, 0x5d, 0xc3]
def placementO0Stripped : Silmaril.Project.Shapes.Placement := ⟨0x11e2f, codeO0Stripped, 0⟩

def codeO0Unstripped : List (BitVec 8) := [0x55, 0x48, 0x89, 0xe5, 0xb8, 0xdb, 0x0, 0x0, 0x0, 0x5d, 0xc3]
def placementO0Unstripped : Silmaril.Project.Shapes.Placement := ⟨0x11e2f, codeO0Unstripped, 0⟩

def codeO1Stripped : List (BitVec 8) := [0xb8, 0xdb, 0x0, 0x0, 0x0, 0xc3]
def placementO1Stripped : Silmaril.Project.Shapes.Placement := ⟨0xd5b6, codeO1Stripped, 0⟩

def codeO1Unstripped : List (BitVec 8) := [0xb8, 0xdb, 0x0, 0x0, 0x0, 0xc3]
def placementO1Unstripped : Silmaril.Project.Shapes.Placement := ⟨0xd5b6, codeO1Unstripped, 0⟩

def codeO3Stripped : List (BitVec 8) := [0xb8, 0xdb, 0x0, 0x0, 0x0, 0xc3]
def placementO3Stripped : Silmaril.Project.Shapes.Placement := ⟨0xfaf0, codeO3Stripped, 0⟩

def codeO3Unstripped : List (BitVec 8) := [0xb8, 0xdb, 0x0, 0x0, 0x0, 0xc3]
def placementO3Unstripped : Silmaril.Project.Shapes.Placement := ⟨0xfaf0, codeO3Unstripped, 0⟩

def codeOgStripped : List (BitVec 8) := [0xb8, 0xdb, 0x0, 0x0, 0x0, 0xc3]
def placementOgStripped : Silmaril.Project.Shapes.Placement := ⟨0xd08b, codeOgStripped, 0⟩

def codeOgUnstripped : List (BitVec 8) := [0xb8, 0xdb, 0x0, 0x0, 0x0, 0xc3]
def placementOgUnstripped : Silmaril.Project.Shapes.Placement := ⟨0xd08b, codeOgUnstripped, 0⟩

/-- Actual stripped/unstripped functions must implement the same deterministic boundary meaning.
The common context permits eight stack bytes below entry, preserves callee-saved registers,
requires valid loaded entry/return and first-return termination, and forbids other memory effects.
Paired provenance chooses the address; each actual ELF's bytes are independently kernel bound.
This is stated-unproved. Stripping and symbol identity are not semantic correctness proofs. -/
@[problem "silmaril.corpus.mimalloc.mi_version.o0_strip_equivalence"
  (title := "Delivered O0 mi_version stripping pair shares a deterministic System V meaning")]
def Task.O0_strip_equivalent : Prop :=
  Silmaril.Project.Shapes.SysV.Implements Silmaril.X86.Open.isa placementO0Unstripped signature 8 versionMeaning ∧
  Silmaril.Project.Shapes.SysV.Implements Silmaril.X86.Open.isa placementO0Stripped signature 8 versionMeaning

/-- Actual stripped/unstripped functions must implement the same deterministic boundary meaning.
The common context permits eight stack bytes below entry, preserves callee-saved registers,
requires valid loaded entry/return and first-return termination, and forbids other memory effects.
Paired provenance chooses the address; each actual ELF's bytes are independently kernel bound.
This is stated-unproved. Stripping and symbol identity are not semantic correctness proofs. -/
@[problem "silmaril.corpus.mimalloc.mi_version.og_strip_equivalence"
  (title := "Delivered Og mi_version stripping pair shares a deterministic System V meaning")]
def Task.Og_strip_equivalent : Prop :=
  Silmaril.Project.Shapes.SysV.Implements Silmaril.X86.Open.isa placementOgUnstripped signature 8 versionMeaning ∧
  Silmaril.Project.Shapes.SysV.Implements Silmaril.X86.Open.isa placementOgStripped signature 8 versionMeaning

/-- Actual stripped/unstripped functions must implement the same deterministic boundary meaning.
The common context permits eight stack bytes below entry, preserves callee-saved registers,
requires valid loaded entry/return and first-return termination, and forbids other memory effects.
Paired provenance chooses the address; each actual ELF's bytes are independently kernel bound.
This is stated-unproved. Stripping and symbol identity are not semantic correctness proofs. -/
@[problem "silmaril.corpus.mimalloc.mi_version.o1_strip_equivalence"
  (title := "Delivered O1 mi_version stripping pair shares a deterministic System V meaning")]
def Task.O1_strip_equivalent : Prop :=
  Silmaril.Project.Shapes.SysV.Implements Silmaril.X86.Open.isa placementO1Unstripped signature 8 versionMeaning ∧
  Silmaril.Project.Shapes.SysV.Implements Silmaril.X86.Open.isa placementO1Stripped signature 8 versionMeaning

/-- Actual stripped/unstripped functions must implement the same deterministic boundary meaning.
The common context permits eight stack bytes below entry, preserves callee-saved registers,
requires valid loaded entry/return and first-return termination, and forbids other memory effects.
Paired provenance chooses the address; each actual ELF's bytes are independently kernel bound.
This is stated-unproved. Stripping and symbol identity are not semantic correctness proofs. -/
@[problem "silmaril.corpus.mimalloc.mi_version.o3_strip_equivalence"
  (title := "Delivered O3 mi_version stripping pair shares a deterministic System V meaning")]
def Task.O3_strip_equivalent : Prop :=
  Silmaril.Project.Shapes.SysV.Implements Silmaril.X86.Open.isa placementO3Unstripped signature 8 versionMeaning ∧
  Silmaril.Project.Shapes.SysV.Implements Silmaril.X86.Open.isa placementO3Stripped signature 8 versionMeaning

end Silmaril.Elf.Corpus.MimallocVersion.AllVariants
