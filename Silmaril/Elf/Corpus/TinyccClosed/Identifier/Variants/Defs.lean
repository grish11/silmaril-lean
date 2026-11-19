module
public import Silmaril.Elf.Corpus.TinyccClosed.Identifier.Thms
public import Silmaril.Elf.Staged.CorpusVariants.Tinycc.N0927.Default.X8664.Og.Unstripped.Tcc.Thms

@[expose] public section
namespace Silmaril.Elf.Corpus.TinyccClosed.Identifier.Variants
open Silmaril.Project.Shapes
open Silmaril.X86.SystemV.CApi

def codeOg : List (BitVec 8) := [0x83, 0xff, 0x5f, 0x74, 0x1e, 0x7e, 0xe, 0x83, 0xef, 0x61, 0x83, 0xff, 0x19, 0x76, 0x20, 0xb8, 0x0, 0x0, 0x0, 0x0, 0xc3, 0x83, 0xef, 0x41, 0x83, 0xff, 0x19, 0x76, 0xc, 0xb8, 0x0, 0x0, 0x0, 0x0, 0xc3, 0xb8, 0x1, 0x0, 0x0, 0x0, 0xc3, 0xb8, 0x1, 0x0, 0x0, 0x0, 0xc3, 0xb8, 0x1, 0x0, 0x0, 0x0, 0xc3]
def placementOg : Silmaril.Project.Shapes.Placement := ⟨0x5e05, codeOg, 0⟩

/-- Deterministic ASCII identifier-character boundary, defined for every signed
int32 input, including negative values. No arbitrary source/Core meaning is
assumed as a premise. This mathematical contract is itself unproved for both
actual binaries. -/
def result (args : Arguments [.int32]) : BitVec 32 :=
  match args with
  | .cons c .nil =>
      let n := Scalar.signed .int32 c
      if (97 ≤ n ∧ n ≤ 122) ∨ (65 ≤ n ∧ n ≤ 90) ∨ n = 95 then 1 else 0

def meaning : SysV.Meaning Silmaril.Elf.Corpus.TinyccClosed.Identifier.signature where
  Safe _ := True
  Returns args value := value = result args

/-- Both selected actual optimization variants must implement the same total,
deterministic boundary meaning. Each is enterable for all arguments, terminates
to first return, preserves callee-saved registers and memory outside sixteen
stack bytes; no global/heap/callee/environment effects are permitted. -/
@[problem "silmaril.corpus.tinycc.isid.o0_og_equivalence"
  (title := "Actual TinyCC O0 and Og identifier predicates share an explicit signed-int context")]
def Task.equivalent : Prop :=
  SysV.Implements Silmaril.X86.Open.isa
    Silmaril.Elf.Corpus.TinyccClosed.Identifier.placement
    Silmaril.Elf.Corpus.TinyccClosed.Identifier.signature 16 meaning ∧
  SysV.Implements Silmaril.X86.Open.isa placementOg
    Silmaril.Elf.Corpus.TinyccClosed.Identifier.signature 16 meaning

end Silmaril.Elf.Corpus.TinyccClosed.Identifier.Variants
