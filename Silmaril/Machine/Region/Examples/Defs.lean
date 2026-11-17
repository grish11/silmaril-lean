module

public import Silmaril.Machine.Region.X86.Thms
public import Silmaril.Machine.Region.Thms

@[expose] public section
namespace Silmaril.Machine.Region.Examples
open Silmaril.Semantics.Region
open Silmaril.X86.Decompile

/-- `EB 00`: one real direct branch, to the first address outside [0,2). -/
def jump : Silmaril.X86.Decompile.Region := ⟨0, [0xeb, 0x00]⟩
def jumpInstruction : Decoded := ⟨0, .jmp8 0, 2⟩
def jumpSupport (l : Nat) : Prop := l = 0
def jumpAdmit (s : Silmaril.X86.MState) : Prop := s.core.rip.toNat = 0 ∧ jump.LoadedIn s.memory

def initial : Silmaril.X86.MState where
  core := ⟨fun _ => 0, 0, ⟨none, none, none, none, none, none⟩, 0⟩
  memory := jump.load

/-- Tiny classification corpus, deliberately not the canonical ELF corpus.
Each pair names the bytes and whether its normal targets should be finite.
Unknown opcode/truncated instruction are tested separately as decode failures. -/
def fixtureCorpus : List (List Silmaril.X86.Byte × Bool) :=
  [([0xeb, 0], true), ([0xeb, 0xfe], true), ([0x74, 0], true),
   ([0x90], true), ([0x0f, 0x0b], true), ([0xe8, 0, 0, 0, 0], false), ([0xc3], false)]

def finiteTargets : Targets Nat → Bool
  | .finite _ => true
  | .top => false

/-- The denominator counts fixture byte strings, including call and return.
A finite result here is an analysis classification, not a certified region. -/
def classificationReport : Nat × Nat × Nat :=
  let results := fixtureCorpus.map fun (bytes, expected) =>
    match (Silmaril.X86.Decompile.Region.mk 0 bytes).decode? 10 with
    | some [d] => (finiteTargets (X86.instructionTargets d) == expected,
        finiteTargets (X86.instructionTargets d))
    | _ => (false, false)
  (results.length, (results.filter fun p => p.1).length,
    (results.filter fun p => p.2).length)

/-- Ambiguous translation is an error, even for duplicate owners. -/
def mapping : Mapping := ⟨⟨.virtual, ⟨0x1000, 0x1002, by decide⟩⟩, 0x40⟩
end Silmaril.Machine.Region.Examples
