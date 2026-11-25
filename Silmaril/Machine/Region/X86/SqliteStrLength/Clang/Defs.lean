module

public import Silmaril.Machine.Region.X86.SqliteStrLength.Defs

/-! # Clang's forward CFG for SQLite 3.54.1 `sqlite3_str_length`

The two return labels distinguish the two actual RET instructions. The
observational view maps both to the GCC graph's common return label.
-/

@[expose] public section
namespace Silmaril.Machine.Region.X86.SqliteStrLength.Clang

open Silmaril.X86
open Silmaril.SSA.LambdaRTL
open Silmaril.Machine.Execution (run)

/-- Clang 19 x86-64 `-O2` symbol at VA/file offset `0x12e70`.
ELF SHA-256: `449086f493bd3058fdcefbf4319f00e386b73b269e00e72c3ec4d8a1a3b82ff1`. -/
def code : List Byte :=
  [0x48, 0x85, 0xff, 0x74, 0x04, 0x8b, 0x47, 0x18, 0xc3, 0x31, 0xc0, 0xc3]

inductive Label where
  | load | zero | returnLoaded | returnZero
  deriving DecidableEq

def offset : Label → Word
  | .load => 5
  | .zero => 9
  | .returnLoaded => 8
  | .returnZero => 11

/-- Preserve the load label and view both machine return sites as the same exit. -/
def exitView : Label → SqliteStrLength.Label
  | .load => .load
  | .zero | .returnLoaded | .returnZero => .ret

/-- TEST/JE selects the forward load or zero block. Each exits at its own RET. -/
def graph : CFG Register Label Operation :=
  ⟨.term (.case (.val (.var .pointer)) .payload (.br .load (.var .pointer))
      .payload (.br .zero (.var .pointer))),
    [(.load, ⟨.pointer, .let1 .result (.app .loadLength (.var .pointer))
        (.term (.br .returnLoaded (.var .result)))⟩),
      (.zero, ⟨.pointer, .let1 .result (.val .unit) (.term (.br .returnZero (.var .result)))⟩)]⟩

/-- The actual branch and return offsets agree with the graph's selected labels.
The graph payload equals the machine's return register and the memory is unchanged. -/
def Bridge (entry final : MState) : Prop :=
  ∃ label terminal branch preRet,
    graph.entry.exec (model entry.memory) (fun k _ _ => some k) (entryStore entry) = some label ∧
    run Open.step 2 entry = some branch ∧ branch.core.rip = entry.core.rip + offset label ∧
    branch.core.read .rdi = pointer entry ∧ branch.memory = entry.memory ∧
    Open.step branch = some preRet ∧ preRet.core.rip = entry.core.rip + offset terminal ∧
    Open.step preRet = some final ∧
    (obs <$> graph.run (model entry.memory) (entryStore entry)) = some (terminal, final.core.read .rax) ∧
    final.memory = entry.memory

end Silmaril.Machine.Region.X86.SqliteStrLength.Clang
