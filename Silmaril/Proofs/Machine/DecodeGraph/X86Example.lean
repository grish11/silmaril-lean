module

public import Silmaril.Machine.DecodeGraph.Thms
public import Silmaril.X86.Stack

/-! A stack-subset decoder, with a toy observable block machine, not x86 execution. -/

namespace Silmaril.Machine.DecodeGraph.X86Example

open scoped SetRel
open Silmaril.X86 (Insn)

private inductive Exit where
  | call (displacement : BitVec 32)
  | ret

private def transfer : Insn → Option Exit
  | .call displacement => some (.call displacement)
  | .ret => some .ret
  | _ => none

/-- A syntactic boundary policy for this subset, distinct from branch execution. -/
private def ends (_ : Unit) (_ : Nat) (instr : Insn) : Prop := (transfer instr).isSome = true

private def decoder : Graph (Unit × Nat) Insn := ofDecoder Insn.byteDecoder
private def blockDecoder : Graph (Unit × Nat) (List Insn) := blocks decoder ends 2

private def input : (Unit × Nat) × Bytes := (((), 16), [0x41, 0x50, 0xC3, 0xCC])
private def code : List Insn := [.push .r8, .ret]

/-- `41 50` decodes as `push r8`, then `c3` terminates at exit boundary 19.
`cc` is outside the block, and the return target is not computed by decoding. -/
theorem pushRet_decodes : (input, (code, 3)) ∈ blockDecoder := by
  change Path decoder ends 2 () 16 [0x41, 0x50, 0xC3, 0xCC] [.push .r8, .ret] (2 + 1)
  exact .next (width := 2) rfl (by decide) (by decide) (by change ¬ (false = true); decide)
    (.last rfl (by decide) (by decide) rfl)

theorem pushRet_outcome {result : List Insn × Nat} :
    (input, result) ∈ blockDecoder ↔ result = (code, 3) :=
  ⟨fun h => blocks_deterministic (ofDecoder_deterministic Insn.byteDecoder) ends 2 h pushRet_decodes,
    fun h => h.symm ▸ pushRet_decodes⟩

/-- A truncated REX prefix is not a fault outcome or an empty decoded block. -/
theorem truncated_no_block : (((), 16), [0x41]) ∉ blockDecoder.dom := by
  rintro ⟨⟨code, span⟩, path⟩
  change Path decoder ends 2 () 16 [0x41] code span at path
  cases path with
  | last decoded => cases (show none = some _ from decoded)
  | next decoded => cases (show none = some _ from decoded)

private abbrev Summary := Nat × Exit

/-- Ordinary instructions increment a toy observation counter. A transfer emits
an exit tag only at the end of the listing. There is no stack or PC state here. -/
private def summarize : List Insn → Option Summary
  | [] => none
  | instr :: rest =>
    match transfer instr with
    | some exit => if rest.isEmpty then some (0, exit) else none
    | none => (summarize rest).map fun (count, exit) => (count + 1, exit)

private def listing : SetRel (List Insn) (List Summary) :=
  Accept.ofPartial fun instructions => (summarize instructions).map fun summary => [summary]

private def machine : Observed (List Summary) Summary :=
  Accept.ofPartial fun
    | [summary] => some summary
    | _ => none

private def listMachine : Observed (List Insn) Summary := rebase listing machine

private def byteToList : SetRel ((Unit × Nat) × Bytes) (List Insn) :=
  blockDecoder ○ Function.graph Prod.fst

/-- An entire two-instruction listing maps to one abstract block, not pointwise. -/
theorem pushRet_abstracts : (code, [(1, .ret)]) ∈ listing := rfl

theorem pushRet_transports : (input, ([(1, .ret)], 3)) ∈ transport listing blockDecoder :=
  ⟨(code, 3), pushRet_decodes, pushRet_abstracts, rfl⟩

theorem pushRet_list_observation : (code, (1, .ret)) ∈ listMachine :=
  ⟨[(1, .ret)], pushRet_abstracts, rfl⟩

theorem pushRet_byte_observation : (input, (1, .ret)) ∈ rebase byteToList listMachine :=
  ⟨code, ⟨(code, 3), pushRet_decodes, rfl⟩, pushRet_list_observation⟩

theorem pushRet_staged_rebase :
    rebase (byteToList ○ listing) machine = rebase byteToList listMachine := rebase_comp ..

end Silmaril.Machine.DecodeGraph.X86Example
