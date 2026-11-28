module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Defs
import Silmaril.SSA.SeaOfNodes.GVN.WordNumber.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges

open Silmaril.SSA.SeaOfNodes
open Diamond (Ty Val ValueSort dataPorts)
open GVN.WordNumber (Key entryKeys entry_read_agrees)
open GVN.Cyclic.TwoBackedges
open Pure.SubZero (word wordPort)
open Pure.ConstantFold.Comparison (Opcode model)
open Quads (Quad write)
open Quads.Join (Block)
open Quads.Loop.Blocks (Bank)
open Quads.Loop.Tail.TwoBackedges (Incoming Program)
open Silmaril.SSA.RVSDG (Port Tuple)

variable {regs : List (ValueSort Unit)}

private abbrev Concrete := Val model.value
private abbrev Symbolic (regs : List (ValueSort Unit)) := Val (numbering regs).value

private theorem write_agrees {F : Ty Unit → Type} {ports : List (Ty Unit)} {t : Ty Unit}
    (interpret : Symbolic regs wordPort → F wordPort)
    (dest : Port ports t) (key : Symbolic regs t) (value : F t)
    (keys : Tuple (Symbolic regs) ports) (values : Tuple F ports)
    (prior : ∀ port : Port ports wordPort, interpret (keys.get port) = values.get port)
    (next : ∀ same : t = wordPort, interpret (show Symbolic regs wordPort from same ▸ key) =
      (show F wordPort from same ▸ value)) :
    ∀ port : Port ports wordPort,
      interpret ((write dest key keys).get port) = (write dest value values).get port := by
  induction dest with
  | head =>
    cases keys with | cons _ keys =>
    cases values with | cons _ values =>
    intro port
    cases port with
    | head => exact next rfl
    | tail port => exact prior (.tail port)
  | tail dest ih =>
    cases keys with | cons _ keys =>
    cases values with | cons _ values =>
    intro port
    cases port with
    | head => exact prior .head
    | tail port => exact ih key value keys values (fun p => prior (.tail p)) next port

private theorem quad_agrees (quad : Quad Opcode regs) (anchor : Bank (regs := regs) model)
    {keys : Keys regs} {values : Bank (regs := regs) model} (prior : Keys.Reads anchor keys values) :
    Keys.Reads anchor (quad.eval (numbering regs) keys) (quad.eval model values) := by
  obtain ⟨_, _, dest, op, operands⟩ := quad
  refine write_agrees (regs := regs) (F := Concrete) (Key.eval anchor) dest _ _ keys values prior ?_
  intro same
  cases op with
  | arithmetic op =>
    cases op with
    | literal => cases operands; rfl
    | add | sub | mul =>
      cases operands with | cons first rest =>
      cases rest with | cons second rest =>
      cases rest
      first
      | exact congrArg₂ BitVec.add (prior first) (prior second)
      | exact congrArg₂ BitVec.sub (prior first) (prior second)
      | exact congrArg₂ BitVec.mul (prior first) (prior second)
  | boolean _ | eq | slt | sle | not => cases same

theorem block_agrees (block : Block Opcode regs) (anchor : Bank (regs := regs) model)
    {keys : Keys regs} {values : Bank (regs := regs) model} (prior : Keys.Reads anchor keys values) :
    Keys.Reads anchor (block.eval (numbering regs) keys) (block.eval model values) := by
  induction block generalizing keys values with
  | nil => exact prior
  | cons head tail ih => exact ih (quad_agrees head anchor prior)

private theorem quad_substitutes (quad : Quad Opcode regs)
    (arguments : WordSlot regs → Key (dataPorts regs)) {fine coarse : Keys regs}
    (related : ∀ port : WordSlot regs, (fine.get port).substitute arguments = coarse.get port) :
    ∀ port : WordSlot regs, ((quad.eval (numbering regs) fine).get port).substitute arguments =
      (quad.eval (numbering regs) coarse).get port := by
  obtain ⟨_, _, dest, op, operands⟩ := quad
  refine write_agrees (regs := regs) (F := Symbolic regs) (Key.substitute arguments) dest _ _ fine coarse related ?_
  intro same
  cases op with
  | arithmetic op =>
    cases op with
    | literal => cases operands; rfl
    | add | sub | mul =>
      cases operands with | cons first rest =>
      cases rest with | cons second rest =>
      cases rest
      first
      | exact congrArg₂ (Key.binary .add) (related first) (related second)
      | exact congrArg₂ (Key.binary .sub) (related first) (related second)
      | exact congrArg₂ (Key.binary .mul) (related first) (related second)
  | boolean _ | eq | slt | sle | not => cases same

theorem block_substitutes (block : Block Opcode regs)
    (arguments : WordSlot regs → Key (dataPorts regs)) {fine coarse : Keys regs}
    (related : ∀ port : WordSlot regs, (fine.get port).substitute arguments = coarse.get port) :
    ∀ port : WordSlot regs, ((block.eval (numbering regs) fine).get port).substitute arguments =
      (block.eval (numbering regs) coarse).get port := by
  induction block generalizing fine coarse with
  | nil => exact related
  | cons head tail ih => exact ih (quad_substitutes head arguments related)

theorem entry_agrees (entry : Bank (regs := regs) model) :
    Keys.Reads entry (entryKeys regs) entry :=
  fun port => entry_read_agrees entry (.arg port)

private theorem write_same {ports : List (Ty Unit)} {t : Ty Unit} (port : Port ports t)
    (bank : Tuple Concrete ports) : write port (bank.get port) bank = bank := by
  induction port with
  | head => cases bank; rfl
  | tail port ih => cases bank with | cons _ tail => exact congrArg (Tuple.cons _) (ih tail)

private theorem header_agrees {representative member : WordSlot regs} {old : Bank (regs := regs) model}
    (same : old.get representative = old.get member) :
    Keys.Reads old (headerKeys representative member) old := by
  have agrees := write_agrees (regs := regs) (F := Concrete) (Key.eval old) member (.argument representative) (old.get member)
    (entryKeys regs) old (entry_agrees old) (fun eq => by cases eq; exact same)
  rw [write_same] at agrees
  exact agrees

theorem match_reads {anchor values : Bank (regs := regs) model} {keys : Keys regs}
    (agrees : Keys.Reads anchor keys values) {first second : WordSlot regs}
    (matched : (keys.get first).matches (keys.get second) = true) :
    values.get first = values.get second :=
  (agrees first).symm.trans ((congrArg (Key.eval anchor) (Key.eq_of_matches matched)).trans (agrees second))

variable {p target : Program Opcode regs word} {representative member replacement : WordSlot regs}

theorem entry_eq (accepted : entryMatches p representative member = true)
    (input : Bank (regs := regs) model) :
    (p.preheader.eval model input).get representative = (p.preheader.eval model input).get member :=
  match_reads (block_agrees p.preheader input (entry_agrees input)) accepted

theorem feedback_eq (side : Bool) (accepted : feedbackMatches p representative member side = true)
    {old : Bank (regs := regs) model} (same : old.get representative = old.get member) :
    ((p.feedback side).eval model (p.header.eval model old)).get representative =
      ((p.feedback side).eval model (p.header.eval model old)).get member :=
  match_reads (block_agrees (p.feedback side) old (block_agrees p.header old (header_agrees same))) accepted

theorem exit_eq (accepted : exitMatches p representative member replacement = true)
    {old : Bank (regs := regs) model} (same : old.get representative = old.get member) :
    (p.header.eval model old).get p.result = (p.header.eval model old).get replacement :=
  match_reads (block_agrees p.header old (header_agrees same)) accepted

private theorem checked_parts (accepted : check p representative member replacement = true) :
    entryMatches p representative member = true ∧
    feedbackMatches p representative member true = true ∧
    feedbackMatches p representative member false = true ∧
    exitMatches p representative member replacement = true := by
  simpa only [check, Bool.and_eq_true, and_assoc] using accepted

theorem rewrite_exact (accepted : rewrite? p representative member replacement = some target) :
    check p representative member replacement = true ∧ target = {p with result := replacement} := by
  unfold rewrite? at accepted
  split at accepted
  · rename_i matched
    exact ⟨matched, (Option.some.inj accepted).symm⟩
  · contradiction

section Replay

variable {holds : Bank (regs := regs) model → Prop}

private theorem invariant_next (invariant : Invariant p holds)
    {old next : Bank (regs := regs) model} {side : Bool}
    (prior : holds old) (taken : p.step model old = .inr (side, next)) : holds next := by
  unfold Program.step at taken
  dsimp only at taken
  split at taken
  · have pair := Sum.inr.inj taken
    have sideEq := congrArg Prod.fst pair
    have bankEq := congrArg Prod.snd pair
    change (p.feedback ((p.header.eval model old).get p.select).down).eval model
      (p.header.eval model old) = next at bankEq
    change ((p.header.eval model old).get p.select).down = side at sideEq
    rw [sideEq] at bankEq
    exact bankEq ▸ invariant.feedback side old prior
  · contradiction

theorem invariant_arrives (invariant : Invariant p holds)
    {input old : Bank (regs := regs) model} {via : Incoming} {count : Nat}
    (arrived : p.Arrives model input via count old) : holds old := by
  induction arrived with
  | entry => exact invariant.entry input
  | feedback _ taken prior => exact invariant_next invariant prior taken

theorem redirect_step {old : Bank (regs := regs) model}
    (returned : (p.header.eval model old).get p.result = (p.header.eval model old).get replacement) :
    (redirect p replacement).step model old = p.step model old := by
  simp only [redirect, Program.step, returned]
  rfl

private theorem redirect_run_header (invariant : Invariant p holds)
    (observes : ∀ old, holds old →
      (p.header.eval model old).get p.result = (p.header.eval model old).get replacement)
    (fuel : Nat) (old : Bank (regs := regs) model) (prior : holds old) :
    (redirect p replacement).source.runFrom model fuel 1 old = p.source.runFrom model fuel 1 old := by
  induction fuel using Nat.strongRecOn generalizing old with
  | ind fuel ih =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      rw [Program.source_header, Program.source_header, redirect_step (observes old prior)]
      cases taken : p.step model old with
      | inl => rfl
      | inr packet =>
        obtain ⟨side, next⟩ := packet
        exact ih (fuel - 2) (by omega) next (invariant_next invariant prior taken)

theorem redirect_run (invariant : Invariant p holds)
    (observes : ∀ old, holds old →
      (p.header.eval model old).get p.result = (p.header.eval model old).get replacement)
    (fuel : Nat) (input : Bank (regs := regs) model) :
    (redirect p replacement).source.runFrom model fuel 0 input = p.source.runFrom model fuel 0 input := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    rw [Program.source_entry, Program.source_entry]
    exact redirect_run_header invariant observes fuel _ (invariant.entry input)

end Replay

private theorem single_invariant (accepted : check p representative member replacement = true) :
    Invariant p (fun old => old.get representative = old.get member) where
  entry := entry_eq (checked_parts accepted).1
  feedback side _ same := by
    have matched := (checked_parts accepted).2
    cases side
    · exact feedback_eq false matched.2.1 same
    · exact feedback_eq true matched.1 same

theorem arrives_eq (accepted : check p representative member replacement = true)
    {input old : Bank (regs := regs) model} {arriving : Incoming} {count : Nat}
    (arrived : p.Arrives model input arriving count old) :
    old.get representative = old.get member :=
  invariant_arrives (single_invariant accepted) arrived

theorem rewrite_step_eq (accepted : rewrite? p representative member replacement = some target)
    {old : Bank (regs := regs) model} (same : old.get representative = old.get member) :
    target.step model old = p.step model old := by
  obtain ⟨matched, rfl⟩ := rewrite_exact accepted
  exact redirect_step (exit_eq (checked_parts matched).2.2.2 same)

theorem rewrite_run_eq (accepted : rewrite? p representative member replacement = some target)
    (fuel : Nat) (input : Bank (regs := regs) model) :
    target.source.runFrom model fuel 0 input = p.source.runFrom model fuel 0 input := by
  obtain ⟨matched, rfl⟩ := rewrite_exact accepted
  exact redirect_run (single_invariant matched) (fun _ same => exit_eq (checked_parts matched).2.2.2 same) fuel input

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges
