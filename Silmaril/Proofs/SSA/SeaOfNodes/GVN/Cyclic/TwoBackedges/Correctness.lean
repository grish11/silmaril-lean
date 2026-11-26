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
open Quads.Loop.Tail.TwoBackedges (Program)
open Silmaril.SSA.RVSDG (Port Tuple)

variable {regs : List (ValueSort Unit)}

private abbrev Concrete := Val model.value
private abbrev Symbolic (regs : List (ValueSort Unit)) := Val (numbering regs).value

/-- Each word key is evaluated in the bank at the beginning of the checked path. -/
private def Agrees (anchor : Bank (regs := regs) model) {ports : List (Ty Unit)}
    (keys : Tuple (Symbolic regs) ports) (values : Tuple Concrete ports) : Prop :=
  ∀ port : Port ports wordPort, (keys.get port).eval anchor = values.get port

private theorem write_agrees (anchor : Bank (regs := regs) model) {ports : List (Ty Unit)} {t : Ty Unit}
    (dest : Port ports t) (key : Symbolic regs t) (value : Concrete t)
    (keys : Tuple (Symbolic regs) ports) (values : Tuple Concrete ports)
    (prior : Agrees anchor keys values)
    (next : ∀ same : t = wordPort, (show Symbolic regs wordPort from same ▸ key).eval anchor =
      (show Concrete wordPort from same ▸ value)) :
    Agrees anchor (write dest key keys) (write dest value values) := by
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
    {keys : Keys regs} {values : Bank (regs := regs) model} (prior : Agrees anchor keys values) :
    Agrees anchor (quad.eval (numbering regs) keys) (quad.eval model values) := by
  obtain ⟨_, _, dest, op, operands⟩ := quad
  refine write_agrees anchor dest _ _ keys values prior ?_
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

private theorem block_agrees (block : Block Opcode regs) (anchor : Bank (regs := regs) model)
    {keys : Keys regs} {values : Bank (regs := regs) model} (prior : Agrees anchor keys values) :
    Agrees anchor (block.eval (numbering regs) keys) (block.eval model values) := by
  induction block generalizing keys values with
  | nil => exact prior
  | cons head tail ih => exact ih (quad_agrees head anchor prior)

private theorem entry_agrees (entry : Bank (regs := regs) model) :
    Agrees entry (entryKeys regs) entry :=
  fun port => entry_read_agrees entry (.arg port)

private theorem write_same {ports : List (Ty Unit)} {t : Ty Unit} (port : Port ports t)
    (bank : Tuple Concrete ports) : write port (bank.get port) bank = bank := by
  induction port with
  | head => cases bank; rfl
  | tail port ih => cases bank with | cons _ tail => exact congrArg (Tuple.cons _) (ih tail)

private theorem header_agrees {representative member : WordSlot regs} {old : Bank (regs := regs) model}
    (same : old.get representative = old.get member) :
    Agrees old (headerKeys representative member) old := by
  have agrees := write_agrees old member (.argument representative) (old.get member)
    (entryKeys regs) old (entry_agrees old) (fun eq => by cases eq; exact same)
  rw [write_same] at agrees
  exact agrees

private theorem match_reads {anchor values : Bank (regs := regs) model} {keys : Keys regs}
    (agrees : Agrees anchor keys values) {first second : WordSlot regs}
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

private theorem next_eq (accepted : check p representative member replacement = true)
    {old next : Bank (regs := regs) model} {side : Bool}
    (same : old.get representative = old.get member) (taken : p.step model old = .inr (side, next)) :
    next.get representative = next.get member := by
  unfold Program.step at taken
  dsimp only at taken
  split at taken
  · have pair := Sum.inr.inj taken
    have sideEq := congrArg Prod.fst pair
    have bankEq := congrArg Prod.snd pair
    change (p.feedback (Tuple.get (p.header.eval model old) p.select).down).eval model
      (p.header.eval model old) = next at bankEq
    change (Tuple.get (p.header.eval model old) p.select).down = side at sideEq
    rw [sideEq] at bankEq
    rw [← bankEq]
    have matched := (checked_parts accepted).2
    cases side
    · exact feedback_eq false matched.2.1 same
    · exact feedback_eq true matched.1 same
  · contradiction

theorem arrives_eq (accepted : check p representative member replacement = true)
    {input old : Bank (regs := regs) model} {arriving : Quads.Loop.Tail.TwoBackedges.Incoming} {count : Nat}
    (arrived : p.Arrives model input arriving count old) :
    old.get representative = old.get member := by
  induction arrived with
  | entry => exact entry_eq (checked_parts accepted).1 input
  | feedback _ taken prior => exact next_eq accepted prior taken

theorem rewrite_step_eq (accepted : rewrite? p representative member replacement = some target)
    {old : Bank (regs := regs) model} (same : old.get representative = old.get member) :
    target.step model old = p.step model old := by
  obtain ⟨matched, rfl⟩ := rewrite_exact accepted
  have returned := exit_eq (checked_parts matched).2.2.2 same
  simp only [Program.step, returned]

private theorem run_header_eq (accepted : rewrite? p representative member replacement = some target)
    (fuel : Nat) (old : Bank (regs := regs) model) (same : old.get representative = old.get member) :
    target.source.runFrom model fuel 1 old = p.source.runFrom model fuel 1 old := by
  induction fuel using Nat.strongRecOn generalizing old with
  | ind fuel ih =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      rw [target.source_header, p.source_header, rewrite_step_eq accepted same]
      cases taken : p.step model old with
      | inl => rfl
      | inr packet =>
        obtain ⟨side, next⟩ := packet
        exact ih (fuel - 2) (by omega) next (next_eq (rewrite_exact accepted).1 same taken)

theorem rewrite_run_eq (accepted : rewrite? p representative member replacement = some target)
    (fuel : Nat) (input : Bank (regs := regs) model) :
    target.source.runFrom model fuel 0 input = p.source.runFrom model fuel 0 input := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    have sameEntry : target.preheader = p.preheader := by rw [(rewrite_exact accepted).2]
    rw [target.source_entry, p.source_entry, sameEntry]
    exact run_header_eq accepted fuel _ (entry_eq (checked_parts (rewrite_exact accepted).1).1 input)

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges
