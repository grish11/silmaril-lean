module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Deletion.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Deletion

open Silmaril.SSA.SeaOfNodes
open Diamond (Ty ValueSort dataPorts)
open GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Deletion
open Pure.SubZero (word)
open Pure.ConstantFold.Comparison (Opcode model)
open Quads (Quad write)
open Quads.Join (Block)
open Quads.Loop.Blocks (Bank)
open Quads.Loop.Tail.TwoBackedges (Incoming Program)
open Silmaril.SSA.RVSDG (Port Tuple)

variable {regs : List (ValueSort Unit)}

private def Away (destination : Nat) (left right : Bank (regs := regs) model) : Prop :=
  ∀ {t : Ty Unit} (port : Port (dataPorts regs) t), Quads.slot port ≠ destination → left.get port = right.get port

private theorem operands_eq {destination : Nat} {left right : Bank (regs := regs) model}
    (agree : Away destination left right) {ports : List (Ty Unit)}
    (operands : Tuple (Port (dataPorts regs)) ports) (avoids : operandsAvoid destination operands = true) :
    operands.map (fun _ port => left.get port) = operands.map (fun _ port => right.get port) := by
  induction operands with
  | nil => rfl
  | cons head tail ih =>
    have reads := Bool.and_eq_true_iff.mp avoids
    exact congrArg₂ Tuple.cons (agree head (of_decide_eq_true reads.1)) (ih reads.2)

private theorem read_after_same_write {T : Type} {F : T → Type} {ts : List T} {t s : T}
    (dest : Port ts t) (value : F t) (left right : Tuple F ts) (port : Port ts s)
    (same : Quads.slot port = Quads.slot dest ∨ left.get port = right.get port) :
    (write dest value left).get port = (write dest value right).get port := by
  induction dest with
  | head =>
    cases left with | cons _ left =>
    cases right with | cons _ right =>
    cases port with
    | head => rfl
    | tail _ => exact same.resolve_left (Nat.succ_ne_zero _)
  | tail dest ih =>
    cases left with | cons _ left =>
    cases right with | cons _ right =>
    cases port with
    | head => exact same.resolve_left (Ne.symm (Nat.succ_ne_zero _))
    | tail port => exact ih value left right port (same.imp Nat.succ.inj id)

private theorem tuple_eq {ps : List (Ty Unit)} {F : Ty Unit → Type} {left right : Tuple F ps}
    (same : ∀ {t} (port : Port ps t), left.get port = right.get port) : left = right := by
  have reads : (fun {t} (port : Port ps t) => left.get port) = (fun {t} (port : Port ps t) => right.get port) := by
    funext t port
    exact same port
  calc
    left = Quads.tabulate ps (fun port => left.get port) := (Quads.tabulate_get_eq left).symm
    _ = Quads.tabulate ps (fun port => right.get port) := congrArg (fun f => Quads.tabulate ps f) reads
    _ = right := Quads.tabulate_get_eq right

private theorem quad_read {destination : Nat} {left right : Bank (regs := regs) model}
    (agree : Away destination left right) (quad : Quad Opcode regs)
    (avoids : operandsAvoid destination quad.operands = true) {t : Ty Unit}
    (port : Port (dataPorts regs) t) (covered : Quads.slot port ≠ destination ∨ Quads.slot quad.dest = destination) :
    (quad.eval model left).get port = (quad.eval model right).get port := by
  unfold Quad.eval
  rw [operands_eq agree quad.operands avoids]
  apply read_after_same_write
  by_cases observed : Quads.slot port = destination
  · exact Or.inl (observed.trans (covered.resolve_left (fun different => different observed)).symm)
  · exact Or.inr (agree port observed)

private theorem scan_eval (block : Block Opcode regs) {destination : Nat} {atEnd : Bool}
    (accepted : safeThrough destination atEnd block = true) {left right : Bank (regs := regs) model}
    (agree : Away destination left right) :
    block.eval model left = block.eval model right ∨
      (atEnd = true ∧ Away destination (block.eval model left) (block.eval model right)) := by
  induction block generalizing left right with
  | nil => exact Or.inr ⟨accepted, agree⟩
  | cons quad rest ih =>
    have scanned := Bool.and_eq_true_iff.mp accepted
    rcases Bool.or_eq_true_iff.mp scanned.2 with overwritten | next
    · have joined : quad.eval model left = quad.eval model right :=
        tuple_eq (fun port => quad_read agree quad scanned.1 port (Or.inr (of_decide_eq_true overwritten)))
      exact Or.inl (congrArg (Block.eval rest model) joined)
    · exact ih next (fun port different => quad_read agree quad scanned.1 port (Or.inl different))

private theorem feedback_eq (block : Block Opcode regs) {destination : Nat}
    (accepted : safeThrough destination false block = true) {left right : Bank (regs := regs) model}
    (agree : Away destination left right) : block.eval model left = block.eval model right :=
  (scan_eval block accepted agree).resolve_right (fun refused => Bool.noConfusion refused.1)

variable (p : Program Opcode regs word) (index : Nat)

private theorem header_split {quad : Quad Opcode regs} (nomination : p.header[index]? = some quad) :
    p.header = p.header.take index ++ quad :: p.header.drop (index + 1) := by
  obtain ⟨inBounds, picked⟩ := List.getElem?_eq_some_iff.mp nomination
  rw [← picked, List.getElem_cons_drop, List.take_append_drop]

private theorem erase_header {quad : Quad Opcode regs} (nomination : p.header[index]? = some quad)
    (safe : safeThrough (Quads.slot quad.dest) (terminatorSafe p (Quads.slot quad.dest)) (p.header.drop (index + 1)) = true)
    (old : Bank (regs := regs) model) :
    (erase p index).header.eval model old = p.header.eval model old ∨
      (terminatorSafe p (Quads.slot quad.dest) = true ∧
        Away (Quads.slot quad.dest) ((erase p index).header.eval model old) (p.header.eval model old)) := by
  let before := Block.eval (p.header.take index) model old
  have beforeOverwrite : Away (Quads.slot quad.dest) before (quad.eval model before) :=
    fun port different => (Quads.get_write_other quad.dest port _ before different).symm
  have follows := scan_eval (p.header.drop (index + 1)) safe beforeOverwrite
  have original : p.header.eval model old = Block.eval (p.header.drop (index + 1)) model (quad.eval model before) := by
    conv_lhs => rw [header_split p index nomination]
    simp only [Block.eval, List.foldl_append, List.foldl_cons, before]
  rw [original]
  simpa only [erase, List.eraseIdx_eq_take_drop_succ, Block.eval, List.foldl_append, before] using follows

theorem erase_step (accepted : check p index = true) (old : Bank (regs := regs) model) :
    (erase p index).step model old = p.step model old := by
  cases nomination : p.header[index]? with
  | none => simp [check, nomination] at accepted
  | some quad =>
    have safe : safeThrough (Quads.slot quad.dest) (terminatorSafe p (Quads.slot quad.dest)) (p.header.drop (index + 1)) = true := by
      simpa only [check, nomination] using accepted
    let clean := (erase p index).header.eval model old
    let original := p.header.eval model old
    change (if (clean.get p.again).down then
      Sum.inr ((clean.get p.select).down, (p.feedback (clean.get p.select).down).eval model clean)
      else Sum.inl (clean.get p.result)) =
      (if (original.get p.again).down then
      Sum.inr ((original.get p.select).down, (p.feedback (original.get p.select).down).eval model original)
      else Sum.inl (original.get p.result))
    rcases erase_header p index nomination safe old with same | ⟨terminator, agree⟩
    · rw [show clean = original from same]
    · simp only [terminatorSafe, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at terminator
      have guard := agree p.again terminator.1
      have selector := agree p.select terminator.2.1
      have returned := agree p.result terminator.2.2.1
      have feedback (side : Bool) : (p.feedback side).eval model clean = (p.feedback side).eval model original := by
        cases side
        · exact feedback_eq (p.feedback false) terminator.2.2.2.2 agree
        · exact feedback_eq (p.feedback true) terminator.2.2.2.1 agree
      rw [guard, selector, returned, feedback]

theorem check_in_bounds (accepted : check p index = true) : index < p.header.length := by
  cases found : p.header[index]? with
  | none => simp [check, found] at accepted
  | some quad => exact (List.getElem?_eq_some_iff.mp found).1

theorem delete_eq_some {target : Program Opcode regs word} :
    delete? p index = some target ↔ check p index = true ∧ target = erase p index := by
  unfold delete?
  split
  · rename_i checked
    exact ⟨fun accepted => ⟨checked, (Option.some.inj accepted).symm⟩,
      fun ⟨_, exactTarget⟩ => congrArg some exactTarget.symm⟩
  · rename_i refused
    exact ⟨(fun accepted => by cases accepted), fun ⟨checked, _⟩ => (refused checked).elim⟩

theorem erase_count (accepted : check p index = true) : (erase p index).header.length + 1 = p.header.length := by
  have bound := check_in_bounds p index accepted
  have size := List.length_eraseIdx_of_lt bound
  change (p.header.eraseIdx index).length + 1 = p.header.length
  omega

private theorem run_header (accepted : check p index = true)
    (fuel : Nat) (old : Bank (regs := regs) model) :
    (erase p index).source.runFrom model fuel 1 old = p.source.runFrom model fuel 1 old := by
  induction fuel using Nat.strongRecOn generalizing old with
  | ind fuel ih =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      rw [Program.source_header, Program.source_header, erase_step p index accepted old]
      cases p.step model old with
      | inl => rfl
      | inr packet =>
        obtain ⟨side, next⟩ := packet
        exact ih (fuel - 2) (by omega) next

theorem erase_run (accepted : check p index = true) (fuel : Nat) (input : Bank (regs := regs) model) :
    (erase p index).source.runFrom model fuel 0 input = p.source.runFrom model fuel 0 input := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    rw [Program.source_entry, Program.source_entry]
    exact run_header p index accepted fuel (p.preheader.eval model input)

theorem erase_arrives (accepted : check p index = true)
    (input old : Bank (regs := regs) model) (via : Incoming) (count : Nat) :
    (erase p index).Arrives model input via count old ↔ p.Arrives model input via count old := by
  constructor
  · intro arrived
    induction arrived with
    | entry => exact .entry
    | feedback _ taken prior => exact .feedback prior ((erase_step p index accepted _).symm.trans taken)
  · intro arrived
    induction arrived with
    | entry => exact .entry
    | feedback _ taken prior => exact .feedback prior ((erase_step p index accepted _).trans taken)

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Deletion
