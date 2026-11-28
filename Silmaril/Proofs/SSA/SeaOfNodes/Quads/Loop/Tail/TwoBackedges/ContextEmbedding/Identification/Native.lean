module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Thms

/-! Singleton write fibres preserve projection throughout native execution. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Proofs

open SeaOfNodes.Diamond (Val ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Port Tuple)
open Blocks (Bank)
open Join (Block)
open Reindex.Guarded.Institution (Valuation)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

universe u w

variable {S T : EntrySignature} {old new : List (ValueSort Width)} {out : ValueSort Width}

theorem tuple_ext {K : Type u} {F : K → Type w} {ts : List K} {xs ys : Tuple F ts}
    (reads : ∀ {t} (p : Port ts t), xs.get p = ys.get p) : xs = ys := by
  rw [← tabulate_get_eq xs, ← tabulate_get_eq ys]
  exact congrArg (tabulate ts) (funext fun _ => funext reads)

theorem pull_get {F : SeaOfNodes.Diamond.Ty Width → Type} (map : BankMap old new)
    (input : Tuple F (dataPorts new)) {t : SeaOfNodes.Diamond.Ty Width} (port : Port (dataPorts old) t) :
    (pull map input).get port = input.get (map t port) :=
  get_tabulate _ port

theorem reduct_embedding (embedding : Embedding S T) (input : Valuation T) :
    reduct embedding.portMap input = embedding.reduct input :=
  tuple_ext fun port => (pull_get embedding.portMap input port).trans (embedding.reduct_get input port).symm

theorem ports_complete {K : Type u} {ts : List K} {t : K} (port : Port ts t) :
    (⟨t, port⟩ : Sigma (Port ts)) ∈ ports ts := by
  induction port with
  | head => exact List.mem_cons_self
  | @tail t fresh tail port ih =>
    let lift (p : Sigma (Port tail)) : Sigma (Port (fresh :: tail)) := ⟨p.1, .tail p.2⟩
    exact List.mem_cons_of_mem _ (List.mem_map_of_mem (f := lift) ih)

theorem checkWrites_iff (map : BankMap old new) (p : Program Op old out) :
    checkWrites map p = true ↔ SafeWrites map p := by
  simp only [checkWrites, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq, SafeWrites, SafeWrite]
  constructor
  · intro check q present t port sameImage
    exact (check q present ⟨t, port⟩ (ports_complete port)).resolve_left (fun h => h sameImage)
  · rintro safe q present ⟨t, port⟩ _
    by_cases sameImage : slot (map t port) = slot (map _ q.dest)
    · exact Or.inr (safe q present t port sameImage)
    · exact Or.inl sameImage

private theorem pull_write {F : SeaOfNodes.Diamond.Ty Width → Type} (map : BankMap old new)
    (q : Quad Op old) (safe : SafeWrite map q) (value : F (.value q.result))
    (input : Tuple F (dataPorts new)) :
    pull map (write (map _ q.dest) value input) = write q.dest value (pull map input) := by
  apply tuple_ext
  intro t port
  by_cases same : slot port = slot q.dest
  · obtain ⟨rfl, heq⟩ := Sigma.mk.inj_iff.mp (Reindex.slot_eq port q.dest same)
    obtain rfl := eq_of_heq heq
    rw [pull_get, get_write_same, get_write_same]
  · have distinct := fun sameImage => same (safe t port sameImage)
    rw [pull_get, get_write_other _ _ _ _ distinct, get_write_other _ _ _ _ same, pull_get]

private theorem operand_reads {F : SeaOfNodes.Diamond.Ty Width → Type} (map : BankMap old new)
    {args : List (SeaOfNodes.Diamond.Ty Width)} (operands : Tuple (Port (dataPorts old)) args)
    (input : Tuple F (dataPorts new)) :
    (operands.map map).map (G := F) (fun _ p => input.get p) =
      operands.map (G := F) (fun _ p => (pull map input).get p) := by
  induction operands with
  | nil => rfl
  | cons p rest ih => exact congrArg₂ Tuple.cons (pull_get map input p).symm ih

private theorem quad_eval (map : BankMap old new) (q : Quad Op old) (safe : SafeWrite map q)
    (input : Bank (regs := new) model) :
    pull map ((quad map q).eval model input) = q.eval model (pull map input) := by
  exact (pull_write (F := Val Word) map q safe _ input).trans
    (congrArg (fun operands => write q.dest (model.run q.op operands) (pull map input))
      (operand_reads map q.operands input))

private theorem block_eval (map : BankMap old new) (block : Block Op old)
    (safe : ∀ q ∈ block, SafeWrite map q) (input : Bank (regs := new) model) :
    pull map (Block.eval (block.map (quad map)) model input) = block.eval model (pull map input) := by
  induction block generalizing input with
  | nil => rfl
  | cons q rest ih =>
    have safeRest : ∀ q ∈ rest, SafeWrite map q := fun q mem => safe q (List.mem_cons_of_mem _ mem)
    simp only [Block.eval, List.map_cons, List.foldl_cons] at ih ⊢
    rw [ih safeRest, quad_eval map q (safe q List.mem_cons_self)]

/-- Singleton written fibres also commute with the shared ordered abstract writes. -/
theorem blockFacts_pull (map : BankMap old new) (block : Block Op old)
    (safe : ∀ q ∈ block, SafeWrite map q) (input : Tuple (Fact Word) (dataPorts new)) :
    pull map (SCCP.blockFacts model (block.map (quad map)) input) =
      SCCP.blockFacts model block (pull map input) := by
  simp only [SCCP.blockFacts_fold]
  induction block generalizing input with
  | nil => rfl
  | cons q rest ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [ih (fun other present => safe other (List.mem_cons_of_mem _ present))]
    apply congrArg (fun bank => rest.foldl (fun row quad => SCCP.quadFacts model quad row) bank)
    simp only [SCCP.quadFacts, quad, operand_reads]
    exact pull_write map q (safe q List.mem_cons_self) _ input

private theorem step_eq (map : BankMap old new) (p : Program Op old out)
    (safe : SafeWrites map p) (input : Bank (regs := new) model) :
    (match (program map p).step model input with
    | .inl value => Sum.inl value
    | .inr (side, next) => .inr (side, pull map next)) =
      p.step model (pull map input) := by
  have header := block_eval map p.header (fun q mem => safe q (by simp [quads, mem])) input
  have feedback (side : Bool) (bank : Bank (regs := new) model) :=
    block_eval map (p.feedback side) (fun q mem => safe q (by cases side <;> simp_all [quads])) bank
  let current := Block.eval (p.header.map (quad map)) model input
  change pull map current = _ at header
  simp only [program, Program.step]
  change (match (if (current.get (map _ p.again)).down then
    Sum.inr ((current.get (map _ p.select)).down,
      Block.eval ((p.feedback (current.get (map _ p.select)).down).map (quad map)) model current)
    else Sum.inl (current.get (map _ p.result))) with
    | .inl value => Sum.inl value
    | .inr (side, next) => .inr (side, pull map next)) = _
  rw [← header]
  simp only [pull_get]
  cases (current.get (map _ p.again)).down <;> simp [feedback] <;> rfl

private theorem header_run (map : BankMap old new) (p : Program Op old out)
    (safe : SafeWrites map p) (fuel : Nat) (input : Bank (regs := new) model) :
    (program map p).source.runFrom model fuel 1 input = p.source.runFrom model fuel 1 (pull map input) := by
  induction fuel using Nat.strong_induction_on generalizing input with
  | ind fuel ih =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      rw [Program.source_header, Program.source_header, ← step_eq map p safe]
      cases (program map p).step model input with
      | inl _ => rfl
      | inr edge =>
        obtain ⟨side, next⟩ := edge
        exact ih (fuel - 2) (by omega) next

theorem source_run (map : BankMap old new) (p : Program Op old out)
    (safe : SafeWrites map p) (fuel : Nat) (input : Bank (regs := new) model) :
    (program map p).source.runFrom model fuel 0 input = p.source.runFrom model fuel 0 (pull map input) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    rw [Program.source_entry, Program.source_entry, header_run map p safe]
    exact congrArg (p.source.runFrom model fuel 1)
      (block_eval map p.preheader (fun q mem => safe q (by simp [quads, mem])) input)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Proofs
