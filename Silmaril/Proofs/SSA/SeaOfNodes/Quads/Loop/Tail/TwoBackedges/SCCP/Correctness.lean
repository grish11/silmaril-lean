module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Thms
import Silmaril.SSA.SeaOfNodes.Quads.CFG.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Dataflow.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Proofs

open Diamond (Model Signature ValueSort Val dataPorts sortValue)
open Diamond.SCCP (Fact TupleCovers TupleLE evalFacts_cover evalFacts_mono readWires_cover readWires_mono tupleFacts)
open SeaOfNodes.Loop.SCCP (BankFacts BankDecidableEq BankCovers bankTuple
  bankTuple_mono tupleFacts_mono bankCovers_of_tuple bankCovers_mono)
open Join (Block)
open Blocks (Bank)
open RVSDG (Tuple)
open Semantics.Dataflow (Flat)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}
variable {m : Model.{u, v, w} Op}

theorem blockFacts_cover (block : Block Op regs)
    {facts : Tuple (Fact m.value) (dataPorts regs)} {old : Bank (regs := regs) m}
    (covers : TupleCovers facts old) : TupleCovers (blockFacts m block facts) (block.eval m old) := by
  let compiled := CFG.compileBlock block (Quads.initial regs)
  have native : compiled.outgoing.read old (compiled.flow.eval m old PUnit.unit) = block.eval m old :=
    (CFG.compileBlock_read (past := []) block m old PUnit.unit (Quads.initial regs)).trans
      (congrArg (block.eval m) (Quads.read_initial m old))
  have locals := evalFacts_cover compiled.flow covers
    (facts := PUnit.unit) (locals := PUnit.unit) (fun i => i.elim0)
  intro t port
  exact native ▸ readWires_cover compiled.outgoing covers locals port

theorem blockFacts_mono (block : Block Op regs)
    {a b : Tuple (Fact m.value) (dataPorts regs)} (le : TupleLE a b) :
    TupleLE (blockFacts m block a) (blockFacts m block b) := by
  let compiled := CFG.compileBlock block (Quads.initial regs)
  intro t port
  exact readWires_mono compiled.outgoing le
    (evalFacts_mono compiled.flow le (lhs := PUnit.unit) (rhs := PUnit.unit) (fun i => i.elim0)) port

private theorem choose_mono {a b : Flat (ULift.{w} Bool)} (test : a ≤ b)
    {t₁ t₂ f₁ f₂ : Marked} (onTrue : t₁ ⊆ t₂) (onFalse : f₁ ⊆ f₂) :
    choose a t₁ f₁ ⊆ choose b t₂ f₂ := by
  cases a with
  | bottom => simp [choose]
  | constant v =>
    cases b with
    | bottom => exact False.elim test
    | constant v' =>
      change v = v' at test
      subst v'
      by_cases side : v.down = true
      · simpa [choose, side] using onTrue
      · simpa [choose, side] using onFalse
    | overdefined =>
      by_cases side : v.down = true
      · simpa [choose, side] using onTrue.trans Finset.subset_union_left
      · simpa [choose, side] using onFalse.trans Finset.subset_union_right
  | overdefined =>
    cases b with
    | bottom | constant => exact False.elim test
    | overdefined => exact Finset.union_subset_union onTrue onFalse

theorem successors_mono {a b s t : Flat (ULift.{w} Bool)} (again : a ≤ b) (select : s ≤ t) :
    successors a s ⊆ successors b t :=
  choose_mono again (choose_mono select Finset.Subset.rfl Finset.Subset.rfl) Finset.Subset.rfl

private theorem choose_cover {fact : Flat (ULift.{w} Bool)} {actual : ULift.{w} Bool}
    (covered : fact.Covers actual) (onTrue onFalse : Marked) :
    (if actual.down then onTrue else onFalse) ⊆ choose fact onTrue onFalse := by
  cases fact with
  | bottom => exact False.elim covered
  | constant known =>
    change known = actual at covered
    subst known
    exact Finset.Subset.rfl
  | overdefined =>
    by_cases side : actual.down = true <;> simp [choose, side]

private theorem gate_le_iff {α : Type*} (marks : Marked) (mark : Fin 4) {value upper : Flat α} :
    gate marks mark value ≤ upper ↔ (mark ∈ marks → value ≤ upper) := by
  by_cases active : mark ∈ marks <;> simp [gate, active]

private theorem gate_mono {α : Type*} {a b : Marked} (marks : a ⊆ b) (mark : Fin 4)
    {value upper : Flat α} (le : value ≤ upper) : gate a mark value ≤ gate b mark upper := by
  apply (gate_le_iff a mark).mpr
  intro member
  simpa [gate, marks member] using le

theorem phiFacts_le_iff {value : Data → Type w} [equal : BankDecidableEq value (dataPorts regs)]
    (marks : Marked) (column : Incoming → BankFacts value (dataPorts regs))
    (upper : BankFacts value (dataPorts regs)) :
    phiFacts marks column ≤ upper ↔ ∀ edge, incomingIndex edge ∈ marks → column edge ≤ upper := by
  constructor
  · intro bound edge member i
    let _ := equal.atPort i
    have both := sup_le_iff.mp (bound i)
    have pair := sup_le_iff.mp both.1
    cases edge with
    | entry => exact (gate_le_iff _ _).mp pair.1 member
    | feedback side =>
      cases side
      · exact (gate_le_iff _ _).mp both.2 member
      · exact (gate_le_iff _ _).mp pair.2 member
  · intro bound i
    let _ := equal.atPort i
    exact sup_le (sup_le
      ((gate_le_iff _ _).mpr (fun member => bound .entry member i))
      ((gate_le_iff _ _).mpr (fun member => bound (.feedback true) member i)))
      ((gate_le_iff _ _).mpr (fun member => bound (.feedback false) member i))

variable {p : Program Op regs out} [BankDecidableEq m.value (dataPorts regs)]
variable {input : Tuple (Fact m.value) (dataPorts regs)}

theorem transfer_mono : Monotone (transfer m p input) := by
  intro a b le
  let left := blockFacts m p.header (bankTuple a.2.1)
  let right := blockFacts m p.header (bankTuple b.2.1)
  have header : TupleLE left right := blockFacts_mono p.header (bankTuple_mono le.2.1)
  refine ⟨?_, ?_, gate_mono le.1 _ (header p.result)⟩
  · change insert _ (if _ then successors (left.get p.again) (left.get p.select) else ∅) ⊆
      insert _ (if _ then successors (right.get p.again) (right.get p.select) else ∅)
    apply Finset.insert_subset_insert
    by_cases marked : incomingIndex .entry ∈ a.1
    · have nextMarked := le.1 marked
      simpa [marked, nextMarked] using successors_mono (header p.again) (header p.select)
    · simp [marked]
  · change phiFacts a.1 (columns m p input left) ≤ phiFacts b.1 (columns m p input right)
    apply (phiFacts_le_iff _ _ _).mpr
    intro edge marked
    have bound := (phiFacts_le_iff b.1 (columns m p input right) _).mp le_rfl edge (le.1 marked)
    refine le_trans ?_ bound
    cases edge with
    | entry => exact le_rfl
    | feedback side => exact tupleFacts_mono (blockFacts_mono (p.feedback side) header)

variable {state : State m.value regs out} {concrete : Bank (regs := regs) m}

private theorem entry_marked (fixed : transfer m p input state = state) :
    incomingIndex .entry ∈ state.1 := by
  rw [← fixed]
  simp [transfer]

private theorem fixed_initial (fixed : transfer m p input state = state) (covered : TupleCovers input concrete) :
    incomingIndex .entry ∈ state.1 ∧ BankCovers state.2.1 (p.preheader.eval m concrete) := by
  have marked := entry_marked fixed
  have bank := congrArg (fun s : State m.value regs out => s.2.1) fixed
  refine ⟨marked, ?_⟩
  rw [← bank]
  apply bankCovers_mono ((phiFacts_le_iff _ _ _).mp le_rfl .entry marked)
  exact bankCovers_of_tuple (blockFacts_cover p.preheader covered)

private theorem fixed_step (fixed : transfer m p input state = state) {old : Bank (regs := regs) m}
    (covered : BankCovers state.2.1 old) :
    match p.step m old with
    | .inl result => exitIndex ∈ state.1 ∧ state.2.2.Covers result
    | .inr (side, next) => incomingIndex (.feedback side) ∈ state.1 ∧ BankCovers state.2.1 next := by
  let current := p.header.eval m old
  let facts := blockFacts m p.header (bankTuple state.2.1)
  let again := current.get p.again
  let side := current.get p.select
  have header : TupleCovers facts current := blockFacts_cover p.header covered
  have enabled := entry_marked fixed
  have marks := congrArg Prod.fst fixed
  have marked {edge : Fin 4} (allowed : edge ∈ successors (facts.get p.again) (facts.get p.select)) :
      edge ∈ state.1 := by
    rw [← marks]
    simp [transfer, enabled, facts, allowed]
  have selected := choose_cover (header p.select)
    {incomingIndex (.feedback true)} {incomingIndex (.feedback false)}
  have continued := choose_cover (header p.again)
    (choose (facts.get p.select) {incomingIndex (.feedback true)} {incomingIndex (.feedback false)}) {exitIndex}
  change (match (if again.down then Sum.inr (side.down, (p.feedback side.down).eval m current)
                 else Sum.inl (current.get p.result)) with
    | .inl result => exitIndex ∈ state.1 ∧ state.2.2.Covers result
    | .inr (side, next) => incomingIndex (.feedback side) ∈ state.1 ∧ BankCovers state.2.1 next)
  by_cases taken : again.down = true
  · have arrival : incomingIndex (.feedback side.down) ∈ state.1 := by
      apply marked
      apply continued
      have inner : incomingIndex (.feedback side.down) ∈
          choose (facts.get p.select) {incomingIndex (.feedback true)} {incomingIndex (.feedback false)} := by
        apply selected
        change incomingIndex (.feedback side.down) ∈
          (if side.down then {incomingIndex (.feedback true)} else {incomingIndex (.feedback false)} : Marked)
        cases side.down <;> simp
      simpa only [show (current.get p.again).down = true from taken, ite_true] using inner
    simp only [taken, ite_true]
    refine ⟨arrival, ?_⟩
    rw [← congrArg (fun s : State m.value regs out => s.2.1) fixed]
    apply bankCovers_mono ((phiFacts_le_iff _ _ _).mp le_rfl (.feedback side.down) arrival)
    exact bankCovers_of_tuple (blockFacts_cover (p.feedback side.down) header)
  · have exits : exitIndex ∈ state.1 := by
      apply marked
      apply continued
      simp [show (current.get p.again).down ≠ true from taken]
    simp only [taken]
    refine ⟨exits, ?_⟩
    rw [← congrArg (fun s : State m.value regs out => s.2.2) fixed]
    change (gate state.1 exitIndex (facts.get p.result)).Covers (current.get p.result)
    rw [show gate state.1 exitIndex (facts.get p.result) = facts.get p.result from by simp [gate, exits]]
    exact header p.result

theorem fixed_arrives (fixed : transfer m p input state = state) (covered : TupleCovers input concrete)
    {via : Incoming} {count : Nat} {old : Bank (regs := regs) m}
    (arrived : p.Arrives m concrete via count old) :
    incomingIndex via ∈ state.1 ∧ BankCovers state.2.1 old := by
  induction arrived with
  | entry => exact fixed_initial fixed covered
  | feedback _ taken ih => simpa only [taken] using fixed_step fixed ih.2

private theorem fixed_header_return (fixed : transfer m p input state = state) (fuel : Nat)
    {old : Bank (regs := regs) m} {result : sortValue m.value out} (covered : BankCovers state.2.1 old)
    (returned : p.source.runFrom m fuel 1 old = some result) :
    exitIndex ∈ state.1 ∧ state.2.2.Covers result := by
  induction fuel using Nat.strong_induction_on generalizing old with
  | ind fuel smaller =>
    cases fuel with
    | zero => cases returned
    | succ fuel =>
      rw [p.source_header] at returned
      have next := fixed_step fixed covered
      cases taken : p.step m old with
      | inl value =>
        rw [taken] at returned next
        cases returned
        exact next
      | inr tagged =>
        obtain ⟨side, bank⟩ := tagged
        rw [taken] at returned next
        exact smaller (fuel - 2) (by omega) next.2 returned

theorem fixed_source_return (fixed : transfer m p input state = state) (covered : TupleCovers input concrete)
    {fuel : Nat} {result : sortValue m.value out}
    (returned : p.source.runFrom m fuel 0 concrete = some result) :
    exitIndex ∈ state.1 ∧ state.2.2.Covers result := by
  cases fuel with
  | zero => cases returned
  | succ fuel =>
    rw [p.source_entry] at returned
    exact fixed_header_return fixed fuel (fixed_initial fixed covered).2 returned

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Proofs
