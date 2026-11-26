module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms

/-! The emitted contract represents intersection along the typed port map. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Proofs

open SeaOfNodes.Diamond (Val ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact TupleCovers)
open SeaOfNodes.MLIR (Word)
open Semantics.Dataflow (Flat)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Port Tuple)
open Blocks (Bank)
open SeaOfNodes.Loop.MLIR.CF (model)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (EntryFacts)

variable {old new : List (ValueSort Width)}

private theorem merge_covers (sort : ValueSort Width) (left right combined : Fact Word (.value sort))
    (ok : merge sort left right = some combined) (value : Val Word (.value sort)) :
    combined.Covers value ↔ left.Covers value ∧ right.Covers value := by
  cases left <;> cases right <;> simp [merge] at ok
  all_goals first
  | subst combined
    simp [Flat.Covers]
  | rename_i left right
    by_cases same : left = right
    · simp [same] at ok
      subst combined
      simp [Flat.Covers, same]
    · simp [same] at ok

private theorem merge_exists (sort : ValueSort Width) (left right : Fact Word (.value sort))
    (value : Val Word (.value sort)) (hl : left.Covers value) (hr : right.Covers value) :
    ∃ combined, merge sort left right = some combined := by
  cases left <;> cases right <;> simp [merge, Flat.Covers] at *
  simp [hl.trans hr.symm]

private theorem write_merge_covers {sort : ValueSort Width} (dest : Port (dataPorts new) (.value sort))
    (head combined : Fact Word (.value sort)) (prior : EntryFacts new)
    (ok : merge sort head (prior.get dest) = some combined) (input : Bank (regs := new) model) :
    TupleCovers (write dest combined prior) input ↔
      TupleCovers prior input ∧ head.Covers (input.get dest) := by
  have atDest := merge_covers sort head (prior.get dest) combined ok (input.get dest)
  constructor
  · intro covered
    have merged := covered dest
    rw [get_write_same] at merged
    obtain ⟨headCovers, priorCovers⟩ := atDest.mp merged
    refine ⟨?_, headCovers⟩
    intro t port
    by_cases same : slot port = slot dest
    · obtain ⟨rfl, heq⟩ := Sigma.mk.inj_iff.mp (Reindex.slot_eq port dest same)
      obtain rfl := eq_of_heq heq
      exact priorCovers
    · have read := covered port
      rwa [get_write_other _ _ _ _ same] at read
  · rintro ⟨covered, headCovers⟩ t port
    by_cases same : slot port = slot dest
    · obtain ⟨rfl, heq⟩ := Sigma.mk.inj_iff.mp (Reindex.slot_eq port dest same)
      obtain rfl := eq_of_heq heq
      rw [get_write_same]
      exact atDest.mpr ⟨headCovers, covered _⟩
    · rw [get_write_other _ _ _ _ same]
      exact covered port

private theorem covers_cons {sort : ValueSort Width} (head : Fact Word (.value sort))
    (rest : EntryFacts old) (map : BankMap (sort :: old) new) (input : Bank (regs := new) model) :
    TupleCovers (.cons head rest) (pull map input) ↔
      head.Covers (input.get (map _ .head)) ∧
        TupleCovers rest (pull (fun t port => map t (.tail port)) input) := by
  constructor
  · intro h
    exact ⟨h .head, fun {_} port => h (.tail port)⟩
  · rintro ⟨h, covered⟩ t port
    cases port with
    | head => exact h
    | tail port => exact covered port

private theorem collect_covers (facts : EntryFacts old) (map : BankMap old new)
    (accumulated combined : EntryFacts new) (ok : collectFacts facts map accumulated = some combined)
    (input : Bank (regs := new) model) :
    TupleCovers combined input ↔ TupleCovers accumulated input ∧ TupleCovers facts (pull map input) := by
  induction old generalizing accumulated with
  | nil =>
    cases facts
    cases ok
    exact ⟨fun h => ⟨h, fun {_} p => nomatch p⟩, And.left⟩
  | cons sort rest ih =>
    cases facts with
    | cons head tail =>
      unfold collectFacts at ok
      cases merged : merge sort head (accumulated.get (map (.value sort) .head)) with
      | none => simp [merged] at ok
      | some fresh =>
        simp only [merged] at ok
        rw [ih _ _ _ ok, write_merge_covers _ _ _ _ merged, covers_cons]
        exact and_assoc

private theorem collect_exists (facts : EntryFacts old) (map : BankMap old new) (accumulated : EntryFacts new)
    (input : Bank (regs := new) model)
    (accCovers : TupleCovers accumulated input) (oldCovers : TupleCovers facts (pull map input)) :
    ∃ combined, collectFacts facts map accumulated = some combined := by
  induction old generalizing accumulated with
  | nil => cases facts; exact ⟨accumulated, rfl⟩
  | cons sort rest ih =>
    cases facts with
    | cons head tail =>
      obtain ⟨headCovers, tailCovers⟩ := (covers_cons head tail map input).mp oldCovers
      let dest := map (.value sort) .head
      obtain ⟨fresh, merged⟩ := merge_exists sort head (accumulated.get dest) (input.get dest)
        headCovers (accCovers dest)
      have updated : TupleCovers (write dest fresh accumulated) input :=
        (write_merge_covers dest head fresh accumulated merged input).mpr ⟨accCovers, headCovers⟩
      obtain ⟨output, ok⟩ := ih tail (fun t port => map t (.tail port)) (write dest fresh accumulated) updated tailCovers
      exact ⟨output, (congrArg (fun answer => answer.bind fun fact =>
        collectFacts tail (fun t port => map t (.tail port)) (write dest fact accumulated)) merged).trans ok⟩

private theorem all_covered (input : Bank (regs := new) model) :
    TupleCovers (tabulate (dataPorts new) fun _ => .overdefined) input := by
  intro t port
  rw [get_tabulate]
  exact True.intro

theorem pushFacts_covers (map : BankMap old new) (facts : EntryFacts old) (combined : EntryFacts new)
    (ok : pushFacts map facts = some combined) (input : Bank (regs := new) model) :
    TupleCovers combined input ↔ TupleCovers facts (pull map input) :=
  (collect_covers facts map _ combined ok input).trans (and_iff_right (all_covered input))

theorem pushFacts_refuses (map : BankMap old new) (facts : EntryFacts old)
    (refused : pushFacts map facts = none) (input : Bank (regs := new) model) :
    ¬ TupleCovers facts (pull map input) := by
  intro covered
  obtain ⟨combined, ok⟩ := collect_exists facts map _ input (all_covered input) covered
  change pushFacts map facts = some combined at ok
  rw [refused] at ok
  cases ok

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Proofs
