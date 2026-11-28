module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FactTransport.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FactTransport.Coverage

/-! The actual intersection succeeds exactly on compatible fibres. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FactTransport.Proofs

open SeaOfNodes.Diamond (Val ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact TupleCovers)
open SeaOfNodes.Loop.MLIR.CF (model)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Port)
open Blocks (Bank)
open Identification (BankMap pull pushFacts collectFacts merge)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (EntryFacts)

variable {old new : List (ValueSort Width)}
variable {t : SeaOfNodes.Diamond.Ty Width}

private theorem cover_compatible (map : BankMap old new) (facts : EntryFacts old)
    (input : Bank (regs := new) model) (covers : TupleCovers facts (pull map input)) : Compatible map facts := by
  refine ⟨?_, ?_⟩
  · intro sort port empty
    have cell := covers port
    rw [empty] at cell
    exact cell
  · intro sort left right a b shared leftFact rightFact
    have l := covers left
    have r := covers right
    rw [leftFact, pull, get_tabulate, shared] at l
    rw [rightFact, pull, get_tabulate] at r
    exact (show a = input.get (map sort right) from l).trans (show b = input.get (map sort right) from r).symm

private theorem compatible_cover (map : BankMap old new) (facts : EntryFacts old)
    (compat : Compatible map facts) : ∃ input : Bank (regs := new) model, TupleCovers facts (pull map input) := by
  classical
  obtain ⟨fill, _⟩ := covered_of_nonbottom (tabulate (F := Fact Word) (dataPorts new) fun _ => .overdefined)
    (fun _ port => by rw [get_tabulate]; intro impossible; cases impossible)
  let constantAt {t} (target : Port (dataPorts new) t) :=
    ∃ (value : Val Word t) (source : Port (dataPorts old) t),
      map t source = target ∧ facts.get source = .constant value
  let input : Bank (regs := new) model := tabulate (dataPorts new) fun port =>
    if hit : constantAt port then Classical.choose hit else fill.get port
  refine ⟨input, ?_⟩
  intro sort port
  cases fact : facts.get port with
  | bottom => exact (compat.1 sort port fact).elim
  | overdefined => exact True.intro
  | constant value =>
    have hit : constantAt (map sort port) := ⟨value, port, rfl, fact⟩
    obtain ⟨source, shares, chosen⟩ := Classical.choose_spec hit
    change value = (pull map input).get port
    simp only [pull, input, get_tabulate, hit, dite_true]
    exact compat.2 sort port source value (Classical.choose hit) shares.symm fact chosen

theorem pushFacts_compatible_iff (map : BankMap old new) (facts : EntryFacts old) :
    (pushFacts map facts).isSome ↔ Compatible map facts := by
  constructor
  · intro someResult
    obtain ⟨out, checked⟩ := Option.isSome_iff_exists.mp someResult
    obtain ⟨input, covers⟩ := pushFacts_has_cover map facts out checked
    exact cover_compatible map facts input ((Identification.pushFacts_covers map facts out checked input).mp covers)
  · intro compat
    obtain ⟨input, covers⟩ := compatible_cover map facts compat
    exact Option.isSome_iff_ne_none.mpr fun conflict => Identification.pushFacts_refuses map facts conflict input covers

private theorem collect_unused (map : BankMap old new) (facts : EntryFacts old)
    (acc out : EntryFacts new) (target : Port (dataPorts new) t)
    (unused : ¬ ∃ origin, map t origin = target) (ok : collectFacts facts map acc = some out) :
    out.get target = acc.get target := by
  induction old generalizing acc with
  | nil =>
    cases facts
    cases ok
    rfl
  | cons sort rest ih =>
    cases facts with
    | cons head tail =>
      simp only [collectFacts] at ok
      cases merged : merge sort head (acc.get (map _ .head)) with
      | none => simp [merged] at ok
      | some value =>
        have apart : slot target ≠ slot (map _ .head) := by
          intro equal
          obtain ⟨rfl, sourceEq⟩ := Sigma.mk.inj_iff.mp (Reindex.slot_eq (map _ .head) target equal.symm)
          exact unused ⟨.head, eq_of_heq sourceEq⟩
        rw [merged] at ok
        exact (ih (fun s p => map s (.tail p)) tail (write (map _ .head) value acc)
          (fun ⟨origin, hit⟩ => unused ⟨.tail origin, hit⟩) ok).trans (get_write_other _ _ _ _ apart)

theorem pushFacts_unused (map : BankMap old new) (facts : EntryFacts old) (out : EntryFacts new)
    (target : Port (dataPorts new) t) (unused : ¬ ∃ origin, map t origin = target)
    (ok : pushFacts map facts = some out) : out.get target = .overdefined :=
  (collect_unused map facts _ out target unused ok).trans (get_tabulate _ target)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FactTransport.Proofs
