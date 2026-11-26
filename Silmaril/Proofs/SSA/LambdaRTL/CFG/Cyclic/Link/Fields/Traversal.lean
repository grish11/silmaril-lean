module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Defs
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Block
import Mathlib.Data.Finset.Card

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields

open Silmaril.Elgot
open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Comparison
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields

variable {V F α : Type} [DecidableEq V] {n a b : Nat} {graph : Graph V F a b}

private theorem private_step (model : PairModel F Part α) (packet : Fin n → α)
    {i : Fin graph.locals} {next : Label graph.locals b} {fields : FieldMap n}
    (edge : next? n graph i = some (next, fields)) :
    graph.step model.val (.inl i, encode model.val packet) =
      Part.some (.inr (next, encode model.val (packet ∘ fields))) := by
  simp [Graph.step, block_sound model packet (graph.block i) (fun _ => model.val.unit) edge]

private def Visited (remaining : Finset (Fin graph.locals)) : Label graph.locals b → Prop
  | .inl i => i ∉ remaining
  | .inr _ => False

/-- Visited blocks have checked successors. Their edges stay in the visited
set except for edges to the current label. -/
private def LinksBack (n : Nat) (remaining : Finset (Fin graph.locals)) (start : Label graph.locals b) : Prop :=
  ∀ i, i ∉ remaining → ∃ next fields,
    next? n graph i = some (next, fields) ∧ (next = start ∨ Visited (graph := graph) remaining next)

private theorem advance {remaining : Finset (Fin graph.locals)} {i : Fin graph.locals}
    {target : Label graph.locals b} {fields : FieldMap n}
    (links : LinksBack n remaining (.inl i)) (edge : next? n graph i = some (target, fields)) :
    LinksBack n (remaining.erase i) target := by
  intro j absent
  by_cases same : j = i
  · subst j
    exact ⟨target, fields, edge, Or.inl rfl⟩
  · obtain ⟨next, route, checked, whereNext⟩ := links j
      (fun member => absent (Finset.mem_erase.mpr ⟨same, member⟩))
    refine ⟨next, route, checked, Or.inr ?_⟩
    rcases whereNext with rfl | visited
    · exact fun member => (Finset.mem_erase.mp member).1 rfl
    · cases next with
      | inl k => exact fun member => visited (Finset.mem_erase.mp member).2
      | inr port => exact visited

/-- Every next state is private and still carries a well-formed packet.
No equality between the packets before and after a loop is required. -/
private theorem no_run (model : PairModel F Part α)
    {remaining : Finset (Fin graph.locals)}
    (closed : ∀ i, i ∉ remaining → ∃ (next : Label graph.locals b) (fields : FieldMap n),
      next? n graph i = some (next, fields) ∧ Visited (graph := graph) remaining next)
    {start : Label graph.locals b × α} {result : Fin b × α}
    (run : Silmaril.Elgot.Part.Runs (graph.step model.val) start result)
    (inside : Visited (graph := graph) remaining start.1)
    (shaped : ∃ packet : Fin n → α, start.2 = encode model.val packet) : False := by
  induction run with
  | @done start result returned =>
    rcases start with ⟨index | port, packet⟩
    · simp [Graph.step, Part.mem_map_iff] at returned
    · exact inside
  | @more start next result advanced _ ih =>
    rcases start with ⟨index | port, packet⟩
    · obtain ⟨fields, eq⟩ := shaped
      change packet = encode model.val fields at eq
      subst packet
      obtain ⟨target, route, checked, visited⟩ := closed index inside
      rw [private_step model fields checked] at advanced
      have same : next = (target, encode model.val (fields ∘ route)) := by simpa using advanced
      subst next
      exact ih visited ⟨fields ∘ route, rfl⟩
    · exact inside

private theorem predict_precompose {locals : Nat} (model : Model F Part α) (packet : Fin n → α)
    (fields : FieldMap n) (outcome : Outcome n locals b) :
    (outcome.precompose fields).predict model packet = outcome.predict model (packet ∘ fields) := by
  cases outcome <;> rfl

private theorem inspect_sound (model : PairModel F Part α) (remaining : Finset (Fin graph.locals))
    (start : Label graph.locals b) (links : LinksBack n remaining start) (packet : Fin n → α)
    (result : Part (Fin b × α))
    (found : (inspect n graph remaining start).predict model.val packet = some result) :
    iter (graph.step model.val) (start, encode model.val packet) = result := by
  induction remaining using Finset.strongInductionOn generalizing start packet with
  | _ remaining ih =>
    rw [inspect.eq_def] at found
    cases start with
    | inr port =>
      have same : Part.some (port, encode model.val packet) = result := Option.some.inj found
      rw [← same, congrFun (LawfulElgotMonad.fixpoint _) _]
      simp [Graph.step]
    | inl i =>
      by_cases fresh : i ∈ remaining
      · simp only [dite_eq_left fresh] at found
        cases checked : next? n graph i with
        | none => simp [checked, Outcome.predict] at found
        | some edge =>
          obtain ⟨next, route⟩ := edge
          simp only [checked, predict_precompose] at found
          rw [congrFun (LawfulElgotMonad.fixpoint _) _, private_step model packet checked,
            ← Part.pure_eq_some, pure_bind]
          exact ih (remaining.erase i) (Finset.erase_ssubset fresh) next (advance links checked)
            (packet ∘ route) found
      · have same : Part.none = result := by simpa [dite_eq_right fresh, Outcome.predict] using found
        have closed : ∀ j, j ∉ remaining → ∃ (next : Label graph.locals b) (fields : FieldMap n),
            next? n graph j = some (next, fields) ∧ Visited (graph := graph) remaining next := by
          intro j absent
          obtain ⟨next, fields, checked, rfl | known⟩ := links j absent
          · exact ⟨.inl i, fields, checked, fresh⟩
          · exact ⟨next, fields, checked, known⟩
        rw [← same]
        refine Part.eq_none_iff.mpr fun value member => ?_
        exact no_run model closed ((Silmaril.Elgot.Part.mem_iter_iff _ _ value).mp member) fresh ⟨packet, rfl⟩

theorem entry_sound (model : PairModel F Part α) (input : Fin a) (packet : Fin n → α)
    (result : Part (Fin b × α))
    (found : (entryOutcome n graph input).predict model.val packet = some result) :
    graph.denote model.val (input, encode model.val packet) = result :=
  inspect_sound model Finset.univ (graph.entry input)
    (fun _ absent => (absent (Finset.mem_univ _)).elim) packet result found

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields
