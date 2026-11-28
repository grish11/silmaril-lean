module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width.Defs
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Thms
import Mathlib.Data.Finset.Card

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width

open Silmaril.Elgot
open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Comparison
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields (Route encode blockTo_evalJump)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width

variable {V F α : Type} [DecidableEq V] {a b : Nat} {graph : Graph V F a b}
variable {inputs : Fin a → Nat} {outputs : Fin b → Nat} {profile : Profile graph inputs outputs}

private theorem private_step (model : PairModel F Part α) {i : Fin graph.locals}
    (packet : Fin (profile.localWidth i) → α) {next : Label graph.locals b}
    {route : Route (profile.localWidth i) (profile.width next)}
    (edge : next? profile i = some ⟨next, route⟩) :
    graph.step model.val (.inl i, encode model.val packet) =
      Part.some (.inr (next, encode model.val (packet ∘ route))) := by
  simp [Graph.step, blockTo_evalJump model packet profile.width (graph.block i) (fun _ => model.val.unit) edge]

private def Visited (remaining : Finset (Fin graph.locals)) : Label graph.locals b → Prop
  | .inl i => i ∉ remaining
  | .inr _ => False

/-- Visited blocks have checked successors. Their edges stay in the visited
set except for edges to the current label. -/
private def LinksBack (profile : Profile graph inputs outputs) (remaining : Finset (Fin graph.locals)) (start : Label graph.locals b) : Prop :=
  ∀ i, i ∉ remaining → ∃ next fields,
    next? profile i = some ⟨next, fields⟩ ∧ (next = start ∨ Visited (graph := graph) remaining next)

private theorem advance {remaining : Finset (Fin graph.locals)} {i : Fin graph.locals}
    {target : Label graph.locals b} {fields : Route (profile.localWidth i) (profile.width target)}
    (links : LinksBack profile remaining (.inl i)) (edge : next? profile i = some ⟨target, fields⟩) :
    LinksBack profile (remaining.erase i) target := by
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
    (closed : ∀ i, i ∉ remaining → ∃ (next : Label graph.locals b) (fields : Route (profile.localWidth i) (profile.width next)),
      next? profile i = some ⟨next, fields⟩ ∧ Visited (graph := graph) remaining next)
    {start : Label graph.locals b × α} {result : Fin b × α}
    (run : Silmaril.Elgot.Part.Runs (graph.step model.val) start result)
    (inside : Visited (graph := graph) remaining start.1)
    (shaped : ∃ packet : Fin (profile.width start.1) → α, start.2 = encode model.val packet) : False := by
  induction run with
  | @done start result returned =>
    rcases start with ⟨index | port, packet⟩
    · simp [Graph.step, Part.mem_map_iff] at returned
    · exact inside
  | @more start next result advanced _ ih =>
    rcases start with ⟨index | port, packet⟩
    · obtain ⟨fields, eq⟩ := shaped
      change (Fin (profile.localWidth index) → α) at fields
      change packet = encode model.val fields at eq
      obtain ⟨target, route, checked, visited⟩ := closed index inside
      rw [eq, private_step (profile := profile) model (i := index) fields checked] at advanced
      have same : next = (target, encode model.val (fields ∘ route)) := by simpa using advanced
      subst next
      exact ih visited ⟨fields ∘ route, rfl⟩
    · exact inside

private theorem predict_precompose {source middle locals : Nat} (model : Model F Part α)
    (packet : Fin source → α) (route : Route source middle) (outcome : Outcome middle locals outputs) :
    (outcome.precompose route).predict model packet = outcome.predict model (packet ∘ route) := by
  cases outcome <;> rfl

private theorem inspect_sound (model : PairModel F Part α) (remaining : Finset (Fin graph.locals))
    (start : Label graph.locals b) (links : LinksBack profile remaining start) (packet : Fin (profile.width start) → α)
    (result : Part (Fin b × α))
    (found : (inspect profile remaining start).predict model.val packet = some result) :
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
        cases checked : next? profile i with
        | none => simp [checked, Outcome.predict] at found
        | some edge =>
          obtain ⟨next, route⟩ := edge
          change (Fin (profile.localWidth i) → α) at packet
          simp only [checked] at found
          have predicted := (predict_precompose model.val packet route
            (inspect profile (remaining.erase i) next)).symm.trans found
          have advanced := congrArg (fun action => action >>= Sum.elim pure (iter (graph.step model.val)))
            (private_step (profile := profile) model (i := i) packet checked)
          rw [← Part.pure_eq_some, pure_bind] at advanced
          exact (congrFun (LawfulElgotMonad.fixpoint (graph.step model.val)) (.inl i, encode model.val packet)).trans
            (advanced.trans (ih (remaining.erase i) (Finset.erase_ssubset fresh) next (advance links checked)
              (packet ∘ route) predicted))
      · have same : Part.none = result := by simpa [dite_eq_right fresh, Outcome.predict] using found
        have closed : ∀ j, j ∉ remaining → ∃ (next : Label graph.locals b) (fields : Route (profile.localWidth j) (profile.width next)),
            next? profile j = some ⟨next, fields⟩ ∧ Visited (graph := graph) remaining next := by
          intro j absent
          obtain ⟨next, fields, checked, rfl | known⟩ := links j absent
          · exact ⟨.inl i, fields, checked, fresh⟩
          · exact ⟨next, fields, checked, known⟩
        rw [← same]
        refine Part.eq_none_iff.mpr fun value member => ?_
        exact no_run model closed ((Silmaril.Elgot.Part.mem_iter_iff _ _ value).mp member) fresh ⟨packet, rfl⟩

private theorem encode_cast (model : Model F Part α) {source target : Nat} (equal : source = target)
    (packet : Fin target → α) : encode model (packet ∘ Fin.cast equal) = encode model packet := by
  cases equal
  rfl

theorem entry_sound (model : PairModel F Part α) (profile : Profile graph inputs outputs)
    (input : Fin a) (packet : Fin (inputs input) → α) (result : Part (Fin b × α))
    (found : (entryOutcome profile input).predict model.val packet = some result) :
    graph.denote model.val (input, encode model.val packet) = result := by
  have predicted := (predict_precompose model.val packet (Fin.cast (profile.entryWidth input))
    (inspect profile Finset.univ (graph.entry input))).symm.trans found
  unfold Graph.denote
  rw [← encode_cast model.val (profile.entryWidth input) packet]
  exact inspect_sound model Finset.univ (graph.entry input)
    (fun _ absent => (absent (Finset.mem_univ _)).elim) _ result predicted

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width
