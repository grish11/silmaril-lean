module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Defs
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Block
import Mathlib.Data.Finset.Card

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean

open Silmaril.Elgot
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width (Profile)

variable {V F α : Type} [DecidableEq V] {a b n : Nat}
  {graph : Graph V F a b} {inputs : Fin a → Nat} {outputs : Fin b → Nat}
  {profile : Profile graph inputs outputs} {advance : Advance profile}

theorem key_injective {L : Type} {width : L → Nat} : Function.Injective (At.key (width := width)) := by
  rintro ⟨left, packet⟩ ⟨right, packet'⟩ equal
  have same : left = right := congrArg Prod.fst equal
  subst right
  have fields := List.map_inj_left.mp (congrArg Prod.snd equal)
  exact congrArg (Sigma.mk left) (funext fun i => fields i (List.mem_finRange i))

theorem mem_packets (packet : Packet n) : packet ∈ packets n := by
  induction n with
  | zero =>
    have equal : packet = Fin.elim0 := funext fun i => Fin.elim0 i
    simp [packets, equal]
  | succ n ih =>
    refine List.mem_flatMap.mpr ⟨Fin.tail packet, ih (Fin.tail packet), ?_⟩
    have equal := Fin.cons_self_tail packet
    cases head : packet 0
    · exact List.mem_cons.mpr (Or.inl (by simpa only [head] using equal.symm))
    · exact List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr (by simpa only [head] using equal.symm)))

private theorem mem_privateKeys (profile : Profile graph inputs outputs) (state : At profile.localWidth) :
    state.key ∈ privateKeys profile := by
  obtain ⟨label, packet⟩ := state
  apply List.mem_toFinset.mpr
  exact List.mem_flatMap.mpr ⟨label, List.mem_finRange label, List.mem_map.mpr ⟨packet, mem_packets packet, rfl⟩⟩

private def inside (profile : Profile graph inputs outputs) (state : At profile.localWidth) : At profile.width :=
  ⟨.inl state.1, state.2⟩

private def Seen (profile : Profile graph inputs outputs) (remaining : Finset (Fin graph.locals × List Bool)) :
    At profile.width → Prop
  | ⟨.inl label, packet⟩ => At.key (⟨label, packet⟩ : At profile.localWidth) ∉ remaining
  | ⟨.inr _, _⟩ => False

/-- Every visited state has a checked edge to another visited state or to
the state being inspected. -/
private def LinksBack (profile : Profile graph inputs outputs) (advance : Advance profile) (remaining : Finset (Fin graph.locals × List Bool))
    (current : At profile.width) : Prop :=
  ∀ state : At profile.localWidth, state.key ∉ remaining → ∃ next, advance state = .next next ∧ (next = current ∨ Seen profile remaining next)

private theorem visit {remaining : Finset (Fin graph.locals × List Bool)}
    {current : At profile.localWidth} {next : At profile.width}
    (links : LinksBack profile advance remaining (inside profile current)) (edge : advance current = .next next) :
    LinksBack profile advance (remaining.erase current.key) next := by
  intro state absent
  by_cases same : state.key = current.key
  · cases key_injective same
    exact ⟨next, edge, Or.inl rfl⟩
  · obtain ⟨target, checked, location⟩ := links state
      (fun member => absent (Finset.mem_erase.mpr ⟨same, member⟩))
    refine ⟨target, checked, Or.inr ?_⟩
    rcases location with rfl | visited
    · cases current
      exact fun member => (Finset.mem_erase.mp member).1 rfl
    · rcases target with ⟨index | port, packet⟩
      · exact fun member => visited (Finset.mem_erase.mp member).2
      · exact visited

private theorem no_run (model : BooleanModel F α) (sound : StepSound model profile advance) {remaining : Finset (Fin graph.locals × List Bool)}
    (closed : ∀ state : At profile.localWidth, state.key ∉ remaining → ∃ next, advance state = .next next ∧ Seen profile remaining next)
    {start : Label graph.locals b × α} {result : Fin b × α}
    (run : Silmaril.Elgot.Part.Runs (graph.step model.pairModel.val) start result)
    (visited : ∃ state : At profile.localWidth, state.key ∉ remaining ∧ start = (inside profile state).render model) :
    False := by
  induction run with
  | @done start result returned =>
    obtain ⟨state, _, same⟩ := visited
    rw [same] at returned
    simp [inside, At.render, Graph.step, Part.mem_map_iff] at returned
  | @more start next result advanced _ ih =>
    obtain ⟨state, seen, same⟩ := visited
    obtain ⟨target, checked, targetSeen⟩ := closed state seen
    rw [same] at advanced
    change Sum.inr next ∈ graph.step model.pairModel.val (.inl state.1, encodePacket model state.2) at advanced
    have step := sound state (Part.some (.inr (At.render model target))) (by rw [checked]; rfl)
    rw [step] at advanced
    have equal : next = target.render model := by simpa using advanced
    rcases target with ⟨index | port, packet⟩
    · exact ih ⟨⟨index, packet⟩, targetSeen, equal⟩
    · exact targetSeen

private theorem inspect_sound (model : BooleanModel F α) (profile : Profile graph inputs outputs)
    (advance : Advance profile) (sound : StepSound model profile advance)
    (remaining : Finset (Fin graph.locals × List Bool)) (start : At profile.width)
    (links : LinksBack profile advance remaining start) (result : Part (Fin b × α))
    (found : (inspectWith profile advance remaining start).predict model = some result) :
    iter (graph.step model.pairModel.val) (start.render model) = result := by
  induction remaining using Finset.strongInductionOn generalizing start with
  | _ remaining ih =>
    rw [inspectWith.eq_def] at found
    rcases start with ⟨index | port, packet⟩
    · by_cases fresh : At.key (⟨index, packet⟩ : At profile.localWidth) ∈ remaining
      · simp only [dite_eq_left fresh] at found
        cases checked : advance ⟨index, packet⟩ with
        | unsupported => simp [checked, Outcome.predict] at found
        | undefined =>
          have same : Part.none = result := by simpa [checked, Outcome.predict] using found
          let step := graph.step model.pairModel.val
          have halted := sound ⟨index, packet⟩ Part.none (by rw [checked]; rfl)
          have stopped := congrArg (fun action => action >>= Sum.elim pure (iter step)) halted
          change _ = Part.none.bind _ at stopped
          rw [Part.bind_none] at stopped
          exact (congrFun (LawfulElgotMonad.fixpoint step) (.inl index, encodePacket model packet)).trans
            (stopped.trans same)
        | next next =>
          have predicted : (inspectWith profile advance (remaining.erase (At.key (⟨index, packet⟩ : At profile.localWidth))) next).predict model = some result := by
            simpa [checked] using found
          let step := graph.step model.pairModel.val
          have advanced := congrArg (fun action => action >>= Sum.elim pure (iter step))
            (sound ⟨index, packet⟩ (Part.some (.inr (At.render model next))) (by rw [checked]; rfl))
          rw [← Part.pure_eq_some, pure_bind] at advanced
          simp only [Sum.elim_inr] at advanced
          exact (congrFun (LawfulElgotMonad.fixpoint step) (.inl index, encodePacket model packet)).trans
            (advanced.trans (ih _ (Finset.erase_ssubset fresh) next (visit links checked) predicted))
      · have same : Part.none = result := by simpa [dite_eq_right fresh, Outcome.predict] using found
        have closed : ∀ s : At profile.localWidth, s.key ∉ remaining → ∃ next, advance s = .next next ∧ Seen profile remaining next := by
          intro s absent
          obtain ⟨next, checked, rfl | known⟩ := links s absent
          · exact ⟨_, checked, fresh⟩
          · exact ⟨next, checked, known⟩
        rw [← same]
        refine Part.eq_none_iff.mpr fun value member => ?_
        exact no_run model sound closed ((Silmaril.Elgot.Part.mem_iter_iff _ _ value).mp member)
          ⟨⟨index, packet⟩, fresh, rfl⟩
    · have same : Part.some (At.render model (⟨port, packet⟩ : At outputs)) = result := Option.some.inj found
      rw [← same, congrFun (LawfulElgotMonad.fixpoint _) _]
      simp [At.render, Graph.step]

private theorem encode_cast (model : BooleanModel F α) {source target : Nat} (equal : source = target)
    (packet : Packet target) : encodePacket model (packet ∘ Fin.cast equal) = encodePacket model packet := by
  cases equal
  rfl

theorem entry_with_sound (model : BooleanModel F α) (profile : Profile graph inputs outputs)
    (advance : Advance profile) (sound : StepSound model profile advance)
    (input : Fin a) (packet : Packet (inputs input)) (result : Part (Fin b × α))
    (found : (entryOutcomeWith profile advance input packet).predict model = some result) :
    graph.denote model.pairModel.val (input, encodePacket model packet) = result := by
  have performed := inspect_sound model profile advance sound (privateKeys profile) (entryState profile input packet)
    (fun state absent => (absent (mem_privateKeys profile state)).elim) result found
  simpa only [Graph.denote, At.render, entryState, encode_cast] using performed

theorem entry_sound (model : BooleanModel F α) (profile : Profile graph inputs outputs)
    (input : Fin a) (packet : Packet (inputs input)) (result : Part (Fin b × α))
    (found : (entryOutcome profile input packet).predict model = some result) :
    graph.denote model.pairModel.val (input, encodePacket model packet) = result :=
  entry_with_sound model profile (pureAdvance profile) (pure_sound model profile) input packet result found

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean
