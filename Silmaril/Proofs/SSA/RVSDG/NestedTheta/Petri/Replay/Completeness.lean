module

public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Replay.Defs

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Petri.Replay.Proofs

open RVSDG.Petri (Tokens)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

theorem successors_complete (m : Model.{u, v, w} Op) {term : Term Op args past sigs outs}
    {entry : Tuple m.Val args} {tokens : Tokens m.Val past} {before after : Marking m term}
    (step : Fire m term entry tokens before after) :
    ∃ move ∈ successors m term entry tokens before, move.val = after := by
  induction step with
  | primitive ready ran =>
    refine ⟨⟨_, .primitive ready ran⟩, ?_, rfl⟩
    simp only [successors]
    split
    · rename_i none
      cases ready.symm.trans none
    · rename_i packet fetched
      cases Option.some.inj (ready.symm.trans fetched)
      apply List.mem_append_left
      split
      · rename_i none
        cases ran.symm.trans none
      · rename_i output computed
        cases Option.some.inj (ran.symm.trans computed)
        exact List.mem_cons_self
  | enter ready picked =>
    refine ⟨⟨_, .enter ready picked⟩, ?_, rfl⟩
    simp only [successors]
    split
    · rename_i none
      cases ready.symm.trans none
    · rename_i packet fetched
      cases Option.some.inj (ready.symm.trans fetched)
      apply List.mem_append_left
      apply List.mem_append_right
      split
      · rename_i none
        cases picked.symm.trans none
      · rename_i arm received entered
        have eq := Option.some.inj (picked.symm.trans entered)
        cases eq
        exact List.mem_singleton.mpr rfl
  | advance step ih =>
    obtain ⟨move, mem, eq⟩ := ih
    cases eq
    refine ⟨⟨_, .advance step⟩, ?_, rfl⟩
    simp only [successors, List.mem_append]
    exact .inl (.inl (List.mem_map.mpr ⟨move, mem, rfl⟩))
  | commit ready picked =>
    refine ⟨⟨_, .commit ready picked⟩, ?_, rfl⟩
    simp only [successors]
    apply List.mem_append_left
    apply List.mem_append_right
    split
    · rename_i none
      cases ready.symm.trans none
    · rename_i packet fetched
      cases Option.some.inj (ready.symm.trans fetched)
      split
      · rename_i output sent
        cases Sum.inl.inj (picked.symm.trans sent)
        exact List.mem_singleton.mpr rfl
      · rename_i feedback sent
        cases picked.symm.trans sent
  | restart ready picked next =>
    refine ⟨⟨_, .restart ready picked next⟩, ?_, rfl⟩
    simp only [successors]
    apply List.mem_append_left
    apply List.mem_append_right
    split
    · rename_i none
      cases ready.symm.trans none
    · rename_i packet fetched
      cases Option.some.inj (ready.symm.trans fetched)
      split
      · rename_i output sent
        cases picked.symm.trans sent
      · rename_i feedback sent
        cases Sum.inr.inj (picked.symm.trans sent)
        split
        · rename_i none
          cases next.symm.trans none
        · rename_i selected bank received
          cases Option.some.inj (next.symm.trans received)
          simp
  | @later _ _ _ _ _ node children rest entry tokens vertex before after step ih =>
    obtain ⟨move, mem, eq⟩ := ih
    cases eq
    refine ⟨⟨_, .later step⟩, ?_, rfl⟩
    have lifted : ⟨_, .later step⟩ ∈ (successors m rest entry (tokens.snoc vertex.outputs) before).map
      (fun candidate => (⟨(vertex, candidate.val), Fire.later candidate.property⟩ :
        {mark : Marking m (.bind node children rest) //
          Fire m (.bind node children rest) entry tokens (vertex, before) mark})) :=
      List.mem_map.mpr ⟨move, mem, rfl⟩
    cases vertex with
    | pending =>
      simp only [successors]
      split
      · exact lifted
      · exact List.mem_append_right _ lifted
    | waiting arm child =>
      cases child
      simp only [successors]
      exact List.mem_append_right _ lifted
    | done _ => exact lifted

theorem checkFire_complete (m : Model.{u, v, w} Op) (colourEq : (t : PortType V S) → DecidableEq (m.Val t))
    {term : Term Op args past sigs outs} {entry : Tuple m.Val args} {tokens : Tokens m.Val past}
    {before after : Marking m term} (step : Fire m term entry tokens before after) :
    (checkFire m colourEq term entry tokens before after).isSome := by
  obtain ⟨move, mem, same⟩ := successors_complete m step
  unfold checkFire
  rw [Option.isSome_iff_ne_none, Ne, List.findSome?_eq_none_iff]
  intro absent
  simpa [same] using absent move mem

end Silmaril.SSA.RVSDG.NestedTheta.Petri.Replay.Proofs
