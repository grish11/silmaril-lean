module

public import Silmaril.Logic.Hoare.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Hoare
open CategoryTheory Silmaril.Logic.Institution
variable {C : Type} {A : Signature C}

theorem phase_exit_terminal (M : Model C A) (c : C) (w : M.World) :
    ∀ y, ¬ phaseStep C M (some c, true, w) y := by
  rintro y ⟨_, _, he, _⟩
  exact Bool.noConfusion he

theorem phase_entry_successor (M : Model C A) (c : C) (w : M.World) :
    ∃ y, phaseStep C M (some c, false, w) y := by
  classical
  by_cases h : ∃ v, (A.body c).Rel M w v
  · obtain ⟨v, hv⟩ := h
    exact ⟨(some c, true, v), c, rfl, rfl, rfl, Or.inl ⟨rfl, hv⟩⟩
  · exact ⟨(some c, false, w), c, rfl, rfl, rfl, Or.inr ⟨rfl, h⟩⟩

def exitTarget (M : Model C A) (c : C) (q : PDL.Formula A.language) (x : Phase C M.World) : Prop :=
  x.1 = some c ∧ x.2.1 = true ∧ q.Holds M x.2.2

theorem phase_bad_iff (M : Model C A) (c : C) (q : PDL.Formula A.language) (w : M.World) :
    CTL.Until (phaseStep C M) (fun x => ¬ exitTarget M c q x)
      (fun x => (∀ y, ¬ phaseStep C M x y) ∧ ¬ exitTarget M c q x) (some c, false, w) ↔
      ∃ v, (A.body c).Rel M w v ∧ ¬ q.Holds M v := by
  classical
  constructor
  · show CTL.Until _ _ _ (some c, false, w) → _
    intro hu
    generalize hx : (some c, false, w) = x at hu
    induction hu with
    | now hb =>
        obtain ⟨y, hy⟩ := phase_entry_successor M c w
        exact (hb.1 y (hx ▸ hy)).elim
    | @next x y _ hr hu ih =>
        show ∃ v, (A.body c).Rel M w v ∧ ¬ q.Holds M v
        have hs : phaseStep C M (some c, false, w) y := hx.symm ▸ hr
        obtain ⟨d, hd, _, hycmd, hbranch⟩ := hs
        have hdc : d = c := (Option.some.inj hd).symm
        rcases hbranch with ⟨hyphase, hrun⟩ | ⟨hy, _⟩
        · show ∃ v, (A.body c).Rel M w v ∧ ¬ q.Holds M v
          have hterm : ∀ z, ¬ phaseStep C M y z := by
            rintro z ⟨_, _, hz, _⟩
            exact Bool.noConfusion (hyphase.symm.trans hz)
          have hb := (CTL.until_deadlock_iff _ _ _ y hterm).mp hu
          refine ⟨y.2.2, hdc ▸ hrun, ?_⟩
          intro hq
          exact hb.2 ⟨hycmd.trans (congrArg some hdc), hyphase, hq⟩
        · exact ih hy.symm
  · show (∃ v, (A.body c).Rel M w v ∧ ¬ q.Holds M v) → _
    rintro ⟨v, hr, hq⟩
    exact .next (fun h => Bool.noConfusion h.2.1)
      ⟨c, rfl, rfl, rfl, Or.inl ⟨rfl, hr⟩⟩
      (.now ⟨phase_exit_terminal M c v, fun h => hq h.2.2⟩)

theorem phase_allPartial_iff (M : Model C A) (c : C) (q : PDL.Formula A.language) (w : M.World) :
    Reachability.AllPartial (phaseStep C M) (exitTarget M c q) (some c, false, w) ↔
      ∀ v, (A.body c).Rel M w v → q.Holds M v := by
  classical
  rw [Reachability.allPartial_iff_no_bad, phase_bad_iff]
  simp only [not_exists, not_and, not_not]

theorem encode_correct (M : Model C A) (t : Triple C A) :
    Reachability.Sentence.Satisfies () (expand C M) (encode C t) ↔ t.Satisfies C M := by
  let _ : Nonempty (Phase C M.World) := ⟨(none, false, M.point)⟩
  unfold expand encode
  rw [Reachability.atomRule_iff]
  constructor
  · intro h w hp
    exact (phase_allPartial_iff M t.command t.post w).mp
      (h (some t.command, false, w) ⟨rfl, rfl, hp⟩)
  · intro h x ⟨hc, hb, hp⟩
    have hx : x = (some t.command, false, x.2.2) := by
      rcases x with ⟨a,b,w⟩
      exact Prod.ext hc (Prod.ext hb rfl)
    exact hx.symm ▸ (phase_allPartial_iff M t.command t.post x.2.2).mpr (h x.2.2 hp)

end Silmaril.Logic.Hoare
