module

public import Silmaril.Logic.Temporal.CTLStar.Thms

@[expose] public section
namespace Silmaril.Logic.Temporal.CTLStar.Examples

abbrev sig : Signature := ⟨Unit⟩

def terminalModel : Model sig := ⟨⟨Unit, fun _ _ => False, fun _ _ => True, ()⟩⟩

def terminalPath : Path terminalModel.toModal.accessible :=
  ⟨fun _ => (), some 0, fun _ h => by simp only [ValidIndex] at h; omega,
    fun _ _ _ => id⟩

/-- Strong next fails at an actual terminal state, including under A. -/
theorem terminal_not_exists_next :
    ¬ (StateFormula.existsPath (.next .top)).Holds terminalModel () := by
  rintro ⟨p, _, hp⟩
  exact p.edges 0 hp.1

theorem terminal_not_all_strong_next_bottom :
    ¬ (StateFormula.allPaths (.next (.state .bot))).Holds terminalModel () := by
  intro h
  exact h ⟨terminalPath, rfl, fun hp => hp.2⟩

/-- The old weak AX has a different, deliberately vacuous terminal meaning. -/
theorem terminal_weak_ax_bottom : (CTL.Formula.ax .bot).Holds terminalModel () := by
  exact fun ⟨_, hr, _⟩ => hr

/-- On a finite singleton path, GF can hold without infinitely many positions. -/
theorem terminal_globally_eventually_atom :
    Sat terminalModel (.existsPath (.globally (.eventually (.state (.atom ()))))) := by
  refine ⟨terminalPath, rfl, (PathFormula.globally_iff terminalModel _ terminalPath 0).mpr ?_⟩
  intro n hn
  exact ⟨0, hn, trivial, fun _ hi => (Nat.not_lt_zero _ hi).elim⟩

/-- A maximal finite path can satisfy G top; old CTL EG top cannot. -/
theorem terminal_exists_globally_top :
    (StateFormula.existsPath (.globally .top)).Holds terminalModel () := by
  refine ⟨terminalPath, rfl, ?_⟩
  rintro ⟨_, _, h, _⟩
  exact h not_false

theorem terminal_not_ctl_eg_top : ¬ (CTL.Formula.eg .top).Holds terminalModel () := by
  rintro ⟨p, _, hr, _⟩
  exact hr 0

/-- A nonterminating spine offers one write at each point, then a non-writing sink. -/
inductive LoopState
  | spine : Nat → LoopState
  | write : LoopState
  | sink : LoopState

inductive LoopEdge : LoopState → LoopState → Prop
  | advance (n) : LoopEdge (.spine n) (.spine (n+1))
  | exit (n) : LoopEdge (.spine n) .write
  | finish : LoopEdge .write .sink
  | idle : LoopEdge .sink .sink

theorem LoopEdge.from_write {v : LoopState} (h : LoopEdge .write v) : v = .sink := by
  cases h
  rfl

theorem LoopEdge.from_sink {v : LoopState} (h : LoopEdge .sink v) : v = .sink := by
  cases h
  rfl

def loopModel : Model sig :=
  ⟨⟨LoopState, LoopEdge, fun _ w => w = .write, .spine 0⟩⟩

theorem loop_serial (w : LoopState) : ∃ v, LoopEdge w v := by
  cases w with
  | spine n => exact ⟨_, .advance n⟩
  | write => exact ⟨_, .finish⟩
  | sink => exact ⟨_, .idle⟩

/-- Re-quantifying at each spine state offers a write, on different paths. -/
theorem loop_ctl_eg_ef_write :
    (CTL.Formula.eg (.ef (.atom ()))).Holds loopModel (.spine 0) := by
  refine ⟨LoopState.spine, rfl, LoopEdge.advance, ?_⟩
  intro n
  exact .next not_false (.exit n) (.now rfl)

/-- One path cannot write infinitely often: taking any write exit commits to the sink. -/
theorem loop_not_exists_globally_eventually_write :
    ¬ (StateFormula.existsPath (.globally (.eventually (.state (.atom ()))))).Holds
      loopModel (.spine 0) := by
  rintro ⟨path, _, hg⟩
  have hn : path.last = none := path.last_none_of_serial loop_serial
  have allvalid (i : Nat) : path.Valid i := by simp only [Path.Valid, ValidIndex, hn]
  have hall : ∀ n, path.Valid (0+n) →
      (PathFormula.eventually (.state (.atom ()))).Holds loopModel path (0+n) :=
    (PathFormula.globally_iff loopModel _ path 0).mp hg
  obtain ⟨d, _, hwrite, _⟩ := hall 0 (allvalid 0)
  have hw : path.state d = .write := by simpa only [Nat.zero_add, PathFormula.Holds,
    StateFormula.Holds, loopModel] using hwrite
  have hfirst : path.state (d+1) = .sink := by
    have he : LoopEdge .write (path.state (d+1)) := by
      simpa only [loopModel, hw] using path.edges d (allvalid (d+1))
    exact LoopEdge.from_write he
  have hsink (k : Nat) : path.state (d+1+k) = .sink := by
    induction k with
    | zero => exact hfirst
    | succ k ih =>
      have he : LoopEdge .sink (path.state (d+1+k+1)) := by
        simpa only [loopModel, ih] using path.edges (d+1+k) (allvalid (d+1+k+1))
      exact LoopEdge.from_sink he
  obtain ⟨j, _, hj, _⟩ := hall (d+1) (allvalid (0+(d+1)))
  have htarget : path.state (d+1+j) = .write := by
    simpa only [Nat.zero_add, PathFormula.Holds, StateFormula.Holds, loopModel] using hj
  exact LoopState.noConfusion ((hsink j).symm.trans htarget)

/-- Same spine witness, with genuine state re-quantification embedded in a path formula. -/
theorem loop_exists_globally_exists_eventually_write :
    (StateFormula.existsPath (.globally (.state
      (.existsPath (.eventually (.state (.atom ()))))))).Holds loopModel (.spine 0) := by
  obtain ⟨path, h0, hg, _⟩ := (encodeCTL_holds loopModel _ (.spine 0)).mpr loop_ctl_eg_ef_write
  exact ⟨path, h0, hg⟩

/-- An actual nonserial chain reaches a terminal labelled target. -/
def chain : Model sig :=
  ⟨⟨Bool, fun w v => w = false ∧ v = true, fun _ w => w = true, false⟩⟩

theorem chain_next_target : Sat chain (.existsPath (.next (.state (.atom ())))) :=
  (encodeCTL_holds chain (.ex (.atom ())) false).mpr ⟨true, ⟨rfl, rfl⟩, rfl⟩

theorem chain_eventually_target : Sat chain (.existsPath (.eventually (.state (.atom ())))) :=
  (encodeCTL_holds chain (.ef (.atom ())) false).mpr
    (.next not_false ⟨rfl, rfl⟩ (.now rfl))

/-- A positive full path-temporal property, witnessed by an actual infinite path. -/
def writing : Model sig := ⟨⟨Unit, fun _ _ => True, fun _ _ => True, ()⟩⟩

theorem writing_globally_eventually :
    Sat writing (.existsPath (.globally (.eventually (.state (.atom ()))))) := by
  let path : Path writing.toModal.accessible :=
    ⟨fun _ => (), none, fun _ _ => trivial, fun _ h => by cases h⟩
  refine ⟨path, rfl, (PathFormula.globally_iff writing _ path 0).mpr ?_⟩
  intro n _
  exact ⟨0, trivial, trivial, fun _ h => (Nat.not_lt_zero _ h).elim⟩

/-- The chosen point is fixed while two other states are exchanged. -/
def permutationModel : Model sig :=
  ⟨⟨Option Bool, fun _ _ => True, fun _ _ => True, none⟩⟩

def swapStates : Option Bool ≃ Option Bool where
  toFun := Option.map Bool.not
  invFun := Option.map Bool.not
  left_inv w := by cases w with | none => rfl | some b => cases b <;> rfl
  right_inv w := by cases w with | none => rfl | some b => cases b <;> rfl

def permutationFrameIso : FrameIso permutationModel permutationModel :=
  ⟨swapStates, rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

open CategoryTheory in
def permutationArrow : (show RichModel sig from ⟨permutationModel.toModal⟩) ⟶
    (show RichModel sig from ⟨permutationModel.toModal⟩) :=
  ⟨permutationFrameIso.toModalIso⟩

theorem permutation_moves_state :
    permutationArrow.iso.hom.map (some false) = some true := rfl

open CategoryTheory in
theorem permutation_not_identity : permutationArrow ≠ 𝟙 _ := by
  intro h
  have he := congrArg (fun f => f.iso.hom.map (some false)) h
  cases he

theorem permutation_preserves_full_satisfaction (p : StateFormula sig) :
    Sat permutationModel p ↔ Sat permutationModel p := rich_hom_sat permutationArrow p

end Silmaril.Logic.Temporal.CTLStar.Examples
