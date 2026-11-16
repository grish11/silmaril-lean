module

public import Silmaril.Logic.Hoare.Rules

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Hoare.Examples

def signature : Signature Unit := ⟨⟨Bool, Unit⟩, fun _ => .action ()⟩

abbrev toggle : Model Unit signature :=
  ⟨Bool, (fun _ w v => v = !w), (fun a => {w | w = a}), false⟩

def good : Triple Unit signature := ⟨(), .atom false, .atom true⟩
def bad : Triple Unit signature := ⟨(), .atom false, .atom false⟩

theorem toggle_valid : good.Satisfies Unit toggle := by
  intro w hw v hv
  change w = false at hw
  change v = !w at hv
  exact hv.trans (congrArg Bool.not hw)

theorem toggle_invalid : ¬ bad.Satisfies Unit toggle := by
  intro h
  exact Bool.noConfusion (h false rfl true rfl)

/-- Repeated command reachability even allows zero steps and cannot replace command completion. -/
theorem wrong_unphased_reachability : Reachability.Reaches (toggle.step ()) (fun w => w = false) false :=
  .now rfl

theorem toggle_canonical_valid : Reachability.Sentence.Satisfies () (expand Unit toggle) (encode Unit good) :=
  (encode_correct _ _).mpr toggle_valid

theorem toggle_canonical_invalid : ¬ Reachability.Sentence.Satisfies () (expand Unit toggle) (encode Unit bad) :=
  fun h => toggle_invalid ((encode_correct _ _).mp h)

abbrev noResult : Model Unit signature :=
  ⟨Bool, (fun _ _ _ => False), (fun _ => Set.univ), false⟩

def falsePost : Triple Unit signature := ⟨(), .neg .bot, .bot⟩

/-- Ordinary relational partial correctness ignores absence of completed results. -/
theorem noResult_partial : falsePost.Satisfies Unit noResult := fun _ _ _ hr => hr

theorem noResult_not_total : ¬ ∃ v, (signature.body ()).Rel noResult false v := fun ⟨_, h⟩ => h

theorem noResult_not_safe : ¬ ∃ v, noResult.step () false v := fun ⟨_, h⟩ => h

/-- The canonical loop records missing results; it does not prove a source execution diverges. -/
theorem canonical_missing_result_loop :
    CTL.Globally (phaseStep Unit noResult) (fun _ => True) (some (), false, false) :=
  ⟨(fun _ => (some (), false, false)), rfl,
    (fun _ => ⟨(), rfl, rfl, rfl, Or.inr ⟨rfl, fun ⟨_, h⟩ => h⟩⟩), fun _ => trivial⟩

theorem source_missing_result_no_steps : ¬ CTL.Globally (noResult.step ()) (fun _ => True) false :=
  CTL.not_globally_of_deadlock _ _ _ (fun _ h => h)

theorem missing_result_canonical_partial : Reachability.Sentence.Satisfies ()
    (expand Unit noResult) (encode Unit falsePost) := (encode_correct _ _).mpr noResult_partial

/-- Actual composition is checked independently of the phase compiler. -/
theorem twice_toggle : Valid toggle (.atom false) (.seq (.action ()) (.action ())) (.atom false) := by
  rintro w hw v ⟨u, hu, hv⟩
  change w = false at hw
  change u = !w at hu
  change v = !u at hv
  exact hv.trans ((congrArg Bool.not hu).trans (by rw [hw]; rfl))

/-- The canonical model restriction is essential: arbitrary entry/exit interpretations can fail. -/
abbrev arbitraryTarget := Reachability.relationalModel (fun _ _ : Unit => False)
  (fun a : Label Unit signature => if a.2.1 then ∅ else Set.univ)

theorem arbitrary_target_rejects_valid_triple : ¬ Reachability.Sentence.Satisfies () arbitraryTarget
    (encode Unit good) := by
  intro h
  have hall := (Reachability.atomRule_iff _ _ _ _ _).mp h () trivial
  obtain ⟨_, _, hfalse⟩ := hall 0 (fun _ => ()) rfl
    (fun _ hi => (Nat.not_lt_zero _ hi).elim) (fun _ h => h)
  exact hfalse

/-- The restriction map really is not model-expansive: canonical carriers have distinct phases. -/
theorem restriction_not_modelExpansive : ¬ (restrictReachability Unit).ModelExpansive := by
  intro h
  have hex := h signature arbitraryTarget
  change ∃ M : Model Unit signature, expand Unit M = arbitraryTarget at hex
  obtain ⟨M, he⟩ := hex
  have hs : Subsingleton ((expand Unit M).carrier ()) := by
    rw [he]
    change Subsingleton Unit
    infer_instance
  have hp : (none, false, M.point) = (none, true, M.point) :=
    @Subsingleton.elim ((expand Unit M).carrier ()) hs (none, false, M.point) (none, true, M.point)
  exact Bool.noConfusion (congrArg (fun x : Phase Unit M.World => x.2.1) hp)

/-- info: 'Silmaril.Logic.Hoare.encode_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms encode_correct
/-- info: 'Silmaril.Logic.Hoare.entails_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms entails_iff

end Silmaril.Logic.Hoare.Examples
