module

public import Silmaril.Logic.CTL

@[expose] public section
namespace Silmaril.Logic.CTL.Examples

abbrev signature : Signature := ⟨Unit⟩

/-- The target is terminal: EU needs only the finite prefix reaching it. -/
def chain : Model signature := ⟨{
  World := Bool
  accessible := fun w v => w = false ∧ v = true
  valuation := fun _ w => w = true
  point := false }⟩

theorem chain_next : Sat chain (.ex (.atom ())) := ⟨true, ⟨rfl, rfl⟩, rfl⟩
theorem chain_until : Sat chain (.eu .top (.atom ())) :=
  .next (fun h => h) ⟨rfl, rfl⟩ (.now rfl)

theorem chain_wrong_guard : ¬ Sat chain (.eu (.atom ()) (.atom ())) := by
  intro h
  cases h with
  | now hq => exact Bool.noConfusion hq
  | next hp _ _ => exact Bool.noConfusion hp

theorem chain_no_infinite_path : ¬ Sat chain (.eg .top) := by
  rintro ⟨path, h0, hr, _⟩
  have h1 : path 1 = true := (hr 0).2
  have h2 : path 1 = false := (hr 1).1
  exact Bool.noConfusion (h1.symm.trans h2)

/-- Universal until succeeds along the finite maximal chain ending at its target. -/
theorem chain_all_until : Sat chain (.au .top (.atom ())) := by
  apply (Formula.au_iff_all_paths chain .top (.atom ()) false).mpr
  constructor
  · intro path h0 hr
    exact (chain_no_infinite_path ⟨path, h0, hr, fun _ h => h⟩).elim
  · intro n path h0 hr hd
    cases n with
    | zero => exact (hd true ⟨h0, rfl⟩).elim
    | succ n => exact ⟨1, Nat.succ_le_succ (Nat.zero_le n), (hr 0 (by omega)).2, fun _ _ h => h⟩

/-- Every successor differs from its predecessor, so this is a genuine cycle. -/
def cycle : Model signature := ⟨{
  World := Bool
  accessible := fun w v => v = !w
  valuation := fun _ _ => False
  point := false }⟩

def alternating : Nat → Bool
  | 0 => false
  | n+1 => !(alternating n)

theorem cycle_infinite : Sat cycle (.eg .top) :=
  ⟨alternating, rfl, fun _ => rfl, fun _ h => h⟩

theorem cycle_nonreach : ¬ Sat cycle (.ef (.atom ())) :=
  Until.not_of_no_target (fun _ h => h)

/-- A genuine infinite path avoiding the target refutes universal until. -/
theorem cycle_not_all_until : ¬ Sat cycle (.au .top (.atom ())) := by
  intro h
  obtain ⟨n, hn, _⟩ := ((Formula.au_iff_all_paths cycle .top (.atom ()) false).mp h).1
    alternating rfl (fun _ => rfl)
  exact hn

def labelledCycle : Model signature := ⟨{
  World := Bool
  accessible := fun w v => v = !w
  valuation := fun _ w => w = true
  point := false }⟩

/-- EG(EF target) nests ν around μ; capture-safe translation preserves this witness. -/
theorem nested_temporal : Sat labelledCycle (.eg (.ef (.atom ()))) := by
  refine ⟨alternating, rfl, fun _ => rfl, ?_⟩
  intro n
  cases h : alternating n with
  | false => exact .next (fun h => h) rfl (.now rfl)
  | true => exact .now rfl

/-- Deadlock is not silently completed with a self-loop. -/
def dead : Model signature := ⟨{
  World := Bool
  accessible := fun _ _ => False
  valuation := fun _ w => w = true
  point := false }⟩

theorem dead_no_next : ¬ Sat dead (.ex .top) := fun ⟨_, h, _⟩ => h
theorem dead_no_infinite : ¬ Sat dead (.eg .top) := not_globally_of_deadlock _ _ false (fun _ h => h)
theorem dead_nonreach : ¬ Sat dead (.ef (.atom ())) := by
  intro h
  cases h with
  | now hq => exact Bool.noConfusion hq
  | next _ hr _ => exact hr

theorem dead_weak_box : Sat dead (.ax .bot) := fun ⟨_, h, _⟩ => h

theorem dead_k_box : Sat dead (encodeK (.box .bot)) := dead_weak_box

theorem dead_strong_af_false : ¬ Sat dead (.af (.atom ())) :=
  fun h => Bool.noConfusion ((Formula.af_deadlock dead (.atom ()) false (fun _ h => h)).mp h)

/-- The infinite-only serial dual is true here, which is why strong AF has a terminal clause. -/
theorem dead_infinite_only_dual : Sat dead (.neg (.eg (.neg (.atom ())))) :=
  not_globally_of_deadlock _ _ false (fun _ h => h)

theorem dead_until_now : Sat dead (.eu .bot .top) := .now (fun h => h)

/-- Arbitrary carriers include infinite chains, not just finite model-checking fixtures. -/
abbrev naturalChain : Model ⟨Nat⟩ := ⟨{
  World := Nat
  accessible := fun w v => v = w+1
  valuation := fun a w => w = a
  point := 0 }⟩

theorem natural_eventual (n : Nat) : Sat naturalChain (.ef (.atom n)) := by
  apply (until_iff_finite_prefix _ _ _ 0).mpr
  exact ⟨n, id, rfl, rfl, fun _ _ => ⟨(fun h => h), rfl⟩⟩

theorem natural_infinite : Sat naturalChain (.eg .top) :=
  ⟨id, rfl, fun _ => rfl, fun _ h => h⟩

theorem translated_nested_temporal : ModalMu.Sat (expandMu labelledCycle)
    (Formula.eg (.ef (.atom ()))).toMu := by
  apply ((Formula.eg (.ef (.atom ()))).toMu_correct (expandMu labelledCycle) false).mpr
  change Sat labelledCycle (.eg (.ef (.atom ())))
  exact nested_temporal

/-- info: 'Silmaril.Logic.CTL.finite_prefix_maximal_extension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms finite_prefix_maximal_extension
/-- info: 'Silmaril.Logic.CTL.Formula.au_iff_all_paths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Formula.au_iff_all_paths
/-- info: 'Silmaril.Logic.CTL.globally_iff_gfp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms globally_iff_gfp
/-- info: 'Silmaril.Logic.CTL.Formula.toMu_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Formula.toMu_correct
/-- info: 'Silmaril.Logic.CTL.k_entails_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms k_entails_iff
/-- info: 'Silmaril.Logic.CTL.mu_entails_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mu_entails_iff

end Silmaril.Logic.CTL.Examples
