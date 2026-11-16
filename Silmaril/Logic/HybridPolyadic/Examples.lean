module

public import Silmaril.Logic.HybridPolyadic.Modal.Thms
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Fin

/-! # Named CFG states, genuine ternary accessibility and scoped binders

Worlds 0,1,2 form entry→middle→exit; world 3 is unreachable. The binary
modal action `fork` denotes a genuine ternary relation (current,left,right).
-/

@[expose] public section
namespace Silmaril.Logic.HybridPolyadic.Examples
open CategoryTheory Silmaril.Logic.Institution

inductive Name where
  | entry | exit
  deriving DecidableEq

inductive Action : ℕ → Type
  | step : Action 1
  | jump : Action 1
  | fork : Action 2
  | halt : Action 0
  deriving DecidableEq

abbrev signature : Signature := ⟨Unit, Name, Action⟩

abbrev cfg : Model signature where
  World := Fin 4
  relation
    | _, Action.step, w, vs => (w = 0 ∧ vs 0 = 1) ∨ (w = 1 ∧ vs 0 = 2)
    | _, Action.jump, w, vs => w = 0 ∧ vs 0 = 2
    | _, Action.fork, w, vs => w = 0 ∧ vs 0 = 1 ∧ vs 1 = 2
    | _, Action.halt, w, _ => w = 2
  valuation _ w := w = 2
  name | Name.entry => 0 | Name.exit => 2
  point := 0

def twoEdges : Formula signature 0 :=
  .atNom Name.entry ((Formula.nominal Name.exit).unaryDia Action.step |>.unaryDia Action.step)

/-- Named entry reaches named exit in exactly the exhibited two steps. -/
theorem entry_two_edges_exit : Sat cfg twoEdges := by
  exact ⟨fun _ => 1, Or.inl ⟨rfl, rfl⟩, fun _ =>
    ⟨fun _ => 2, Or.inr ⟨rfl, rfl⟩, fun _ => rfl⟩⟩

theorem entry_not_exit : ¬ Sat cfg (.atNom Name.entry (.nominal Name.exit)) := by
  change (0 : Fin 4) ≠ 2
  decide

theorem no_direct_step : ¬ Sat cfg (.atNom Name.entry ((Formula.nominal Name.exit).unaryDia Action.step)) := by
  rintro ⟨vs, hv, hs⟩
  have he : vs 0 = 2 := hs 0
  rcases hv with ⟨hw, hs⟩ | ⟨hw, hs⟩
  · have bad := hs.symm.trans he
    cases bad
  · cases hw

theorem no_return : ¬ Sat cfg (.atNom Name.exit ((Formula.nominal Name.entry).unaryDia Action.step)) := by
  rintro ⟨vs, hv, _⟩
  rcases hv with ⟨hw, _⟩ | ⟨hw, _⟩ <;> cases hw

/-- The extra arbitrary world has no incoming step from any world. -/
theorem unreachable : ∀ w, ¬ cfg.relation 1 Action.step w (fun _ => (3 : Fin 4)) := by
  intro w hv
  rcases hv with ⟨_, hv⟩ | ⟨_, hv⟩ <;> cases hv

/-- Arity two checks two coordinates in one actual relation tuple. -/
theorem genuine_polyadic : Sat cfg (.dia Action.fork ![Formula.top, .nominal Name.exit]) := by
  refine ⟨![1, 2], ⟨rfl, rfl, rfl⟩, ?_⟩
  intro i
  fin_cases i
  · exact id
  · rfl

theorem swapped_coordinate_rejected : ¬ Sat cfg (.dia Action.fork ![.nominal Name.exit, Formula.top]) := by
  rintro ⟨vs, hv, hs⟩
  have he : vs 0 = 2 := hs 0
  have hn : vs 0 = 1 := hv.2.1
  have bad := hn.symm.trans he
  cases bad

/-- Nullary modalities assert their actual unary-on-current-world relation. -/
theorem nullary_at_exit : Sat cfg (.atNom Name.exit (.dia Action.halt Fin.elim0)) := by
  exact ⟨Fin.elim0, rfl, fun i => Fin.elim0 i⟩

/-- An inner binder shadows index zero; the saved outer state is index one. -/
theorem binder_shadow : Sat cfg (.down ((Formula.down (.state 0)).unaryDia Action.step)) := by
  exact ⟨fun _ => 1, Or.inl ⟨rfl, rfl⟩, fun _ => rfl⟩

theorem binder_outer_distinct : ¬ Sat cfg (.down ((Formula.down (.state 1)).unaryDia Action.step)) := by
  rintro ⟨vs, hv, hs⟩
  have he : vs 0 = 0 := hs 0
  rcases hv with ⟨hw, hs⟩ | ⟨hw, hs⟩
  · have bad := hs.symm.trans he
    cases bad
  · cases hw

theorem saved_entry_at : Sat cfg
    (.down ((Formula.down (.atState 1 (.nominal Name.entry))).unaryDia Action.step)) := by
  exact ⟨fun _ => 1, Or.inl ⟨rfl, rfl⟩, fun _ => rfl⟩

theorem shadowed_entry_at_false : ¬ Sat cfg
    (.down ((Formula.down (.atState 0 (.nominal Name.entry))).unaryDia Action.step)) := by
  rintro ⟨vs, hv, hs⟩
  have he : vs 0 = 0 := hs 0
  rcases hv with ⟨hw, hs⟩ | ⟨hw, hs⟩
  · have bad := hs.symm.trans he
    cases bad
  · cases hw

/-- Scope extension lifts the old free index past the new bound zero. -/
theorem rename_avoids_capture :
    ((Formula.down (.state 1) : Formula signature 1).rename (fun _ : Fin 1 => (1 : Fin 2))) =
      .down (.state 2) := rfl

theorem rename_preserves_bound :
    ((Formula.down (.state 0) : Formula signature 1).rename (fun _ : Fin 1 => (1 : Fin 2))) =
      .down (.state 0) := rfl

theorem renamed_outer_state :
    (((Formula.down (.state 1) : Formula signature 1).rename (fun _ : Fin 1 => (1 : Fin 2)))
      ).Holds cfg ![2, 0] 0 := by
  rfl

theorem captured_outer_state_false :
    ¬ (Formula.down (.state 1) : Formula signature 2).Holds cfg ![2, 0] 0 := by
  change (0 : Fin 4) ≠ 2
  decide

/-- Signature arrows intentionally permit nominal aliases. -/
def aliasNames : signature ⟶ signature :=
  ⟨id, fun _ => Name.exit, fun _ => id⟩

theorem names_alias_target : Sat cfg ((Formula.atNom Name.entry (.nominal Name.exit)).map aliasNames) := by
  rfl

theorem names_alias_reduct : Sat ((reduct aliasNames).obj cfg) (.atNom Name.entry (.nominal Name.exit)) :=
  (Formula.holds_map aliasNames cfg _ Fin.elim0 cfg.point).mp names_alias_target

/-- Action aliases respect the explicit index; a unary jump may become a unary step. -/
def aliasActions : signature ⟶ signature :=
  ⟨id, id, fun _ a => match a with | Action.jump => Action.step | Action.step => Action.step | Action.fork => Action.fork | Action.halt => Action.halt⟩

theorem jump_reaches_exit : Sat cfg ((Formula.nominal Name.exit).unaryDia Action.jump) := by
  exact ⟨fun _ => 2, ⟨rfl, rfl⟩, fun _ => rfl⟩

theorem action_alias_changes_truth :
    ¬ Sat cfg (((Formula.nominal Name.exit).unaryDia Action.jump).map aliasActions) := by
  exact no_direct_step

theorem action_alias_reduct :
    ¬ Sat ((reduct aliasActions).obj cfg) ((Formula.nominal Name.exit).unaryDia Action.jump) :=
  fun h => action_alias_changes_truth ((Formula.holds_map aliasActions cfg _ Fin.elim0 cfg.point).mpr h)

/-- The three reachable worlds form a proper generated submodel. -/
abbrev reachableCfg : Model signature where
  World := Fin 3
  relation k a w vs := cfg.relation k a w.castSucc (Fin.castSucc ∘ vs)
  valuation a w := cfg.valuation a w.castSucc
  name | Name.entry => 0 | Name.exit => 2
  point := 0

private theorem unary_lift (a : Fin 3) (vs : Fin 1 → Fin 4)
    (h : a.castSucc = vs 0) : Fin.castSucc ∘ (fun _ : Fin 1 => a) = vs := by
  funext i
  rw [Fin.eq_zero i]
  exact h

private theorem binary_lift (vs : Fin 2 → Fin 4) (h0 : vs 0 = 1) (h1 : vs 1 = 2) :
    Fin.castSucc ∘ (![1, 2] : Fin 2 → Fin 3) = vs := by
  funext i
  fin_cases i
  · exact h0.symm
  · exact h1.symm

/-- A genuine non-surjective model arrow: unreachable world 3 need not be in its image. -/
def reachableInclusion : reachableCfg ⟶ cfg where
  map := Fin.castSucc
  injective := Fin.castSucc_injective 3
  point := rfl
  atoms := fun _ _ => Iff.rfl
  names := by intro a; cases a <;> rfl
  forth := fun _ _ _ _ h => h
  back := by
    intro k a w vs hv
    cases a with
    | step =>
      rcases hv with ⟨hw, hs⟩ | ⟨hw, hs⟩
      · exact ⟨fun _ => 1, Or.inl ⟨hw, rfl⟩, unary_lift 1 vs hs.symm⟩
      · exact ⟨fun _ => 2, Or.inr ⟨hw, rfl⟩, unary_lift 2 vs hs.symm⟩
    | jump => exact ⟨fun _ => 2, ⟨hv.1, rfl⟩, unary_lift 2 vs hv.2.symm⟩
    | fork => exact ⟨![1, 2], ⟨hv.1, rfl, rfl⟩, binary_lift vs hv.2.1 hv.2.2⟩
    | halt => exact ⟨Fin.elim0, hv, funext (fun i => Fin.elim0 i)⟩

theorem inclusion_not_surjective : ¬ Function.Surjective reachableInclusion.map := by
  intro h
  obtain ⟨w, hw⟩ := h 3
  have heq := congrArg Fin.val hw
  have hlt := w.isLt
  change w.val = 3 at heq
  omega

theorem generated_submodel_two_edges : Sat reachableCfg twoEdges :=
  (sat_hom reachableInclusion twoEdges).mpr entry_two_edges_exit

/-- The K fixture has the same two-edge CFG; its actual encoded target is checked. -/
abbrev kCfg : Modal.Model ⟨Unit⟩ where
  World := Fin 4
  accessible w v := (w = 0 ∧ v = 1) ∨ (w = 1 ∧ v = 2)
  valuation _ w := w = 2
  point := 0

def kTwoEdges : Modal.Formula ⟨Unit⟩ := .box (.box (.atom ()))

theorem k_two_edges : Modal.Sat kCfg kTwoEdges := by
  intro v hv w hw
  change w = 2
  rcases hv with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;>
    rcases hw with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> omega

theorem checked_K_target : Sat (expandModal kCfg) (encodeModal kTwoEdges) := by
  apply (encodeModal_holds (expandModal kCfg) kTwoEdges Fin.elim0 kCfg.point).mpr
  change Modal.Sat ((modalReduct _).obj (expandModal kCfg)) kTwoEdges
  rw [modalReduct_expand]
  exact k_two_edges

/-- A closed binder can detect the collapse of two distinct accessible worlds. -/
abbrev collapseSource : Model (modalSignatures.obj ⟨Unit⟩) where
  World := Bool
  relation _ _ _ _ := True
  valuation _ _ := True
  name := Empty.elim
  point := false

abbrev collapseTarget : Model (modalSignatures.obj ⟨Unit⟩) where
  World := Unit
  relation _ _ _ _ := True
  valuation _ _ := True
  name := Empty.elim
  point := ()

def distinctSuccessor : Formula (modalSignatures.obj ⟨Unit⟩) 0 :=
  .down ((Formula.state 0).neg.unaryDia modalAction)

theorem distinct_successor_source : Sat collapseSource distinctSuccessor := by
  refine ⟨fun _ => true, True.intro, ?_⟩
  intro i heq
  cases heq

theorem distinct_successor_target_false : ¬ Sat collapseTarget distinctSuccessor := by
  rintro ⟨vs, _, hs⟩
  exact hs 0 (Subsingleton.elim _ _)

/-- Ordinary K permits this noninjective bounded map; the hybrid arrow policy excludes it. -/
def kCollapse : (modalReduct ⟨Unit⟩).obj collapseSource ⟶
    (modalReduct ⟨Unit⟩).obj collapseTarget where
  map _ := ()
  point := rfl
  atoms := fun _ _ => Iff.rfl
  forth := fun _ _ _ => True.intro
  back := by
    intro w v _
    cases v
    exact ⟨w, True.intro, rfl⟩

theorem collapse_not_injective : ¬ Function.Injective kCollapse.map := by
  intro h
  exact Bool.false_ne_true (h (a₁ := false) (a₂ := true) rfl)

/-- Empty world carriers are impossible because every model has an actual point. -/
theorem carrier_nonempty {S : Signature} (M : Model S) : Nonempty M.World := ⟨M.point⟩

end Silmaril.Logic.HybridPolyadic.Examples

/-- info: 'Silmaril.Logic.HybridPolyadic.Formula.holds_rename' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.HybridPolyadic.Formula.holds_rename
/-- info: 'Silmaril.Logic.HybridPolyadic.Formula.holds_map' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.HybridPolyadic.Formula.holds_map
/-- info: 'Silmaril.Logic.HybridPolyadic.Formula.holds_hom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.HybridPolyadic.Formula.holds_hom
/-- info: 'Silmaril.Logic.HybridPolyadic.modalToHybridPolyadic_modelExpansive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.HybridPolyadic.modalToHybridPolyadic_modelExpansive
/-- info: 'Silmaril.Logic.HybridPolyadic.Examples.entry_two_edges_exit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.HybridPolyadic.Examples.entry_two_edges_exit
/-- info: 'Silmaril.Logic.HybridPolyadic.Examples.genuine_polyadic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.HybridPolyadic.Examples.genuine_polyadic
/-- info: 'Silmaril.Logic.HybridPolyadic.Examples.binder_outer_distinct' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.HybridPolyadic.Examples.binder_outer_distinct
/-- info: 'Silmaril.Logic.HybridPolyadic.Examples.inclusion_not_surjective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.HybridPolyadic.Examples.inclusion_not_surjective
/-- info: 'Silmaril.Logic.HybridPolyadic.Examples.checked_K_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Logic.HybridPolyadic.Examples.checked_K_target
