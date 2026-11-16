module

public import Silmaril.Logic.Kore.FixedPoint.Semantics.Thms

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Kore.FixedPoint.Examples

def origin (index : Nat) : Modules.Origin := ⟨"Positive", index⟩
def seedSymbol : Modules.NamedSymbol := ⟨origin 2, ⟨"seed", [], "S"⟩⟩
def stepSymbol : Modules.NamedSymbol := ⟨origin 3, ⟨"step", ["S"], "S"⟩⟩
def liftSymbol : Modules.NamedSymbol := ⟨origin 4, ⟨"lift", ["S"], "T"⟩⟩
def pairSymbol : Modules.NamedSymbol := ⟨origin 5, ⟨"pair", ["S", "S"], "S"⟩⟩
def scope : Modules.Scope :=
  ⟨[(origin 0, "S"), (origin 1, "T")], [seedSymbol, stepSymbol, liftSymbol, pairSymbol], []⟩

def seedOp : scope.signature.operations 0 (fun i => seedSymbol.declaration.arguments.get i) "S" :=
  ⟨seedSymbol, by simp [scope], rfl, rfl⟩
def stepOp : scope.signature.operations 1 (fun i => stepSymbol.declaration.arguments.get i) "S" :=
  ⟨stepSymbol, by simp [scope], rfl, rfl⟩

def seed {sets objects : Names} : Pattern scope sets objects "S" :=
  .app seedOp (fun i => i.elim0)
def step {sets objects : Names} (p : Pattern scope sets objects "S") :
    Pattern scope sets objects "S" := .app stepOp (Fin.cases p (fun i => i.elim0))

def reaches : Pattern scope [] [] "S" :=
  .mu (P' := context [("@X", "S")])
    (.disj (seed (sets := [("@X", "S")]) (objects := []))
      (step (sets := [("@X", "S")]) (objects := []) (.setvar 0)))
def forever : Pattern scope [] [] "S" :=
  .nu (P' := context [("@X", "S")])
    (step (sets := [("@X", "S")]) (objects := []) (.setvar 0))
def reachText : String := "\\mu{}(@X:S{},\\or{S{}}(seed{}(),step{}(@X:S{})))"
def foreverText : String := "\\nu{}(@X:S{},step{}(@X:S{}))"

/-- These equalities exercise the actual lexer, parser, symbol lookup, sorted
checker and binder resolution, not a supplied compiled-pattern oracle. -/
theorem read_reaches : Checking.read scope 20 [] [] "S" reachText = some reaches := by rfl
theorem read_forever : Checking.read scope 20 [] [] "S" foreverText = some forever := by rfl

abbrev naturalModel : Matching.FixedPoint.Model scope.signature where
  carrier _ := Nat
  nonempty _ := ⟨0⟩
  operation op values :=
    if op.val = seedSymbol then {0} else {result | ∃ i, result = values i + 1}

/-- The successor operation really advances the supplied argument; no
reachability predicate is installed as an extra operation. -/
theorem natural_seed {sets objects : Names}
    (v : ∀ i, naturalModel.carrier (context objects i))
    (η : ∀ i, Set (naturalModel.carrier (context sets i))) :
    (seed : Pattern scope sets objects "S").denote naturalModel v η = {0} := by
  ext x
  simp [seed, Matching.FixedPoint.Pattern.denote, Matching.FixedPoint.application, naturalModel, seedOp]

theorem natural_step {sets objects : Names} (p : Pattern scope sets objects "S")
    (v : ∀ i, naturalModel.carrier (context objects i))
    (η : ∀ i, Set (naturalModel.carrier (context sets i))) :
    (step p).denote naturalModel v η = {result | ∃ n ∈ p.denote naturalModel v η, result = n + 1} := by
  ext x
  simp only [step, Matching.FixedPoint.Pattern.denote, Matching.FixedPoint.application, naturalModel, stepOp]
  simp only [show stepSymbol ≠ seedSymbol by decide, ↓reduceIte]
  simp only [Fin.forall_fin_one, Fin.exists_fin_one, Fin.cases_zero]
  constructor
  · rintro ⟨values, hv, hx⟩
    exact ⟨values 0, hv, hx⟩
  · rintro ⟨n, hn, hx⟩
    exact ⟨fun _ => n, hn, hx⟩

/-- A real infinite successor chain: every natural is in the least closed set
containing zero. This is proved by induction, rather than finite unfolding. -/
theorem reaches_all : reaches.denote naturalModel (fun i => i.elim0) (fun i => i.elim0) = Set.univ := by
  change (sInf {X : Set Nat |
    ((seed (sets := [("@X", "S")]) (objects := [])).denote naturalModel (fun i => i.elim0) (@Fin.cases 0 (fun _ => Set Nat) X (fun i => i.elim0)) ∪
      (step (sets := [("@X", "S")]) (objects := []) (.setvar 0)).denote naturalModel (fun i => i.elim0) (@Fin.cases 0 (fun _ => Set Nat) X (fun i => i.elim0))) ⊆ X}) = _
  rw [Set.eq_univ_iff_forall]
  intro n
  apply Set.mem_sInter.mpr
  intro X hX
  induction n with
  | zero => exact hX (Or.inl (by rw [natural_seed]; rfl))
  | succ n ih =>
      apply hX
      right
      rw [natural_step]
      exact ⟨n, ih, rfl⟩

/-- The same signature supports a graph with a self-loop at true and no edge
from false. The greatest invariant keeps exactly the loop state. -/
abbrev loopModel : Matching.FixedPoint.Model scope.signature where
  carrier _ := Bool
  nonempty _ := ⟨false⟩
  operation op values :=
    if op.val = seedSymbol then ∅ else {result | result = true ∧ ∃ i, values i = true}

theorem loop_step {sets objects : Names} (p : Pattern scope sets objects "S")
    (v : ∀ i, loopModel.carrier (context objects i))
    (η : ∀ i, Set (loopModel.carrier (context sets i))) :
    (step p).denote loopModel v η = {result | result = true ∧ true ∈ p.denote loopModel v η} := by
  ext x
  simp only [step, Matching.FixedPoint.Pattern.denote, Matching.FixedPoint.application, loopModel, stepOp]
  simp only [show stepSymbol ≠ seedSymbol by decide, ↓reduceIte]
  simp only [Fin.forall_fin_one, Fin.exists_fin_one, Fin.cases_zero]
  constructor
  · rintro ⟨values, hv, hx, hi⟩
    rw [hi] at hv
    exact ⟨hx, hv⟩
  · rintro ⟨hx, hp⟩
    exact ⟨fun _ => true, hp, hx, rfl⟩

theorem forever_loop_only :
    forever.denote loopModel (fun i => i.elim0) (fun i => i.elim0) = {true} := by
  change (sSup {X : Set Bool |
    X ⊆ (step (sets := [("@X", "S")]) (objects := []) (.setvar 0)).denote loopModel (fun i => i.elim0) (@Fin.cases 0 (fun _ => Set Bool) X (fun i => i.elim0))}) = _
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨X, hX, hx⟩ := Set.mem_sUnion.mp hx
    have target := hX hx
    rw [loop_step] at target
    exact target.1
  · intro x hx
    apply Set.mem_sUnion.mpr
    refine ⟨{true}, ?_, hx⟩
    intro y hy
    rw [loop_step]
    exact ⟨hy, rfl⟩
theorem source_reaches_all :
    Semantics.read scope naturalModel 20 [] [] "S" reachText = some Set.univ := by
  have meaning := Semantics.read_sound naturalModel 20 [] [] "S" reachText reaches
    (fun i => i.elim0) (fun i => i.elim0) read_reaches
  simp only [Semantics.interpret] at meaning
  exact meaning.trans (congrArg some reaches_all)

theorem source_forever_loop_only :
    Semantics.read scope loopModel 20 [] [] "S" foreverText = some {true} := by
  have meaning := Semantics.read_sound loopModel 20 [] [] "S" foreverText forever
    (fun i => i.elim0) (fun i => i.elim0) read_forever
  simp only [Semantics.interpret] at meaning
  exact meaning.trans (congrArg some forever_loop_only)

/-- The inner set binder shadows the outer one, so this is mu of a constant
universe, rather than mu X.X. -/
def shadow : Pattern scope [] [] "S" :=
  .mu (P' := context [("@X", "S")])
    (.nu (P' := context [("@X", "S"), ("@X", "S")]) (.setvar 0))
theorem read_shadow : Checking.read scope 20 [] [] "S"
    "\\mu{}(@X:S{},\\nu{}(@X:S{},@X:S{}))" = some shadow := by rfl

theorem identity_least (M : Matching.FixedPoint.Model scope.signature) :
    (Matching.FixedPoint.Pattern.mu (P' := context [("@X", "S")]) (.setvar 0) : Pattern scope [] [] "S").denote
      M (fun i => i.elim0) (fun i => i.elim0) = ∅ := by
  change sInf {X : Set (M.carrier "S") | X ⊆ X} = ∅
  exact le_antisymm (sInf_le (show (∅ : Set (M.carrier "S")) ⊆ ∅ from le_rfl)) bot_le

theorem identity_greatest (M : Matching.FixedPoint.Model scope.signature) :
    (Matching.FixedPoint.Pattern.nu (P' := context [("@X", "S")]) (.setvar 0) : Pattern scope [] [] "S").denote
      M (fun i => i.elim0) (fun i => i.elim0) = Set.univ := by
  change sSup {X : Set (M.carrier "S") | X ⊆ X} = Set.univ
  exact le_antisymm le_top (le_sSup (show (Set.univ : Set (M.carrier "S")) ⊆ Set.univ from le_rfl))

theorem shadow_universe (M : Matching.FixedPoint.Model scope.signature) :
    shadow.denote M (fun i => i.elim0) (fun i => i.elim0) = Set.univ := by
  change sInf {X : Set (M.carrier "S") | sSup {Y : Set (M.carrier "S") | Y ⊆ Y} ⊆ X} = Set.univ
  have greatest : sSup {Y : Set (M.carrier "S") | Y ⊆ Y} = Set.univ :=
    le_antisymm le_top (le_sSup (show (Set.univ : Set (M.carrier "S")) ⊆ Set.univ from le_rfl))
  rw [greatest]
  exact le_antisymm le_top (le_sInf fun X hX => hX)
theorem source_shadow_universe (M : Matching.FixedPoint.Model scope.signature) :
    Semantics.read scope M 20 [] [] "S"
      "\\mu{}(@X:S{},\\nu{}(@X:S{},@X:S{}))" = some Set.univ := by
  have meaning := Semantics.read_sound M 20 [] [] "S" _ shadow
    (fun i => i.elim0) (fun i => i.elim0) read_shadow
  simp only [Semantics.interpret] at meaning
  exact meaning.trans (congrArg some (shadow_universe M))

theorem read_identity_least : Checking.read scope 20 [] [] "S" "\\mu{}(@X:S{},@X:S{})" =
    some (Matching.FixedPoint.Pattern.mu (P' := context [("@X", "S")]) (.setvar 0)) := by rfl

theorem read_identity_greatest : Checking.read scope 20 [] [] "S" "\\nu{}(@X:S{},@X:S{})" =
    some (Matching.FixedPoint.Pattern.nu (P' := context [("@X", "S")]) (.setvar 0)) := by rfl
end Silmaril.Logic.Kore.FixedPoint.Examples
