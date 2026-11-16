module

public import Silmaril.Logic.Kore.FixedPoint.Modules.Thms

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace Silmaril.Logic.Kore.FixedPoint.ModuleExamples
open CategoryTheory

def source : String := "[]
module BASE
  sort S{} []
  symbol seed{}():S{} []
  symbol step{}(S{}):S{} []
  axiom{} \\mu{}(@X:S{},\\or{S{}}(seed{}(),step{}(@X:S{}))) []
endmodule []
module USE
  import BASE []
  claim{} \\mu{}(@X:S{},@X:S{}) []
endmodule []"

theorem checked_source : (Modules.checkText 32 source).isSome = true := by decide +kernel

def checked : Modules.CheckedDefinition := (Modules.checkText 32 source).get checked_source
def base : Modules.CheckedModule checked.ambient := checked.modules.get ⟨0, by decide +kernel⟩
def useModule : Modules.CheckedModule checked.ambient := checked.modules.get ⟨1, by decide +kernel⟩

def seedSymbol : Kore.Modules.NamedSymbol := ⟨⟨"BASE", 1⟩, ⟨"seed", [], "S"⟩⟩
def stepSymbol : Kore.Modules.NamedSymbol := ⟨⟨"BASE", 2⟩, ⟨"step", ["S"], "S"⟩⟩

def seedOp : checked.ambient.signature.operations 0 (fun i => seedSymbol.declaration.arguments.get i) "S" :=
  ⟨seedSymbol, by decide +kernel, rfl, rfl⟩
def stepOp : checked.ambient.signature.operations 1 (fun i => stepSymbol.declaration.arguments.get i) "S" :=
  ⟨stepSymbol, by decide +kernel, rfl, rfl⟩

def seed {sets objects : Names} : Pattern checked.ambient sets objects "S" :=
  .app seedOp (fun i => i.elim0)
def step {sets objects : Names} (p : Pattern checked.ambient sets objects "S") :
    Pattern checked.ambient sets objects "S" := .app stepOp (Fin.cases p (fun i => i.elim0))

def reaches : Pattern checked.ambient [] [] "S" :=
  .mu (P' := context [("@X", "S")])
    (.disj (seed (sets := [("@X", "S")]) (objects := []))
      (step (sets := [("@X", "S")]) (objects := []) (.setvar 0)))
def reachText : String := "\\mu{}(@X:S{},\\or{S{}}(seed{}(),step{}(@X:S{})))"

/-- These equalities exercise the actual lexer, parser, symbol lookup, sorted
checker and binder resolution, not a supplied compiled-pattern oracle. -/
theorem read_reaches : Checking.read checked.ambient 20 [] [] "S" reachText = some reaches := by rfl

abbrev naturalModel : Matching.FixedPoint.Model checked.ambient.signature where
  carrier _ := Nat
  nonempty _ := ⟨0⟩
  operation op values :=
    if op.val = seedSymbol then {0} else {result | ∃ i, result = values i + 1}

/-- The successor operation really advances the supplied argument; no
reachability predicate is installed as an extra operation. -/
theorem natural_seed {sets objects : Names}
    (v : ∀ i, naturalModel.carrier (context objects i))
    (η : ∀ i, Set (naturalModel.carrier (context sets i))) :
    (seed : Pattern checked.ambient sets objects "S").denote naturalModel v η = {0} := by
  ext x
  simp [seed, Matching.FixedPoint.Pattern.denote, Matching.FixedPoint.application, naturalModel, seedOp]

theorem natural_step {sets objects : Names} (p : Pattern checked.ambient sets objects "S")
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


def reachSentence : Sentence checked.ambient.signature :=
  (base.localAxioms.get ⟨0, by decide +kernel⟩).sentence

def falseClaim : Sentence checked.ambient.signature :=
  (useModule.claims.get ⟨0, by decide +kernel⟩).sentence

theorem native_reach : reachSentence.lower =
    ⟨0, 0, context [], context [], "S", reaches⟩ := by
  change reachSentence.source.lower.map (𝟙 _) = _
  rw [Matching.FixedPoint.Sentence.map_id]
  rfl

theorem reach_true : reachSentence.Satisfies naturalModel := by
  apply (Sentence.satisfies_lower naturalModel reachSentence).mpr
  rw [native_reach]
  intro v η x
  have hv : v = (fun i => i.elim0) := funext fun i => i.elim0
  have hη : η = (fun i => i.elim0) := funext fun i => i.elim0
  subst v; subst η
  exact Set.eq_univ_iff_forall.mp reaches_all x

theorem false_claim_false : ¬ falseClaim.Satisfies naturalModel := by
  intro h
  have hp := (Sentence.satisfies_lower naturalModel falseClaim).mp h
    (fun i => i.elim0) (fun i => i.elim0) 0
  change 0 ∈ sInf {X : Set Nat | X ⊆ X} at hp
  have bottom : (sInf {X : Set Nat | X ⊆ X}) ⊆ (∅ : Set Nat) :=
    sInf_le (show (∅ : Set Nat) ⊆ ∅ from le_rfl)
  exact bottom hp

/-- The false claim does not prevent the axiom presentation having a model. -/
theorem model_satisfies_importer :
    ∀ p ∈ useModule.axiomSet, Sentence.Satisfies naturalModel p := by
  rintro p ⟨d, hd, rfl⟩
  change d ∈ [_] at hd
  simp only [List.mem_singleton] at hd
  subst d
  exact reach_true

theorem false_claim_unproved : ¬ useModule.Proves falseClaim := by
  intro h
  exact false_claim_false (h naturalModel model_satisfies_importer)

theorem claims_separate : useModule.localAxioms.length = 0 ∧
    useModule.claims.length = 1 ∧ useModule.axioms.length = 1 := by decide +kernel

theorem imported_origin :
    (useModule.axioms.map Kore.Modules.Checking.CheckedSentence.origin) = [⟨"BASE", 3⟩] :=
  by decide +kernel

theorem imported_parent : base.asImport ∈ useModule.imports := by
  change base.asImport ∈ [base.asImport]
  exact List.mem_singleton_self _

noncomputable def actualImport :=
  Kore.Modules.Checking.CheckedModule.importHom base useModule imported_parent

noncomputable def actualNativeImport := Modules.nativeImportHom base useModule imported_parent

end Silmaril.Logic.Kore.FixedPoint.ModuleExamples
