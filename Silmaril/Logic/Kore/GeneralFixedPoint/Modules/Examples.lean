module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Modules.Thms

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace Silmaril.Logic.Kore.GeneralFixedPoint.ModuleExamples
open CategoryTheory

def source : String := "[]
module BASE
  sort S{} []
  symbol seed{}():S{} []
  symbol step{}(S{}):S{} []
  axiom{} \\mu{}(@X:S{},\\or{S{}}(seed{}(),\\not{S{}}(\\not{S{}}(step{}(@X:S{}))))) []
endmodule []
module USE
  import BASE []
  axiom{} \\or{S{}}(@Y:S{},\\not{S{}}(@Y:S{})) []
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

def body : Pattern checked.ambient [("@X", "S")] [] "S" :=
  (seed (sets := [("@X", "S")]) (objects := [])).disj
    (.neg (.neg (step (sets := [("@X", "S")]) (objects := []) (.setvar 0))))

def reaches : Pattern checked.ambient [] [] "S" := .mu body

abbrev naturalModel : Matching.GeneralFixedPoint.Model checked.ambient.signature where
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
  simp [seed, Matching.GeneralFixedPoint.Pattern.denote, Matching.FixedPoint.application, naturalModel, seedOp]

theorem natural_step {sets objects : Names} (p : Pattern checked.ambient sets objects "S")
    (v : ∀ i, naturalModel.carrier (context objects i))
    (η : ∀ i, Set (naturalModel.carrier (context sets i))) :
    (step p).denote naturalModel v η = {result | ∃ n ∈ p.denote naturalModel v η, result = n + 1} := by
  ext x
  simp only [step, Matching.GeneralFixedPoint.Pattern.denote, Matching.FixedPoint.application, naturalModel, stepOp]
  simp only [show stepSymbol ≠ seedSymbol by decide, ↓reduceIte]
  simp only [Fin.forall_fin_one, Fin.exists_fin_one, Fin.cases_zero]
  constructor
  · rintro ⟨values, hv, hx⟩
    exact ⟨values 0, hv, hx⟩
  · rintro ⟨n, hn, hx⟩
    exact ⟨fun _ => n, hn, hx⟩

theorem body_formula (X : Set Nat) :
    body.denote naturalModel (fun i => i.elim0) (Fin.cases X (fun i => i.elim0)) =
      (seed (sets := [("@X", "S")]) (objects := [])).denote naturalModel (fun i => i.elim0)
        (Fin.cases X (fun i => i.elim0)) ∪
      (step (sets := [("@X", "S")]) (objects := []) (.setvar 0)).denote naturalModel
        (fun i => i.elim0) (Fin.cases X (fun i => i.elim0)) := by
  let a : Set Nat := (seed (sets := [("@X", "S")]) (objects := [])).denote naturalModel
    (fun i => i.elim0) (Fin.cases X (fun i => i.elim0))
  let b : Set Nat := (step (sets := [("@X", "S")]) (objects := []) (.setvar 0)).denote
    naturalModel (fun i => i.elim0) (Fin.cases X (fun i => i.elim0))
  change (aᶜ ∩ (bᶜᶜ)ᶜ)ᶜ = a ∪ b
  simp only [compl_compl, ← Set.compl_union]

/-- Local positivity admits double negation; induction still establishes the
actual infinite successor closure rather than a finite unfolding. -/
theorem reaches_all : reaches.denote naturalModel (fun i => i.elim0) (fun i => i.elim0) = Set.univ := by
  change sInf {X : Set Nat | body.denote naturalModel (fun i => i.elim0)
    (Fin.cases X (fun i => i.elim0)) ⊆ X} = _
  rw [Set.eq_univ_iff_forall]
  intro n
  apply Set.mem_sInter.mpr
  intro X hX
  change body.denote naturalModel (fun i => i.elim0)
    (Fin.cases X (fun i => i.elim0)) ⊆ X at hX
  rw [body_formula X] at hX
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
    ⟨0, 0, context [], context [], "S", reaches, by decide +kernel⟩ := by
  change reachSentence.source.lower.map (𝟙 _) = _
  rw [Matching.GeneralFixedPoint.Sentence.map_id]
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

def excludedMiddle : Sentence checked.ambient.signature :=
  (useModule.localAxioms.get ⟨0, by decide +kernel⟩).sentence

theorem excluded_middle_true : excludedMiddle.Satisfies naturalModel := by
  apply (Sentence.satisfies_lower naturalModel excludedMiddle).mpr
  change ∀ (_ : Fin 0 → Nat) (η : Fin 1 → Set Nat) (x : Nat),
    x ∈ ((η 0)ᶜ ∩ ((η 0)ᶜ)ᶜ)ᶜ
  intro v η x
  simp

/-- Both mixed-polarity free set variables and an actual fixed-point axiom are
satisfied; the deliberately false claim remains excluded. -/
theorem model_satisfies_importer :
    ∀ p ∈ useModule.axiomSet, Sentence.Satisfies naturalModel p := by
  rintro p ⟨d, hd, rfl⟩
  change d ∈ [_, _] at hd
  cases hd with
  | head => exact excluded_middle_true
  | tail _ hd =>
      cases hd with
      | head => exact reach_true
      | tail _ impossible => cases impossible

theorem false_claim_unproved : ¬ useModule.Proves falseClaim := by
  intro h
  exact false_claim_false (h naturalModel model_satisfies_importer)

/-- The enlarged language really contains nonmonotone free-set dependencies;
only bound recursion variables are subject to the positivity requirement. -/
theorem negative_free_not_monotone :
    ¬ Monotone (fun X : Set Nat =>
      (Matching.GeneralFixedPoint.Pattern.neg (.setvar 0) :
        Pattern checked.ambient [("@Y", "S")] [] "S").denote naturalModel
          (fun i => i.elim0) (fun _ => X)) := by
  change ¬ Monotone (fun X : Set Nat => Xᶜ)
  intro h
  have bad : (∅ : Set Nat)ᶜ ⊆ Set.univᶜ := h (Set.empty_subset _)
  have absurd := bad (show 0 ∈ (∅ : Set Nat)ᶜ by simp)
  exact absurd trivial

theorem claims_separate : useModule.localAxioms.length = 1 ∧
    useModule.claims.length = 1 ∧ useModule.axioms.length = 2 := by decide +kernel

theorem imported_origin :
    (useModule.axioms.map Kore.Modules.Checking.CheckedSentence.origin) = [⟨"USE", 1⟩, ⟨"BASE", 3⟩] :=
  by decide +kernel

theorem imported_parent : base.asImport ∈ useModule.imports := by
  change base.asImport ∈ [base.asImport]
  exact List.mem_singleton_self _

noncomputable def actualImport :=
  Kore.Modules.Checking.CheckedModule.importHom base useModule imported_parent

noncomputable def actualNativeImport := Modules.nativeImportHom base useModule imported_parent

end Silmaril.Logic.Kore.GeneralFixedPoint.ModuleExamples
