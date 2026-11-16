module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Aliases.Modules.Examples

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 400000
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Aliases.ModuleExamples

def seedOp : checked.ambient.signature.operations 0 (fun i => seedSymbol.declaration.arguments.get i) "S" :=
  ⟨checked.ambient.symbols.get ⟨0, by decide +kernel⟩, by decide +kernel,
    by decide +kernel, by decide +kernel⟩
def stepOp : checked.ambient.signature.operations 1 (fun i => stepSymbol.declaration.arguments.get i) "S" :=
  ⟨checked.ambient.symbols.get ⟨1, by decide +kernel⟩, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

def seed {sets objects : Names} : Pattern checked.ambient sets objects "S" :=
  .app seedOp (fun i => i.elim0)
def step {sets objects : Names} (p : Pattern checked.ambient sets objects "S") :
    Pattern checked.ambient sets objects "S" := .app stepOp (Fin.cases p (fun i => i.elim0))
def actual {sets objects : Names} : Pattern checked.ambient sets objects "S" :=
  seed.disj (step seed)

def reachBody : Pattern checked.ambient [("@X", "S")] [] "S" :=
  actual.disj (step (.setvar 0))
def persistBody : Pattern checked.ambient [("@Z", "S")] [] "S" :=
  .conj (.base Matching.FirstOrder.Pattern.top) (actual.disj (step (.setvar 0)))
def expanded : Pattern checked.ambient [] [] "S" :=
  .conj (.mu reachBody) (.nu persistBody)
def axiomRaw : RawPattern :=
  .app "chain" [.disj "S" (.app "seed" []) (.app "step" [.app "seed" []]), .top "S"]

theorem axiom_checked :
    (Checking.elaborate checked.ambient checked.aliases 48 [] [] "S" axiomRaw).isSome = true := by
  decide +kernel

def compiledAxiom : Pattern checked.ambient [] [] "S" :=
  (Checking.elaborate checked.ambient checked.aliases 48 [] [] "S" axiomRaw).get axiom_checked

theorem compiledAxiom_accepted :
    Checking.elaborate checked.ambient checked.aliases 48 [] [] "S" axiomRaw = some compiledAxiom :=
  (Option.some_get axiom_checked).symm

/-- Canonical finite argument functions avoid comparing unreduced traversals
under impossible zero-arity arguments. This is fixture proof support. -/
private def finiteArgs {n : Nat} {β : Fin n → Type} (f : ∀ i, β i) : ∀ i, β i :=
  match n with
  | 0 => fun i => i.elim0
  | _ + 1 => Fin.cases (f 0) (finiteArgs (fun i => f i.succ))

private theorem finiteArgs_eq {n : Nat} {β : Fin n → Type} (f : ∀ i, β i) :
    finiteArgs f = f := by
  induction n with
  | zero => funext i; exact i.elim0
  | succ n ih =>
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact congrFun (ih (fun j => f j.succ)) j

private def canonical {r k : Nat} {P : Fin r → String} {Γ : Fin k → String} {s : String}
    (p : Matching.GeneralFixedPoint.Pattern checked.ambient.signature P Γ s) :
    Matching.GeneralFixedPoint.Pattern checked.ambient.signature P Γ s := by
  induction p with
  | base p => exact .base p
  | setvar i => exact .setvar i
  | app op args ih => exact .app op (finiteArgs ih)
  | neg p ih => exact .neg ih
  | conj p q hp hq => exact .conj hp hq
  | ex b p ih => exact .ex b ih
  | mu p ih => exact .mu ih
  | nu p ih => exact .nu ih

private theorem canonical_eq {r k : Nat} {P : Fin r → String} {Γ : Fin k → String} {s : String}
    (p : Matching.GeneralFixedPoint.Pattern checked.ambient.signature P Γ s) : canonical p = p := by
  induction p with
  | base p => rfl
  | setvar i => rfl
  | app op args ih =>
      change Matching.GeneralFixedPoint.Pattern.app op (finiteArgs _) = _
      rw [finiteArgs_eq]
      exact congrArg (Matching.GeneralFixedPoint.Pattern.app op) (funext ih)
  | neg p ih => exact congrArg Matching.GeneralFixedPoint.Pattern.neg ih
  | conj p q hp hq => exact congrArg₂ Matching.GeneralFixedPoint.Pattern.conj hp hq
  | ex b p ih => exact congrArg (Matching.GeneralFixedPoint.Pattern.ex b) ih
  | mu p ih => exact congrArg Matching.GeneralFixedPoint.Pattern.mu ih
  | nu p ih => exact congrArg Matching.GeneralFixedPoint.Pattern.nu ih

private def normalized (p : Pattern checked.ambient [] [] "S") : Pattern checked.ambient [] [] "S" :=
  canonical (p.substitute (fun i => .setvar i) (fun i => .base (.var i)))

private theorem normalized_meaning (p : Pattern checked.ambient [] [] "S") :
    (normalized p).denote naturalModel (fun i => i.elim0) (fun i => i.elim0) =
      p.denote naturalModel (fun i => i.elim0) (fun i => i.elim0) := by
  unfold normalized
  rw [canonical_eq]
  exact p.denote_substitute_id naturalModel _ _

/-- Native source expansion is compared through a semantics-preserving
canonical presentation of finite argument functions and first-order leaves. -/
theorem axiom_expansion : compiledAxiom.denote naturalModel
    (fun i => i.elim0) (fun i => i.elim0) =
    expanded.denote naturalModel (fun i => i.elim0) (fun i => i.elim0) := by
  have same : normalized compiledAxiom = normalized expanded := by rfl
  rw [← normalized_meaning compiledAxiom, same, normalized_meaning expanded]

theorem seed_meaning {sets objects : Names}
    (v : ∀ i, naturalModel.carrier (context objects i))
    (η : ∀ i, Set (naturalModel.carrier (context sets i))) :
    (seed : Pattern checked.ambient sets objects "S").denote naturalModel v η = {0, 1} := by
  change {result : Nat | ∃ values : Fin 0 → Nat,
    (∀ i : Fin 0, _) ∧ result ∈ ({0, 1} : Set Nat)} = _
  ext x
  constructor
  · rintro ⟨_, _, hx⟩
    exact hx
  · intro hx
    exact ⟨(fun i => i.elim0), (fun i => i.elim0), hx⟩

theorem step_meaning {sets objects : Names} (p : Pattern checked.ambient sets objects "S")
    (v : ∀ i, naturalModel.carrier (context objects i))
    (η : ∀ i, Set (naturalModel.carrier (context sets i))) :
    (step p).denote naturalModel v η = {result | ∃ n ∈ p.denote naturalModel v η, result = n + 1} := by
  change {result : Nat | ∃ values : Fin 1 → Nat,
    (∀ i : Fin 1, _) ∧ (∃ i : Fin 1, result = values i + 1)} = _
  ext x
  simp only [Set.mem_ofPred_eq, Fin.forall_fin_one, Fin.exists_fin_one, Fin.cases_zero]
  constructor
  · rintro ⟨values, hv, hx⟩
    exact ⟨values 0, hv, hx⟩
  · rintro ⟨n, hn, hx⟩
    exact ⟨fun _ => n, hn, hx⟩

theorem disj_meaning {sets objects : Names} (p q : Pattern checked.ambient sets objects "S")
    (v : ∀ i, naturalModel.carrier (context objects i))
    (η : ∀ i, Set (naturalModel.carrier (context sets i))) :
    (p.disj q).denote naturalModel v η = p.denote naturalModel v η ∪ q.denote naturalModel v η := by
  let a : Set Nat := p.denote naturalModel v η
  let b : Set Nat := q.denote naturalModel v η
  change (aᶜ ∩ bᶜ)ᶜ = a ∪ b
  simp only [← Set.compl_union, compl_compl]

theorem reachBody_meaning (X : Set Nat) :
    reachBody.denote naturalModel (fun i => i.elim0) (Fin.cases X (fun i => i.elim0)) =
      ({0, 1} ∪ {result | ∃ n ∈ ({0, 1} : Set Nat), result = n + 1}) ∪
        {result | ∃ n ∈ X, result = n + 1} := by
  simp only [reachBody, actual, disj_meaning, seed_meaning, step_meaning]
  rfl

theorem persistBody_meaning (X : Set Nat) :
    persistBody.denote naturalModel (fun i => i.elim0) (Fin.cases X (fun i => i.elim0)) =
      ({0, 1} ∪ {result | ∃ n ∈ ({0, 1} : Set Nat), result = n + 1}) ∪
        {result | ∃ n ∈ X, result = n + 1} := by
  change naturalModel.denote (Γ := context []) (s := "S") (fun i => i.elim0)
    Matching.FirstOrder.Pattern.top ∩ _ = _
  rw [Matching.FirstOrder.Model.denote_top, Set.univ_inter]
  exact reachBody_meaning X

/-- The actual μ computes the infinite successor closure of a nonsingleton
argument; this is not a finite unfolding or an empty-carrier example. -/
theorem reach_all :
    (Matching.GeneralFixedPoint.Pattern.mu reachBody).denote naturalModel
      (fun i => i.elim0) (fun i => i.elim0) = Set.univ := by
  change sInf {X : Set Nat | reachBody.denote naturalModel (fun i => i.elim0)
    (Fin.cases X (fun i => i.elim0)) ⊆ X} = _
  rw [Set.eq_univ_iff_forall]
  intro n
  apply Set.mem_sInter.mpr
  intro X hX
  change reachBody.denote naturalModel (fun i => i.elim0)
    (Fin.cases X (fun i => i.elim0)) ⊆ X at hX
  rw [reachBody_meaning] at hX
  induction n with
  | zero => exact hX (Or.inl (Or.inl (by simp)))
  | succ n ih => exact hX (Or.inr ⟨n, ih, rfl⟩)

/-- The ν branch is proved through an actual post-fixed set witness. -/
theorem persist_all :
    (Matching.GeneralFixedPoint.Pattern.nu persistBody).denote naturalModel
      (fun i => i.elim0) (fun i => i.elim0) = Set.univ := by
  change sSup {X : Set Nat | X ⊆ persistBody.denote naturalModel (fun i => i.elim0)
    (Fin.cases X (fun i => i.elim0))} = _
  have postfixed : (Set.univ : Set Nat) ⊆
      persistBody.denote naturalModel (fun i => i.elim0)
        (Fin.cases Set.univ (fun i => i.elim0)) := by
    rw [persistBody_meaning]
    intro n _
    cases n with
    | zero => exact Or.inl (Or.inl (by simp))
    | succ n => exact Or.inr ⟨n, Set.mem_univ n, rfl⟩
  rw [Set.eq_univ_iff_forall]
  intro n
  exact Set.mem_sUnion.mpr ⟨Set.univ, postfixed, Set.mem_univ n⟩

theorem expanded_all : expanded.denote naturalModel (fun i => i.elim0) (fun i => i.elim0) = Set.univ := by
  change (Matching.GeneralFixedPoint.Pattern.mu reachBody).denote naturalModel
      (fun i => i.elim0) (fun i => i.elim0) ∩
    (Matching.GeneralFixedPoint.Pattern.nu persistBody).denote naturalModel
      (fun i => i.elim0) (fun i => i.elim0) = Set.univ
  rw [reach_all, persist_all, Set.univ_inter]

/-- The independent raw interpreter agrees for the genuinely used μ/ν alias
chain in the complete module's axiom, on an infinite carrier. -/
theorem source_axiom_all : Semantics.denote checked.ambient checked.aliases naturalModel
    48 [] [] "S" axiomRaw = some Set.univ := by
  have meaning := Semantics.elaborate_sound checked.aliases naturalModel 48 [] [] "S"
    axiomRaw compiledAxiom (fun i => i.elim0) (fun i => i.elim0) compiledAxiom_accepted
  rw [axiom_expansion, expanded_all] at meaning
  simpa only [Semantics.interpret, GeneralFixedPoint.Semantics.interpret,
    Kore.FixedPoint.Semantics.interpret] using meaning

end Silmaril.Logic.Kore.GeneralFixedPoint.Aliases.ModuleExamples
