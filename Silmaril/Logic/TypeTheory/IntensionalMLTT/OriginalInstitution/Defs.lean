module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability.FiniteSoundness.Thms
public import Silmaril.Logic.Institution.Metatheory.Entailment
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.WithBot

@[expose] public section

/-!
# The original cumulative typing calculus as concrete realizability institutions

Finite capacities interpret every declaration and carrier by actual Code cap
membership. The top capacity uses the actual full code hierarchy. A syntax stage
admits capacities at least that stage; an inclusion retains the actual capacity,
so no equivalence between different-cap interpretations is assumed.
-/

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT.OriginalInstitution

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Metatheory

/-- The finite universe-count stages and their actual full-hierarchy apex. -/
abbrev Stage := WithTop ℕ

/-- Bound every context, term and carrier occurrence, with no bound at the apex. -/
abbrev Sentence (stage : Stage) :=
  {q : ScopedTyping // (q.universeBound : WithTop ℕ) ≤ stage}

/-- Actual finite code truncations or the full code hierarchy supplying this stage. -/
abbrev Model (stage : Stage) := {capacity : Stage // stage ≤ capacity}

/-- Concrete finite-cap realization, or the full actual hierarchy at top. -/
noncomputable def CapacityValid : Stage → ScopedTyping → Prop
  | none, q => RawRealizability.Valid q.Γ q.term q.carrier
  | some cap, q => RawRealizability.ValidAt cap q.Γ q.term q.carrier

/-- The complete original proof tree, including formation and raw conversion intermediates. -/
abbrev Proof (stage : Stage) (H : Set ScopedTyping) (q : ScopedTyping) :=
  {d : DerivationH H q.Γ q.term q.carrier // (d.universeBudget : WithTop ℕ) ≤ stage}

/-- Actual scoped typing assumptions have bounded hypothesis leaves. -/
def Proof.hyp {stage : Stage} {H : Set ScopedTyping} (q : ScopedTyping)
    (hq : q ∈ H) (hBound : (q.universeBound : WithTop ℕ) ≤ stage) : Proof stage H q :=
  ⟨.hyp hq, by simpa [DerivationH.universeBudget, ScopedTyping.universeBound] using hBound⟩

/-- Enlarging a proof cap leaves the complete original proof tree unchanged. -/
def Proof.include {stage more : Stage} {H : Set ScopedTyping} {q : ScopedTyping}
    (h : stage ≤ more) (d : Proof stage H q) : Proof more H q := ⟨d.val, d.property.trans h⟩

/-- Substitute proof trees beneath every original rule, retaining the actual stage bound. -/
noncomputable def Proof.bind {stage : Stage} {H K : Set ScopedTyping} {q : ScopedTyping}
    (d : Proof stage H q) (hH : ∀ r ∈ H, Proof stage K r) : Proof stage K q :=
  match stage with
  | none => ⟨d.val.bind (fun r hr => (hH r hr).val), le_top⟩
  | some cap =>
      let e := (show BoundedDerivationH cap H q.Γ q.term q.carrier from
        ⟨d.val, WithTop.coe_le_coe.mp d.property⟩).bind
          (fun r hr => ⟨(hH r hr).val, WithTop.coe_le_coe.mp (hH r hr).property⟩)
      ⟨e.val, WithTop.coe_le_coe.mpr e.property⟩

/-- The room of actual original typing judgments and concrete code capacities. -/
noncomputable def room (stage : Stage) : Room.{0, 0, 0} where
  Sen := Sentence stage
  Mod := Cat.of (Discrete (Model stage))
  Sat T q := CapacityValid T.as.val q.val

/-- The fixed-language institution at an actual finite or full stage. -/
noncomputable def inst (stage : Stage) : Discrete Unit ⥤ Room.{0, 0, 0} :=
  Discrete.functor (fun _ => room stage)

/-- The institution of the original scoped typing calculus at this stage. -/
noncomputable def bundled (stage : Stage) : Inst.{0, 0, 0, 0, 0} where
  Sign := Discrete Unit
  I := inst stage

/-- Full original-rule consequence with actual typing-hypothesis leaves. -/
noncomputable def logic (stage : Stage) : LogicalSystem.{0, 0, 0, 0, 0} (Discrete Unit) where
  I := inst stage
  Derives _ H q := Nonempty (Proof stage (Subtype.val '' H) q.val)
  refl _ q := ⟨Proof.hyp q.val ⟨q, Set.mem_singleton q, rfl⟩ q.property⟩
  mono := by
    intro S H K q hHK h
    rcases h with ⟨d⟩
    have hRep : ∀ r ∈ Subtype.val '' H, Nonempty (Proof stage (Subtype.val '' K) r) := by
      rintro r ⟨s, hs, rfl⟩
      exact ⟨Proof.hyp s.val ⟨s, hHK hs, rfl⟩ s.property⟩
    exact ⟨d.bind (fun r hr => Classical.choice (hRep r hr))⟩
  trans := by
    intro S H Δ q hΔ h
    rcases h with ⟨d⟩
    have hRep : ∀ r ∈ Subtype.val '' (H ∪ Δ), Nonempty (Proof stage (Subtype.val '' H) r) := by
      rintro r ⟨s, hs, rfl⟩
      rcases hs with hs | hs
      · exact ⟨Proof.hyp s.val ⟨s, hs, rfl⟩ s.property⟩
      · exact hΔ s hs
    exact ⟨d.bind (fun r hr => Classical.choice (hRep r hr))⟩
  map_derives := by
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ σ H q h
    rw [Subsingleton.elim σ (𝟙 _), CategoryTheory.Functor.map_id]
    simpa using h

/-- Include a smaller bounded sentence without changing its actual scoped typing judgment. -/
def includeSentence {stage more : Stage} (h : stage ≤ more) (q : Sentence stage) : Sentence more :=
  ⟨q.val, q.property.trans h⟩

/-- Restriction retains the actual finite truncation or full code interpretation. -/
def modelReduct {stage more : Stage} (h : stage ≤ more) :
    Discrete (Model more) ⥤ Discrete (Model stage) :=
  Discrete.functor (fun T => Discrete.mk ⟨T.val, h.trans T.property⟩)

/-- Inclusion preserves satisfaction because the actual semantic capacity is retained. -/
noncomputable def inclusionCorridor {stage more : Stage} (h : stage ≤ more) : room stage ⟶ room more where
  sen := includeSentence h
  mod := modelReduct h
  sat _ _ := Iff.rfl

/-- Stage enlargement as an institution comorphism. -/
noncomputable def inclusion {stage more : Stage} (h : stage ≤ more) :
    Inst.CoHom (bundled stage) (bundled more) where
  Φ := 𝟭 _
  ρ := Discrete.natTrans (fun _ => inclusionCorridor h)

/-- Every inclusion preserves actual full original-rule consequence. -/
noncomputable def inclusionLogic {stage more : Stage} (h : stage ≤ more) :
    LogicalSystem.CoHom (logic stage) (logic more) where
  Φ := (inclusion h).Φ
  ρ := (inclusion h).ρ
  map_derives := by
    intro S H q hd
    rcases hd with ⟨d⟩
    have hRep : ∀ r ∈ Subtype.val '' H,
        Nonempty (Proof more (Subtype.val '' (includeSentence h '' H)) r) := by
      rintro r ⟨s, hs, rfl⟩
      exact ⟨Proof.hyp s.val ⟨includeSentence h s, ⟨s, hs, rfl⟩, rfl⟩ (s.property.trans h)⟩
    exact ⟨(d.include h).bind (fun r hr => Classical.choice (hRep r hr))⟩

end Silmaril.Logic.TypeTheory.IntensionalMLTT.OriginalInstitution
