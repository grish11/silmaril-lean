module

public import Silmaril.Logic.Egg.Source.Named.Resolution.Defs
public import Silmaril.Logic.Egglog.Source.Named.Resolution.Thms

@[expose] public section
namespace Silmaril.Logic.Egg.Source.Named
open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Egglog.Source.Named

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Exact annotated source spelling of a local term. -/
def eraseTerm {D : Declarations} (Γ : CheckedContext D) :
    {s : D.checked.LocalSort} → EQ.Term D.signature Γ.profile s → RawTerm
  | _, .var i => .var (Γ.bindings.get i).name
  | s, .app o arguments => .app o.val.name s.val _ (fun i => eraseTerm Γ (arguments i))

theorem eraseTerm_denotes {D : Declarations} (Γ : CheckedContext D)
    (M : Core.Model D.signature) (ρ : Valuation M Γ) {s : D.checked.LocalSort}
    (term : EQ.Term D.signature Γ.profile s) :
    (eraseTerm Γ term).Denotes M Γ ρ s (term.eval M ρ) := by
  exact EQ.Term.rec (motive := fun s term =>
    (eraseTerm Γ term).Denotes M Γ ρ s (term.eval M ρ))
    (fun i => .var i _ rfl)
    (fun o arguments ih => .app o _ _ rfl rfl _ _ ih) term

/-- Same-name finite declarations fix the sorted operation, even when semantic
operations identify values and ordinary homomorphisms are noninjective. -/
theorem denotes_unique {D : Declarations} (Γ : CheckedContext D)
    (M : Core.Model D.signature) (ρ : Valuation M Γ) {raw : RawTerm}
    {s : D.checked.LocalSort} {value : M.carrier s} (denotes : raw.Denotes M Γ ρ s value) :
    ∀ (t : D.checked.LocalSort) (other : M.carrier t), raw.Denotes M Γ ρ t other →
      (⟨s, value⟩ : Σ s, M.carrier s) = ⟨t, other⟩ := by
  induction denotes with
  | var i name named =>
      intro t other second
      cases second with
      | var j _ named' =>
          have positions := binding_name_injective Γ (named.trans named'.symm)
          subst j
          rfl
  | app o name result named annotated arguments values denotes ih =>
      intro t other second
      cases second with
      | app p _ _ named' annotated' _ otherValues otherDenotes =>
          obtain ⟨profiles, outputs, symbols⟩ :=
            constructor_profile_unique o p (named.trans named'.symm)
          subst_vars
          have valuesEqual : values = otherValues := by
            funext i
            exact eq_of_heq (Sigma.mk.inj (ih i _ _ (otherDenotes i))).2
          subst otherValues
          rfl

/-- All original annotations, names and ordered children survive resolution. -/
theorem resolveTerm_erase {D : Declarations} (Γ : CheckedContext D) (raw : RawTerm)
    (resolved : PackedTerm Γ) (success : resolveTerm? Γ raw = some resolved) :
    eraseTerm Γ resolved.2 = raw := by
  induction raw generalizing resolved with
  | var name =>
      cases hi : (List.finRange Γ.bindings.length).find?
          (fun i => (Γ.bindings.get i).name == name) with
      | none =>
          simp only [resolveTerm?, Silmaril.Logic.Egglog.Source.Named.resolveTerm?, hi,
            bind, Option.bind] at success
          cases success
      | some i =>
          simp only [resolveTerm?, Silmaril.Logic.Egglog.Source.Named.resolveTerm?, hi,
            bind, Option.bind, Option.pure_def, Option.some.injEq] at success
          subst resolved
          exact congrArg RawTerm.var (by simpa using List.find?_some hi)
  | app name result n arguments ih =>
      cases hc : constructor? D.checked name n with
      | none =>
          simp only [resolveTerm?, hc, bind, Option.bind] at success
          cases success
      | some symbol =>
          rcases symbol with ⟨w, s, o⟩
          by_cases annotated : s.val = result
          · cases hr : sequence? n (fun i => do
                let packed ← resolveTerm? Γ (arguments i)
                termAt? (w i) packed) with
            | none =>
                simp only [bind, Option.bind] at hr
                simp only [resolveTerm?, hc, annotated, ↓reduceIte, bind, Option.bind, hr] at success
                cases success
            | some terms =>
                simp only [bind, Option.bind] at hr
                simp only [resolveTerm?, hc, annotated, ↓reduceIte, bind, Option.bind, hr,
                  Option.pure_def, Option.some.injEq] at success
                subst resolved
                have named := constructor?_name D.checked name n ⟨w, s, o⟩ hc
                change o.val.name = name at named
                simp only [eraseTerm]
                rw [named, annotated]
                apply congrArg (RawTerm.app name result n)
                funext i
                have component := sequence_component n _ terms hr i
                cases hp : resolveTerm? Γ (arguments i) with
                | none => simp [hp] at component
                | some packed =>
                    have transported : termAt? (w i) packed = some (terms i) := by
                      simpa [hp] using component
                    have original := termAt?_eq (w i) packed (terms i) transported
                    rw [original] at hp
                    exact ih i _ hp
          · simp [resolveTerm?, hc, annotated] at success

theorem eraseTerm_denotes_iff {D : Declarations} (Γ : CheckedContext D)
    (M : Core.Model D.signature) (ρ : Valuation M Γ) {s : D.checked.LocalSort}
    (term : EQ.Term D.signature Γ.profile s) (value : M.carrier s) :
    (eraseTerm Γ term).Denotes M Γ ρ s value ↔ term.eval M ρ = value := by
  have canonical := eraseTerm_denotes Γ M ρ term
  constructor
  · intro denotes
    exact eq_of_heq (Sigma.mk.inj (denotes_unique Γ M ρ canonical _ _ denotes)).2
  · intro equal
    rw [← equal]
    exact canonical

theorem resolveTerm_denotes_iff {D : Declarations} (Γ : CheckedContext D) (raw : RawTerm)
    (resolved : PackedTerm Γ) (success : resolveTerm? Γ raw = some resolved)
    (M : Core.Model D.signature) (ρ : Valuation M Γ) (value : M.carrier resolved.1) :
    raw.Denotes M Γ ρ resolved.1 value ↔ resolved.2.eval M ρ = value := by
  rw [← resolveTerm_erase Γ raw resolved success]
  exact eraseTerm_denotes_iff Γ M ρ resolved.2 value

def eraseEquality {D : Declarations} (Γ : CheckedContext D)
    (e : Core.Equality D.signature Γ.profile) : RawEquality :=
  ⟨eraseTerm Γ e.lhs, eraseTerm Γ e.rhs⟩

theorem eraseEquality_holds_iff {D : Declarations} (Γ : CheckedContext D)
    (M : Core.Model D.signature) (ρ : Valuation M Γ)
    (e : Core.Equality D.signature Γ.profile) :
    (eraseEquality Γ e).Holds M Γ ρ ↔ e.Holds M ρ := by
  constructor
  · rintro ⟨sort, left, right, hl, hr, equal⟩
    have canonical := eraseTerm_denotes Γ M ρ e.lhs
    have same := denotes_unique Γ M ρ canonical _ _ hl
    cases same
    have value := (eraseTerm_denotes_iff Γ M ρ e.rhs _).mp hr
    exact equal.trans value.symm
  · intro equal
    exact ⟨e.sort, _, _, eraseTerm_denotes Γ M ρ e.lhs,
      eraseTerm_denotes Γ M ρ e.rhs, equal⟩

theorem resolveEquality_erase {D : Declarations} (Γ : CheckedContext D)
    (raw : RawEquality) (resolved : Core.Equality D.signature Γ.profile)
    (success : resolveEquality? Γ raw = some resolved) : eraseEquality Γ resolved = raw := by
  rcases raw with ⟨left, right⟩
  cases hl : resolveTerm? Γ left with
  | none => simp [resolveEquality?, hl] at success
  | some packedLeft =>
      rcases packedLeft with ⟨sort, typedLeft⟩
      cases hr : resolveTerm? Γ right with
      | none => simp [resolveEquality?, hl, hr] at success
      | some packedRight =>
          cases ht : termAt? sort packedRight with
          | none => simp [resolveEquality?, hl, hr, ht] at success
          | some typedRight =>
              simp [resolveEquality?, hl, hr, ht] at success
              subst resolved
              have rightOriginal := termAt?_eq sort packedRight typedRight ht
              rw [rightOriginal] at hr
              simp only [eraseEquality]
              rw [resolveTerm_erase Γ left _ hl, resolveTerm_erase Γ right _ hr]

theorem resolveEquality_holds_iff {D : Declarations} (Γ : CheckedContext D)
    (raw : RawEquality) (resolved : Core.Equality D.signature Γ.profile)
    (success : resolveEquality? Γ raw = some resolved)
    (M : Core.Model D.signature) (ρ : Valuation M Γ) :
    raw.Holds M Γ ρ ↔ resolved.Holds M ρ := by
  rw [← resolveEquality_erase Γ raw resolved success]
  exact eraseEquality_holds_iff Γ M ρ resolved

/-- All contexts with the same complete binder list are equal. -/
private theorem rule_holds_context {D : Declarations} (Γ : CheckedContext D)
    (M : Core.Model D.signature) (r : RawRule) (same : r.context = Γ.bindings) :
    r.Holds M ↔ ∀ ρ : Valuation M Γ,
      (∀ e ∈ r.guards, e.Holds M Γ ρ) → r.conclusion.Holds M Γ ρ := by
  constructor
  · rintro ⟨other, bindings, holds⟩
    have equal := Silmaril.Logic.Egglog.Source.Named.CheckedContext.eq_of_bindings
      other Γ (bindings.trans same)
    subst other
    exact holds
  · intro holds
    exact ⟨Γ, same.symm, holds⟩

/-- Exact conditional-equation adequacy, with all guards and all binders. -/
theorem resolveRule_holds_iff (D : Declarations) (raw : RawRule)
    (resolved : Core.Rule D.signature) (success : resolveRule? D raw = some resolved)
    (M : Core.Model D.signature) : raw.Holds M ↔ resolved.Holds M := by
  cases hc : Silmaril.Logic.Egglog.Source.Named.Context.check D.checked raw.context with
  | none => simp [resolveRule?, hc] at success
  | some Γ =>
      cases hg : raw.guards.mapM (resolveEquality? Γ) with
      | none => simp [resolveRule?, hc, hg] at success
      | some guards =>
          cases hh : resolveEquality? Γ raw.conclusion with
          | none => simp [resolveRule?, hc, hg, hh] at success
          | some conclusion =>
              simp [resolveRule?, hc, hg, hh] at success
              subst resolved
              have bindings := context_check_bindings D.checked raw.context Γ hc
              rw [rule_holds_context Γ M raw bindings.symm]
              change (∀ ρ, (∀ e ∈ raw.guards, e.Holds M Γ ρ) →
                raw.conclusion.Holds M Γ ρ) ↔
                ∀ ρ, (∀ e ∈ guards, e.Holds M ρ) → conclusion.Holds M ρ
              apply forall_congr'
              intro ρ
              exact imp_congr
                (mapM_forall_iff _ raw.guards guards hg _ _
                  (fun e typed accepted => resolveEquality_holds_iff Γ e typed accepted M ρ))
                (resolveEquality_holds_iff Γ raw.conclusion conclusion hh M ρ)

/-- Every original rule is interpreted in the same algebra as every other rule.
Whole-file adequacy does not select a representative entry. -/
theorem resolveProgram_holds_iff (D : Declarations) (raw : RawProgram)
    (resolved : List (Core.Rule D.signature)) (success : resolveProgram? D raw = some resolved)
    (M : Core.Model D.signature) : raw.Holds M ↔ ∀ r ∈ resolved, r.Holds M := by
  unfold resolveProgram? at success
  split at success
  · exact mapM_forall_iff _ raw resolved success _ _
      (fun r typed accepted => resolveRule_holds_iff D r typed accepted M)
  · contradiction

end Silmaril.Logic.Egg.Source.Named
