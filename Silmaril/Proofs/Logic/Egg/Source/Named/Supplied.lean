module

public import Silmaril.Logic.Egg.Source.Named.Supplied.Defs
public import Silmaril.Logic.Egglog.Source.Named.Supplied.Thms

@[expose] public section
namespace Silmaril.Logic.Egg.Source.Named
open CategoryTheory Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Egglog.Source.Named (context_check_bindings context_check_valid)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem eraseTermAt_context {D : Declarations} (Γ : CheckedContext D) {s : D.checked.LocalSort}
    (term : EQ.Term D.signature Γ.profile s) :
    eraseTermAt (fun i => (Γ.bindings.get i).name) term = eraseTerm Γ term := by
  refine EQ.Term.rec (motive := fun _ term =>
    eraseTermAt (fun i => (Γ.bindings.get i).name) term = eraseTerm Γ term) ?_ ?_ term
  · intro i; rfl
  · intro n w s o arguments ih
    simp only [eraseTermAt, eraseTerm]
    congr 1
    exact funext ih

theorem eraseEqualityAt_context {D : Declarations} (Γ : CheckedContext D)
    (e : Core.Equality D.signature Γ.profile) :
    eraseEqualityAt (fun i => (Γ.bindings.get i).name) e = eraseEquality Γ e := by
  simp only [eraseEqualityAt, eraseEquality, eraseTermAt_context]

namespace DeclarationHom

theorem eraseTermAt_map {D E : Declarations} (f : DeclarationHom D E)
    {k : Nat} {profile : Fin k → D.checked.LocalSort} (names : Fin k → String)
    {s : D.checked.LocalSort} (term : EQ.Term D.signature profile s) :
    eraseTermAt names (term.map f.symbols.toHom) = eraseTermAt names term := by
  refine EQ.Term.rec (motive := fun _ term =>
    eraseTermAt names (term.map f.symbols.toHom) = eraseTermAt names term) ?_ ?_ term
  · intro i; rfl
  · intro n w s o arguments ih
    simp only [EQ.Term.map, eraseTermAt, f.constructor_name, f.sort_name]
    congr 1
    exact funext ih

theorem eraseEqualityAt_map {D E : Declarations} (f : DeclarationHom D E)
    {k : Nat} {profile : Fin k → D.checked.LocalSort} (names : Fin k → String)
    (e : Core.Equality D.signature profile) :
    eraseEqualityAt names (e.map f.symbols.toHom) = eraseEqualityAt names e := by
  simp only [Core.Equality.map, eraseEqualityAt, eraseTermAt_map]
end DeclarationHom

theorem resolveEqualities_erase {D : Declarations} (Γ : CheckedContext D)
    (raw : List RawEquality) (es : List (Core.Equality D.signature Γ.profile))
    (success : raw.mapM (resolveEquality? Γ) = some es) : es.map (eraseEquality Γ) = raw := by
  induction raw generalizing es with
  | nil => simp at success; subst es; rfl
  | cons first rest ih =>
      cases hf : resolveEquality? Γ first with
      | none => simp [hf] at success
      | some e =>
          cases hr : rest.mapM (resolveEquality? Γ) with
          | none => simp [hf, hr] at success
          | some tail =>
              simp [hf, hr] at success
              subst es
              simp only [List.map_cons, resolveEquality_erase Γ first e hf, ih tail hr]

theorem eraseRuleAt_resolve {D : Declarations} (Γ : CheckedContext D)
    (legal : ∀ b ∈ Γ.bindings, Silmaril.Logic.Egglog.Source.Named.LegalName b.name)
    (profile : Fin Γ.bindings.length → D.checked.LocalSort) (same : profile = Γ.profile)
    (label : String) (guards : List (Core.Equality D.signature profile))
    (conclusion : Core.Equality D.signature profile) :
    resolveRule? D ⟨label, Γ.bindings,
      guards.map (eraseEqualityAt (fun i => (Γ.bindings.get i).name)),
      eraseEqualityAt (fun i => (Γ.bindings.get i).name) conclusion⟩ =
      some ⟨Γ.bindings.length, profile, guards, conclusion⟩ := by
  subst profile
  have erased : (eraseEqualityAt (fun i => (Γ.bindings.get i).name) :
      Core.Equality D.signature Γ.profile → RawEquality) = eraseEquality Γ :=
    funext (eraseEqualityAt_context Γ)
  simpa only [erased] using eraseRule_resolve Γ legal label guards conclusion

namespace DeclarationHom
/-- Actual same-source resolver naturality. No field assumes this theorem. -/
theorem resolveRule_map {D E : Declarations} (f : DeclarationHom D E)
    (raw : RawRule) (r : Core.Rule D.signature) (success : resolveRule? D raw = some r) :
    resolveRule? E raw = some (r.map f.symbols.toHom) := by
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
              subst r
              have bindings := context_check_bindings D.checked raw.context Γ hc
              have legal := (context_check_valid D.checked raw.context Γ hc).2.1
              have guardsRaw := resolveEqualities_erase Γ raw.guards guards hg
              have conclusionRaw := resolveEquality_erase Γ raw.conclusion conclusion hh
              have complete := eraseRuleAt_resolve (mapContext f Γ)
                (by simpa only [mapContext, Silmaril.Logic.Egglog.Source.Named.DeclarationHom.mapContext,
                  bindings] using legal)
                (f.symbols.sorts ∘ Γ.profile) (mapContext_profile f Γ).symm raw.name
                (guards.map (Core.Equality.map f.symbols.toHom)) (conclusion.map f.symbols.toHom)
              have rebuilt : (⟨raw.name, raw.context, raw.guards, raw.conclusion⟩ : RawRule) = raw := by
                cases raw
                rfl
              simpa only [mapContext, Silmaril.Logic.Egglog.Source.Named.DeclarationHom.mapContext,
                List.map_map, Function.comp_def, eraseEqualityAt_map, eraseEqualityAt_context,
                guardsRaw, conclusionRaw, bindings, Core.Rule.map, rebuilt] using complete

/-- Every original ordered rule translates under the actual vocabulary map. -/
theorem resolveProgram_map {D E : Declarations} (f : DeclarationHom D E)
    (raw : RawProgram) (rules : List (Core.Rule D.signature))
    (success : resolveProgram? D raw = some rules) :
    resolveProgram? E raw = some (rules.map (Core.Rule.map f.symbols.toHom)) := by
  have mapRules : ∀ (xs : RawProgram) (ys : List (Core.Rule D.signature)),
      xs.mapM (resolveRule? D) = some ys →
      xs.mapM (resolveRule? E) = some (ys.map (Core.Rule.map f.symbols.toHom)) := by
    intro xs
    induction xs with
    | nil => intro ys h; simp at h; subst ys; rfl
    | cons first rest ih =>
        intro ys h
        cases hf : resolveRule? D first with
        | none => simp [hf] at h
        | some r =>
            cases hr : rest.mapM (resolveRule? D) with
            | none => simp [hf, hr] at h
            | some tail =>
                simp [hf, hr] at h
                subst ys
                simp [resolveRule_map f first r hf, ih tail hr]
  unfold resolveProgram? at success ⊢
  split at success
  · rename_i valid
    rw [ite_eq_left valid]
    exact mapRules raw rules success
  · contradiction
end DeclarationHom

end Silmaril.Logic.Egg.Source.Named
