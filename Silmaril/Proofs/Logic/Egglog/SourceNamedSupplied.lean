module

public import Silmaril.Logic.Egglog.Source.Named.Supplied.Defs

@[expose] public section
namespace Silmaril.Logic.Egglog.Source.Named
open CategoryTheory Silmaril.Logic.Institution.Examples

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem eraseTermAt_context {D : Declarations} (Γ : CheckedContext D) {s : D.LocalSort}
    (term : EQ.Term D.signature.toSignature Γ.profile s) :
    eraseTermAt (fun i => (Γ.bindings.get i).name) term = eraseTerm Γ term := by
  refine EQ.Term.rec (motive := fun _ term =>
    eraseTermAt (fun i => (Γ.bindings.get i).name) term = eraseTerm Γ term) ?_ ?_ term
  · intro i; rfl
  · intro n w s o arguments ih
    simp only [eraseTermAt, eraseTerm]
    congr 1
    exact funext ih

theorem eraseAtomAt_context {D : Declarations} (Γ : CheckedContext D)
    (atom : Core.Atom D.signature Γ.profile) :
    eraseAtomAt (fun i => (Γ.bindings.get i).name) atom = eraseAtom Γ atom := by
  cases atom with
  | equal e => simp only [eraseAtomAt, eraseAtom, eraseTermAt_context]
  | relation r arguments =>
      simp only [eraseAtomAt, eraseAtom]
      congr 1
      exact funext (fun i => eraseTermAt_context Γ (arguments i))
  | row f arguments value =>
      simp only [eraseAtomAt, eraseAtom, eraseTermAt_context]

namespace DeclarationHom

theorem eraseTermAt_map {D E : Declarations} (f : DeclarationHom D E)
    {k : Nat} {profile : Fin k → D.LocalSort} (names : Fin k → String) {s : D.LocalSort}
    (term : EQ.Term D.signature.toSignature profile s) :
    eraseTermAt names (term.map f.symbols.toHom) = eraseTermAt names term := by
  refine EQ.Term.rec (motive := fun _ term =>
    eraseTermAt names (term.map f.symbols.toHom) = eraseTermAt names term) ?_ ?_ term
  · intro i; rfl
  · intro n w s o arguments ih
    simp only [EQ.Term.map, eraseTermAt, f.constructor_name]
    congr 1
    exact funext ih

theorem eraseAtomAt_map {D E : Declarations} (f : DeclarationHom D E)
    {k : Nat} {profile : Fin k → D.LocalSort} (names : Fin k → String)
    (atom : Core.Atom D.signature profile) :
    eraseAtomAt names (atom.map f.symbols) = eraseAtomAt names atom := by
  cases atom with
  | equal e =>
      simp only [Core.Atom.map, Silmaril.Logic.Egg.Core.Equality.map, eraseAtomAt,
        eraseTermAt_map]
  | relation r arguments =>
      simp only [Core.Atom.map, eraseAtomAt, f.relation_name]
      congr 1
      exact funext (fun i => f.eraseTermAt_map names (arguments i))
  | row t arguments value =>
      simp only [Core.Atom.map, eraseAtomAt, f.function_name, eraseTermAt_map]
end DeclarationHom

/-- Erased atom lists retain every successful original source entry. -/
theorem resolveAtoms_erase {D : Declarations} (Γ : CheckedContext D)
    (raw : List RawAtom) (atoms : List (Core.Atom D.signature Γ.profile))
    (success : raw.mapM (resolveAtom? Γ) = some atoms) : atoms.map (eraseAtom Γ) = raw := by
  induction raw generalizing atoms with
  | nil => simp at success; subst atoms; rfl
  | cons first rest ih =>
      cases hf : resolveAtom? Γ first with
      | none => simp [hf] at success
      | some atom =>
          cases hr : rest.mapM (resolveAtom? Γ) with
          | none => simp [hf, hr] at success
          | some tail =>
              simp [hf, hr] at success
              subst atoms
              simp only [List.map_cons, resolveAtom_erase Γ first atom hf, ih tail hr]

/-- Generalizing the typed profile avoids hiding transport inside the parser. -/
theorem eraseRuleAt_resolve {D : Declarations} (Γ : CheckedContext D)
    (legal : ∀ binding ∈ Γ.bindings, LegalName binding.name)
    (profile : Fin Γ.bindings.length → D.LocalSort) (same : profile = Γ.profile)
    (body : List (Core.Atom D.signature profile)) (head : Core.Atom D.signature profile) :
    resolveSentence? D (.rule Γ.bindings
      (body.map (eraseAtomAt (fun i => (Γ.bindings.get i).name)))
      (eraseAtomAt (fun i => (Γ.bindings.get i).name) head)) =
      some (.rule ⟨Γ.bindings.length, profile, body, head⟩) := by
  subst profile
  have erased : (eraseAtomAt (fun i => (Γ.bindings.get i).name) :
      Core.Atom D.signature Γ.profile → RawAtom) = eraseAtom Γ :=
    funext (eraseAtomAt_context Γ)
  simpa only [erased] using eraseRule_resolve Γ legal body head

theorem eraseQueryAt_resolve {D : Declarations} (Γ : CheckedContext D)
    (legal : ∀ binding ∈ Γ.bindings, LegalName binding.name)
    (profile : Fin Γ.bindings.length → D.LocalSort) (same : profile = Γ.profile)
    (goals : List (Core.Atom D.signature profile)) :
    resolveSentence? D (.query Γ.bindings
      (goals.map (eraseAtomAt (fun i => (Γ.bindings.get i).name)))) =
      some (.query ⟨Γ.bindings.length, profile, goals⟩) := by
  subst profile
  have erased : (eraseAtomAt (fun i => (Γ.bindings.get i).name) :
      Core.Atom D.signature Γ.profile → RawAtom) = eraseAtom Γ :=
    funext (eraseAtomAt_context Γ)
  simpa only [erased] using eraseQuery_resolve Γ legal goals

/-- Successful checking proves legality for the entire ordered binder context. -/
theorem context_check_valid (D : Declarations) (context : Context) (Γ : CheckedContext D)
    (success : Context.check D context = some Γ) : Context.Valid D context := by
  unfold Context.check at success
  split at success
  · assumption
  · contradiction

namespace DeclarationHom
/-- The same raw sentence resolves naturally along an actual spelling-preserving
local signature map. This is proved from executable resolution, not an arrow field. -/
theorem resolveSentence_map {D E : Declarations} (f : DeclarationHom D E)
    (raw : RawSentence) (sentence : Core.Sentence D.signature)
    (success : resolveSentence? D raw = some sentence) :
    resolveSentence? E raw = some (sentence.map f.symbols) := by
  cases raw with
  | rule context body head =>
      cases hc : Context.check D context with
      | none => simp [resolveSentence?, hc] at success
      | some Γ =>
          cases hb : body.mapM (resolveAtom? Γ) with
          | none => simp [resolveSentence?, hc, hb] at success
          | some typedBody =>
              cases hh : resolveAtom? Γ head with
              | none => simp [resolveSentence?, hc, hb, hh] at success
              | some typedHead =>
                  simp [resolveSentence?, hc, hb, hh] at success
                  subst sentence
                  have bindings := context_check_bindings D context Γ hc
                  have legal := (context_check_valid D context Γ hc).2.1
                  have bodyRaw := resolveAtoms_erase Γ body typedBody hb
                  have headRaw := resolveAtom_erase Γ head typedHead hh
                  have complete := eraseRuleAt_resolve (f.mapContext Γ)
                    (by simpa only [mapContext, bindings] using legal)
                    (f.symbols.sorts ∘ Γ.profile) (f.mapContext_profile Γ).symm
                    (typedBody.map (Core.Atom.map f.symbols)) (typedHead.map f.symbols)
                  simpa only [mapContext, List.map_map, Function.comp_def,
                    eraseAtomAt_map, eraseAtomAt_context, bodyRaw, headRaw, bindings,
                    Core.Sentence.map, Core.Rule.map] using complete
  | query context goals =>
      cases hc : Context.check D context with
      | none => simp [resolveSentence?, hc] at success
      | some Γ =>
          cases hg : goals.mapM (resolveAtom? Γ) with
          | none => simp [resolveSentence?, hc, hg] at success
          | some typedGoals =>
              simp [resolveSentence?, hc, hg] at success
              subst sentence
              have bindings := context_check_bindings D context Γ hc
              have legal := (context_check_valid D context Γ hc).2.1
              have goalsRaw := resolveAtoms_erase Γ goals typedGoals hg
              have complete := eraseQueryAt_resolve (f.mapContext Γ)
                (by simpa only [mapContext, bindings] using legal)
                (f.symbols.sorts ∘ Γ.profile) (f.mapContext_profile Γ).symm
                (typedGoals.map (Core.Atom.map f.symbols))
              simpa only [mapContext, List.map_map, Function.comp_def,
                eraseAtomAt_map, eraseAtomAt_context, goalsRaw, bindings,
                Core.Sentence.map, Core.Query.map] using complete
end DeclarationHom

namespace AcceptedSentence

@[ext] theorem ext {D : Declarations} (first second : AcceptedSentence D)
    (bytes : first.bytes = second.bytes) (raw : first.raw = second.raw)
    (resolved : first.resolved = second.resolved) : first = second := by
  cases first
  cases second
  cases bytes
  cases raw
  cases resolved
  rfl

/-- Direct supplied-text transport retains the original body reader receipt and
uses the proved same-raw resolver naturality for its target compilation. -/
def map {D E : Declarations} (f : D ⟶ E) (sentence : AcceptedSentence D) : AcceptedSentence E where
  bytes := sentence.bytes
  raw := sentence.raw
  read_eq := sentence.read_eq
  resolved := sentence.resolved.map f.symbols
  resolve_eq := f.resolveSentence_map _ _ sentence.resolve_eq

@[simp] theorem map_bytes {D E : Declarations} (f : D ⟶ E) (sentence : AcceptedSentence D) :
    (sentence.map f).bytes = sentence.bytes := rfl

@[simp] theorem map_raw {D E : Declarations} (f : D ⟶ E) (sentence : AcceptedSentence D) :
    (sentence.map f).raw = sentence.raw := rfl

@[simp] theorem map_id {D : Declarations} (sentence : AcceptedSentence D) :
    sentence.map (𝟙 D) = sentence :=
  ext _ _ rfl rfl (Core.Sentence.map_id sentence.resolved)

@[simp] theorem map_comp {D E F : Declarations} (f : D ⟶ E) (g : E ⟶ F)
    (sentence : AcceptedSentence D) : sentence.map (f ≫ g) = (sentence.map f).map g :=
  ext _ _ rfl rfl (Core.Sentence.map_comp f.symbols g.symbols sentence.resolved)
end AcceptedSentence
end Silmaril.Logic.Egglog.Source.Named
