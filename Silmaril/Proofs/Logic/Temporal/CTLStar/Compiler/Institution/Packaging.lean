module

public import Silmaril.Logic.Temporal.CTLStar.Compiler.Institution.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Temporal.CTLStar.Compiler.Institution
open CategoryTheory Silmaril.Logic.Institution

theorem decode_encode {S : CTLStar.Signature} (M : CTLStar.Model S) :
    decodeModel (encodeModel M) = M := by cases M; rfl

theorem encode_decode {S : CTLStar.Signature} (N : ModalMu.Model (toMuSig S)) :
    encodeModel (decodeModel N) = N := by
  cases N with
  | mk W step valuation point =>
    congr 1

theorem compile_sat {S : CTLStar.Signature} (N : ModalMu.Model (toMuSig S))
    (p : StateFormula S) : ModalMu.Sat N (compileState p) ↔ CTLStar.Sat (decodeModel N) p := by
  have h : ModalMu.Sat (encodeModel (decodeModel N)) (compileState p) ↔
      CTLStar.Sat (decodeModel N) p :=
    compileState_correct p (decodeModel N) ModalMu.emptyEnv N.point
  simpa only [encode_decode] using h

/-- Equality of the full model functors, including their action on arrows. -/
theorem discrete_model_naturality {S T : CTLStar.Signature} (f : S ⟶ T) :
    ModalMu.modelReduct (toMuMap f) ⋙ decodeDiscreteFunctor S =
      decodeDiscreteFunctor T ⋙ CTL.modelReduct f := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro M N h
  cases h.down
  rfl

theorem rich_model_naturality {S T : CTLStar.Signature} (f : S ⟶ T) :
    ModalMu.modelReduct (toMuMap f) ⋙ decodeRichFunctor S =
      decodeRichFunctor T ⋙ (Modal.reduct f).core := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro M N h
  cases h.down
  rfl

def discreteNatural : CTLStar.institution ⟶ signatureFunctor ⋙ ModalMu.institution where
  app S := ⟨compileState, decodeDiscreteFunctor S, compile_sat⟩
  naturality := by
    intro S T f
    exact Room.hom_ext (funext (fun p => (compileState_map p f).symm)) (discrete_model_naturality f)

def richNatural : CTLStar.richInstitution ⟶ signatureFunctor ⋙ ModalMu.institution where
  app S := ⟨compileState, decodeRichFunctor S, compile_sat⟩
  naturality := by
    intro S T f
    exact Room.hom_ext (funext (fun p => (compileState_map p f).symm)) (rich_model_naturality f).symm

def discreteComorphism : Inst.CoHom ⟨CTLStar.Signature, CTLStar.institution⟩
    ⟨ModalMu.Signature, ModalMu.institution⟩ := ⟨signatureFunctor, discreteNatural⟩

def richComorphism : Inst.CoHom ⟨CTLStar.Signature, CTLStar.richInstitution⟩
    ⟨ModalMu.Signature, ModalMu.institution⟩ := ⟨signatureFunctor, richNatural⟩

theorem discrete_modelExpansive : discreteComorphism.ModelExpansive := by
  intro S M
  exact ⟨encodeModel M, decode_encode M⟩

theorem rich_modelExpansive : richComorphism.ModelExpansive := by
  intro S M
  refine ⟨encodeModel ⟨M.of⟩, ?_⟩
  cases M
  rfl

theorem discrete_entails_iff (S : CTLStar.Signature) (H : Set (StateFormula S))
    (p : StateFormula S) :
    (CTLStar.institution.obj S).Entails H p ↔
      (ModalMu.institution.obj (toMuSig S)).Entails (compileState '' H) (compileState p) :=
  discreteComorphism.entails_iff discrete_modelExpansive S H p

theorem rich_entails_iff (S : CTLStar.Signature) (H : Set (StateFormula S))
    (p : StateFormula S) :
    (CTLStar.richInstitution.obj S).Entails H p ↔
      (ModalMu.institution.obj (toMuSig S)).Entails (compileState '' H) (compileState p) :=
  richComorphism.entails_iff rich_modelExpansive S H p

theorem discrete_satisfiable_iff (S : CTLStar.Signature) (H : Set (StateFormula S)) :
    (∃ M : CTLStar.Model S, ∀ p ∈ H, CTLStar.Sat M p) ↔
      ∃ N : ModalMu.Model (toMuSig S), ∀ q ∈ compileState '' H, ModalMu.Sat N q := by
  constructor
  · rintro ⟨M, h⟩
    refine ⟨encodeModel M, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    exact (compileState_correct p M ModalMu.emptyEnv M.toModal.point).mpr (h p hp)
  · rintro ⟨N, h⟩
    exact ⟨decodeModel N, fun p hp => (compile_sat N p).mp (h _ ⟨p, hp, rfl⟩)⟩

theorem rich_satisfiable_iff (S : CTLStar.Signature) (H : Set (StateFormula S)) :
    (∃ M : CTLStar.RichModel S, ∀ p ∈ H, CTLStar.Sat ⟨M.of⟩ p) ↔
      ∃ N : ModalMu.Model (toMuSig S), ∀ q ∈ compileState '' H, ModalMu.Sat N q :=
  (CTLStar.rich_satisfiable_iff S H).trans (discrete_satisfiable_iff S H)

theorem discrete_unsatisfiable_iff (S : CTLStar.Signature) (H : Set (StateFormula S)) :
    (¬ ∃ M : CTLStar.Model S, ∀ p ∈ H, CTLStar.Sat M p) ↔
      ¬ ∃ N : ModalMu.Model (toMuSig S), ∀ q ∈ compileState '' H, ModalMu.Sat N q :=
  not_congr (discrete_satisfiable_iff S H)

theorem rich_unsatisfiable_iff (S : CTLStar.Signature) (H : Set (StateFormula S)) :
    (¬ ∃ M : CTLStar.RichModel S, ∀ p ∈ H, CTLStar.Sat ⟨M.of⟩ p) ↔
      ¬ ∃ N : ModalMu.Model (toMuSig S), ∀ q ∈ compileState '' H, ModalMu.Sat N q :=
  not_congr (rich_satisfiable_iff S H)

end Silmaril.Logic.Temporal.CTLStar.Compiler.Institution
