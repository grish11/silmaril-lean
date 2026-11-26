module

public import Silmaril.SSA.MLIR.SCF.LetIter.FixedProfile.Institution

/-! # The fixed-profile isomorphism in CoIns -/

@[expose] public section

namespace Silmaril.MLIR.SCF.LetIter.FixedProfile

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Observational (Sentence)
open Silmaril.MLIR.Arith (Env)
open Silmaril.MLIR.Pure (Eval)

variable {P : Profile} {S T : Signature}

abbrev ScalarProgram (P : Profile) (S : Signature) := (scalarPresentation P).Program S
abbrev NativeProgram (P : Profile) (S : Signature) := (nativePresentation P).Program S

/-- Encode on observational classes. -/
def encodeQ : ScalarProgram P S → NativeProgram P S :=
  Quotient.map encode (fun a b eq M input =>
    (observe_encode a M input).trans ((eq M input).trans (observe_encode b M input).symm))

/-- Decode on observational classes. -/
noncomputable def decodeQ : NativeProgram P S → ScalarProgram P S :=
  Quotient.map Native.decode (fun a b eq M input =>
    (observe_decode a M input).trans ((eq M input).trans (observe_decode b M input).symm))

@[simp] theorem decodeQ_encodeQ (q : ScalarProgram P S) : decodeQ (encodeQ q) = q :=
  Quotient.inductionOn q fun a => Quotient.sound fun M input =>
    (observe_decode (encode a) M input).trans (observe_encode a M input)

@[simp] theorem encodeQ_decodeQ (q : NativeProgram P S) : encodeQ (decodeQ q) = q :=
  Quotient.inductionOn q fun a => Quotient.sound fun M input =>
    (observe_encode a.decode M input).trans (observe_decode a M input)

theorem encodeQ_rename (f : S ⟶ T) (q : ScalarProgram P S) :
    encodeQ ((scalarPresentation P).renameQ f q) = (nativePresentation P).renameQ f (encodeQ q) :=
  Quotient.inductionOn q fun a => congrArg Quotient.mk'' (encode_rename f a).symm

theorem decodeQ_rename (f : S ⟶ T) (q : NativeProgram P S) :
    decodeQ ((nativePresentation P).renameQ f q) = (scalarPresentation P).renameQ f (decodeQ q) := by
  apply (Function.LeftInverse.injective (g := decodeQ) decodeQ_encodeQ)
  rw [encodeQ_decodeQ, encodeQ_rename, encodeQ_decodeQ]

theorem observeQ_encodeQ (q : ScalarProgram P S) (M : Eval S.op) (input : Env P.input) :
    (nativePresentation P).observeQ (encodeQ q) M input = (scalarPresentation P).observeQ q M input :=
  Quotient.inductionOn q fun a => observe_encode a M input

theorem observeQ_decodeQ (q : NativeProgram P S) (M : Eval S.op) (input : Env P.input) :
    (scalarPresentation P).observeQ (decodeQ q) M input = (nativePresentation P).observeQ q M input :=
  Quotient.inductionOn q fun a => observe_decode a M input

/-- A natural translation of observable programs gives a comorphism with
identity signature and model components. -/
def Presentation.comorphism (source target : Presentation P)
    (translate : {S : Signature} → source.Program S → target.Program S)
    (natural : ∀ {S T : Signature} (f : S ⟶ T) (q : source.Program S),
      translate (source.renameQ f q) = target.renameQ f (translate q))
    (preserves : ∀ {S : Signature} (q : source.Program S) (M : Eval S.op) (input : Env P.input),
      target.observeQ (translate q) M input = source.observeQ q M input) :
    Inst.CoHom source.inst target.inst where
  Φ := 𝟭 Signature
  ρ := {
    app S := ⟨Sentence.map translate, 𝟭 _, fun M φ => by
      let evaluator : Eval S.op := M.as
      have agree (q : source.Program S) (input : Env P.input) :
          target.observeQ (translate q) evaluator input = source.observeQ q evaluator input :=
        preserves q evaluator input
      change (∀ input, (φ.map translate).Holds (fun q => target.observeQ q evaluator input)) ↔
        ∀ input, φ.Holds (fun q => source.observeQ q evaluator input)
      cases φ <;> simp only [Sentence.map, Sentence.Holds, agree]⟩
    naturality := by
      intro S T f
      apply Room.hom_ext
      · change Sentence.map (@translate T) ∘ Sentence.map (source.renameQ f) =
          Sentence.map (target.renameQ f) ∘ Sentence.map (@translate S)
        simp only [Sentence.map_comp]
        exact congrArg Sentence.map (funext fun q => natural f q)
      · rfl }

/-- Translate both sides of each equation or refinement by encoding. -/
def scalarToNative (P : Profile) : Inst.CoHom (scalarInstitution P) (nativeInstitution P) :=
  (scalarPresentation P).comorphism (nativePresentation P) encodeQ encodeQ_rename observeQ_encodeQ

/-- Translate both sides of each equation or refinement by decoding. -/
noncomputable def nativeToScalar (P : Profile) : Inst.CoHom (nativeInstitution P) (scalarInstitution P) :=
  (nativePresentation P).comorphism (scalarPresentation P) decodeQ decodeQ_rename observeQ_decodeQ

/-- The two fixed-profile institutions are isomorphic in CoIns. Both inverse
laws are equalities of comorphisms, with the stated model reduct and
identity model components. -/
noncomputable def scalarNativeIso (P : Profile) :
    Iso (C := CoIns.{1, 0, 0, 0, 0}) (scalarInstitution P) (nativeInstitution P) where
  hom := scalarToNative P
  inv := nativeToScalar P
  hom_inv_id := by
    refine Inst.CoHom.ext rfl ?_
    apply NatTrans.ext
    funext S
    apply Room.hom_ext
    · funext φ
      change (φ.map encodeQ).map decodeQ = φ
      cases φ with
      | eq a b => exact congrArg₂ Sentence.eq (decodeQ_encodeQ a) (decodeQ_encodeQ b)
      | le a b => exact congrArg₂ Sentence.le (decodeQ_encodeQ a) (decodeQ_encodeQ b)
    · rfl
  inv_hom_id := by
    refine Inst.CoHom.ext rfl ?_
    apply NatTrans.ext
    funext S
    apply Room.hom_ext
    · funext φ
      change (φ.map decodeQ).map encodeQ = φ
      cases φ with
      | eq a b => exact congrArg₂ Sentence.eq (encodeQ_decodeQ a) (encodeQ_decodeQ b)
      | le a b => exact congrArg₂ Sentence.le (encodeQ_decodeQ a) (encodeQ_decodeQ b)
    · rfl

end Silmaril.MLIR.SCF.LetIter.FixedProfile
