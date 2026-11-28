module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Categorical.WeakTree.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Categorical.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.FlatLetCase.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Model.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Kleisli.Thms
import Silmaril.Raw.SSA.Isotope.Morphism.CaseIter.Monadic

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Categorical.WeakTree

open CategoryTheory CategoryTheory.Limits
open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Acyclic
open Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.WeakTree
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Categorical
  (ctxObj labelObj labelInject unpackLabelExit unpackLabel packLabel packedLabelInject
    singletonLabelPayload)
open LambdaSSA.Semantics.Interaction (Transfer)
open LambdaSSA.Semantics.Interaction.Typed
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LambdaSSA.Semantics.Monadic (LabelValue)
open Silmaril.Isotope.Semantics (encodeValue)
open LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open LetIter.Semantics.Categorical (envObj boundLookup)
open LetCase.LocallyNameless (Derivation)
open Morphism.CaseSSA (erase)
open Positional.Capture.Reverse (CheckedTable)
open Region (packedExitType packedExitValue)

universe u v

variable {κ : Type (u + 1)} [AtomValues κ] {Φ : Type v} [HasTy Φ (Ty κ)] [HasEff Φ Bool]
  {Events : Type u → Type u}

attribute [local instance] typeModel categoricalInstructions

local notation "Atoms" => AtomValues.carrier (κ := κ)
local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty κ))
local notation "K" => typeJ (m := ModelTree Events)
local notation "T" => LambdaSSA.Semantics.Categorical.ofMonadicTypeModel (τ := Ty κ)

/-! ## The two presentations of the structural type model -/

omit [HasTy Φ (Ty κ)] [HasEff Φ Bool] in
theorem types_eq_proof :
    T = LetIter.Semantics.Categorical.ofTypeModel (Ty.denote Atoms) := by
  have initial : ∀ a b : IsInitial (Ty.denote Atoms (Silmaril.empty : Ty κ)), a = b :=
    fun a b => Subsingleton.elim a b
  exact congrArg (fun e : IsInitial (Ty.denote Atoms (Silmaril.empty : Ty κ)) =>
    (LetIter.Semantics.Categorical.TypeModel.mk (Ty.denote Atoms)
      (LetIter.Semantics.Categorical.ofTypeModel (Ty.denote Atoms)).productIso
      (LetIter.Semantics.Categorical.ofTypeModel (Ty.denote Atoms)).unitIso
      (LetIter.Semantics.Categorical.ofTypeModel (Ty.denote Atoms)).coprodIso e :
        LetIter.Semantics.Categorical.TypeModel (Ty κ) (Type (u + 1)))) (initial _ _)

/-! ## The LetCase arrow computes the erased weak tree -/

section LetCase

variable {n : Nat} {β : BoundCtx (Ty κ) n} {t : LetCase.LocallyNameless.Tm Empty Φ n} {A : Ty κ}

/-- The comparison at any presentation of the type model that is equal
to the structural one, with the same primitive arrows and encoding. -/
private theorem letCase_tree_at (M : Model (κ := κ) Events Φ)
    (types : LetIter.Semantics.Categorical.TypeModel (Ty κ) (Type (u + 1)))
    (same : types = LetIter.Semantics.Categorical.ofTypeModel (Ty.denote Atoms))
    (calls : LetIter.Semantics.Categorical.InstructionModel K types Φ)
    (sameCalls : ∀ f, HEq (calls.denote f)
      ((LetIter.Semantics.Categorical.ofInstructionModel (Ty.denote Atoms)
        (⟨fun f x => M.instructions.denote f x⟩ :
          Isotope.Semantics.InstructionModel (Ty.denote Atoms) Φ (ModelTree Events))).denote f))
    (enc : ∀ A, types.obj A → Value (Sigma Atoms))
    (sameEnc : ∀ A, HEq (enc A) (encodeValue Atoms A))
    (d : Derivation Φ Γ₀ β t A) (x : envObj types Γ₀ β) (env : Env (Sigma Atoms))
    (agree : ∀ i, env i.val = enc (β.get i) (boundLookup types i x.2)) :
    ((show ModelTree Events (types.obj A) from
        (LetCase.Semantics.Categorical.denote K types d).of x) >>= fun a => pure (enc A a)) =
      LambdaSSA.Semantics.Interaction.term M.raw env (erase t) := by
  subst same
  have encoded : enc = fun A => encodeValue Atoms A := funext fun A => eq_of_heq (sameEnc A)
  subst encoded
  have called : calls = LetIter.Semantics.Categorical.ofInstructionModel (Ty.denote Atoms)
      (⟨fun f x => M.instructions.denote f x⟩ :
        Isotope.Semantics.InstructionModel (Ty.denote Atoms) Φ (ModelTree Events)) := by
    cases calls
    congr
    funext f
    exact eq_of_heq (sameCalls f)
  subst called
  let _ := LetIter.Semantics.Categorical.ofInstructionModel (Ty.denote Atoms)
    (⟨fun f x => M.instructions.denote f x⟩ :
      Isotope.Semantics.InstructionModel (Ty.denote Atoms) Φ (ModelTree Events))
  rw [← Native.denote_caseIter K _ d]
  have direct := LetIter.Semantics.Categorical.denoteOfType_eq (Ty.denote Atoms)
    (⟨fun f x => M.instructions.denote f x⟩ :
      Isotope.Semantics.InstructionModel (Ty.denote Atoms) Φ (ModelTree Events))
    (Silmaril.Isotope.Morphism.CaseIter.derivation d) x.1 x.2
  rw [Silmaril.Isotope.Morphism.CaseIter.denote_derivation] at direct
  have free : LetIter.Semantics.Categorical.freeEnv (Ty.denote Atoms) (Γ := Γ₀) x.1 =
      fun z => z.elim := funext fun z => z.elim
  rw [free] at direct
  rw [← FlatLetCase.denote_tree _ M.raw M.compatible d
    (LetIter.Semantics.Categorical.boundEnv (Ty.denote Atoms) x.2) env agree]
  exact congrArg (fun tree => tree >>= fun a => pure (encodeValue Atoms A a)) direct

theorem letCase_tree_proof (M : Model (κ := κ) Events Φ) (d : Derivation Φ Γ₀ β t A)
    (x : envObj T Γ₀ β) (env : Env (Sigma Atoms))
    (agree : ∀ i, env i.val = encodeValue Atoms (β.get i) (boundLookup T i x.2)) :
    let _ := M.instructions
    ((show ModelTree Events (Ty.denote Atoms A) from
        (LetCase.Semantics.Categorical.denote K T d).of x) >>= fun a =>
          pure (encodeValue Atoms A a)) =
      LambdaSSA.Semantics.Interaction.term M.raw env (erase t) :=
  let _ := M.instructions
  letCase_tree_at M T types_eq_proof categoricalInstructions (fun _ => HEq.rfl)
    (fun A => encodeValue Atoms A) (fun _ => HEq.rfl) d x env agree

end LetCase

/-! ## Ordered exits and their packed value -/

section Exits

omit [HasTy Φ (Ty κ)] [HasEff Φ Bool]

private theorem encode_cast {A B : Ty κ} (eq : A = B) (a : Ty.denote Atoms A) :
    encodeValue Atoms B (eq ▸ a) = encodeValue Atoms A a := by cases eq; rfl

private theorem encodeLabel_inject {L : LCtx (Ty κ)} {A : Ty κ} (i : Nat) (h : At L i A)
    (a : Ty.denote Atoms A) :
    encodeLabel L (LabelValue.inject i h a) = (i, encodeValue Atoms A a) := by
  unfold encodeLabel
  rw [LabelValue.toSigma_inject]
  obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp h
  change (i, encodeValue Atoms L[i] (he.symm ▸ a)) = _
  rw [encode_cast]

/-- Every ordered exit is the injection of a payload at a position. -/
private theorem label_cases : (L : LCtx (Ty κ)) → (x : LabelValue L) →
    ∃ (i : Nat) (A : Ty κ) (h : At L i A) (a : Ty.denote Atoms A), x = LabelValue.inject i h a
  | [], x => nomatch x
  | A :: _, Sum.inl a => ⟨0, A, rfl, a, rfl⟩
  | _ :: L, Sum.inr x => by
      obtain ⟨i, A, h, a, rfl⟩ := label_cases L x
      exact ⟨i + 1, A, h, a, rfl⟩

/-- The encoding of a payload in the packed sum is the packed value of
its encoding. -/
private theorem encode_packedLabelInject : {L : LCtx (Ty κ)} → (i : Nat) → {A : Ty κ} →
    (h : At L i A) → (a : Ty.denote Atoms A) →
    encodeValue Atoms (packedExitType L) (packedLabelInject T i h a) =
      packedExitValue i (encodeValue Atoms A a)
  | [], _, _, h, _ => by simp [At] at h
  | B :: L, 0, A, h, a => by
      obtain rfl : B = A := by simpa [At] using h
      have left := ConcreteCategory.congr_hom
        (Types.binaryCoproductIso_inl_comp_hom (Ty.denote Atoms B)
          (Ty.denote Atoms (packedExitType L))) a
      simp only [packedLabelInject, eqToHom_refl, Category.id_comp]
      change encodeValue Atoms (Ty.coprod B (packedExitType L))
        ((coprod.inl ≫ (Types.binaryCoproductIso (Ty.denote Atoms B)
          (Ty.denote Atoms (packedExitType L))).hom) a) = _
      rw [left]
      rfl
  | B :: L, i + 1, A, h, a => by
      have step := encode_packedLabelInject (L := L) i h a
      have right := ConcreteCategory.congr_hom
        (Types.binaryCoproductIso_inr_comp_hom (Ty.denote Atoms B)
          (Ty.denote Atoms (packedExitType L))) (packedLabelInject T i h a)
      simp only [packedLabelInject]
      change encodeValue Atoms (Ty.coprod B (packedExitType L))
        ((coprod.inr ≫ (Types.binaryCoproductIso (Ty.denote Atoms B)
          (Ty.denote Atoms (packedExitType L))).hom) (packedLabelInject T i h a)) = _
      rw [right]
      change Value.inr (encodeValue Atoms (packedExitType L) (packedLabelInject T i h a)) = _
      rw [step]
      rfl

set_option backward.isDefEq.respectTransparency false in
private theorem singleton_payload (A : Ty κ) :
    labelInject T 0 (rfl : At [A] 0 A) ≫ singletonLabelPayload T A = 𝟙 _ := by
  rw [LambdaSSA.Semantics.Categorical.labelInject_eq_sigma]
  rw [Category.assoc, singletonLabelPayload, Sigma.ι_comp_desc]
  simp

theorem unpack_packed_proof (L : LCtx (Ty κ)) (v : Ty.denote Atoms (packedExitType L)) :
    FiniteCFG.packedTreeOutput (encodeLabel L ((LabelValue.categoricalEquiv L).symm
        ((labelInject T (L := [packedExitType L]) 0 rfl ≫ unpackLabelExit T L) v))) =
      (0, encodeValue Atoms (packedExitType L) v) := by
  have unpacked : labelInject T (L := [packedExitType L]) 0 rfl ≫ unpackLabelExit T L =
      unpackLabel T L := by
    rw [unpackLabelExit, ← Category.assoc, singleton_payload, Category.id_comp]
  rw [unpacked]
  obtain ⟨i, A, h, a, eq⟩ :=
    label_cases L ((LabelValue.categoricalEquiv L).symm (unpackLabel T L v))
  have out : unpackLabel T L v = labelInject T i h a := by
    rw [← LabelValue.categoricalEquiv_inject i h a, ← eq, Equiv.apply_symm_apply]
  have packed : packedLabelInject T i h a = v := by
    have pack := ConcreteCategory.congr_hom
      (LambdaSSA.Semantics.Categorical.labelInject_packLabel T h) a
    have inverse := ConcreteCategory.congr_hom
      (LambdaSSA.Semantics.Categorical.unpackLabel_packLabel T L) v
    change packLabel T L (labelInject T i h a) = packedLabelInject T i h a at pack
    change packLabel T L (unpackLabel T L v) = v at inverse
    rw [← pack, ← out, inverse]
  rw [eq, encodeLabel_inject, ← packed, encode_packedLabelInject]
  rfl

end Exits

/-! ## The arrow of a checked table -/

section Arrow

variable {d : Nat} {β : BoundCtx (Ty κ) d} {L : LCtx (Ty κ)}

omit [AtomValues κ] in
/-- Three pure observations of a tree compare by their composites. -/
private theorem observe {A B C D E : Type (u + 1)} (x : ModelTree Events A) (f : A → B)
    (g : B → C) (h : C → D) (e : A → E) (k : E → D) (eq : ∀ a, h (g (f a)) = k (e a)) :
    (((x >>= fun a => pure (f a)) >>= fun b => pure (g b)) >>= fun c => pure (h c)) =
      ((x >>= fun a => pure (e a)) >>= fun b => pure (k b)) := by
  simp only [bind_assoc, pure_bind, eq]

theorem arrow_packed_proof (M : Model (κ := κ) Events Φ) (c : CheckedTable Φ β L)
    (y : ctxObj T β.toList) (env : Env (Sigma Atoms))
    (agree : ∀ i, env i.val =
      encodeValue Atoms (β.get i) (boundLookup T i (contextMap T β y).2)) :
    (exitTree L (arrow M c) y >>= fun out => pure (FiniteCFG.packedTreeOutput out)) =
      (LambdaSSA.Semantics.Interaction.term M.raw env (erase c.toLetCase.1) >>= fun value =>
        pure (0, value)) := by
  let _ := M.instructions
  let _ := regionTypingCoherent M.raw M.compatible
  have law := Positional.Capture.Table.toLetCase_denote K T c.table c.checked 0 c.entry
  have tree := letCase_tree_proof M c.toLetCase.2 (contextMap T β y) env agree
  have value : (show ModelTree Events (labelObj T L) from
        (LambdaSSA.Semantics.Categorical.denoteRegion K T c.toSSA_hasType).of y) =
      ((show ModelTree Events (Ty.denote Atoms (packedExitType L)) from
        (LetCase.Semantics.Categorical.denote K T c.toLetCase.2).of (contextMap T β y)) >>=
          fun v => pure ((labelInject T (L := [packedExitType L]) 0 rfl ≫
            unpackLabelExit T L) v)) := by
    have applied := congrArg (fun f => (show ModelTree Events _ from f.of y)) law
    simp only [Kleisli.Type.comp_of_eq_kleisliRight, Bind.kleisliRight, mapTree_of,
      pure_bind] at applied
    exact applied
  rw [← tree]
  change (((show ModelTree Events (labelObj T L) from
      (LambdaSSA.Semantics.Categorical.denoteRegion K T c.toSSA_hasType).of y) >>= fun out =>
        pure (encodeLabel L ((LabelValue.categoricalEquiv L).symm out))) >>= fun out =>
          pure (FiniteCFG.packedTreeOutput out)) = _
  rw [value]
  exact observe _ _ _ _ _ _ (unpack_packed_proof L)

omit [AtomValues κ] in
/-- A pure injective observation determines the tree. -/
private theorem observe_injective {A B : Type (u + 1)} (f : A → B)
    (injective : Function.Injective f) (a b : ModelTree Events A)
    (eq : (a >>= fun x => pure (f x)) = (b >>= fun x => pure (f x))) : a = b := by
  classical
  let decode (y : B) : ModelTree Events A := if h : ∃ x, f x = y then pure h.choose else a
  have retract (x : A) : decode (f x) = pure x := by
    have found : ∃ z, f z = f x := ⟨x, rfl⟩
    simp only [decode, found, ↓reduceDIte]
    exact congrArg pure (injective found.choose_spec)
  have decoded := congrArg (fun tree => tree >>= decode) eq
  simpa only [bind_assoc, pure_bind, retract, bind_pure] using decoded

private theorem packedExitValue_inj {α : Type (u + 1)} {i j : Nat} {a b : Value α} :
    packedExitValue i a = packedExitValue j b → i = j ∧ a = b := by
  induction i generalizing j with
  | zero => cases j <;> simp [packedExitValue]
  | succ i ih =>
    cases j with
    | zero => simp [packedExitValue]
    | succ j =>
      intro h
      obtain ⟨rfl, rfl⟩ := ih (Value.inr.inj h)
      exact ⟨rfl, rfl⟩

theorem packedTreeOutput_injective_proof {α : Type (u + 1)} :
    Function.Injective (FiniteCFG.packedTreeOutput (α := α)) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ eq
  obtain ⟨rfl, rfl⟩ := packedExitValue_inj (congrArg Prod.snd eq)
  rfl

omit [AtomValues κ] in
theorem packed_injective_proof {α : Type (u + 1)} (a b : ModelTree Events (Transfer α))
    (eq : (a >>= fun out => pure (FiniteCFG.packedTreeOutput out)) =
      (b >>= fun out => pure (FiniteCFG.packedTreeOutput out))) : a = b :=
  observe_injective FiniteCFG.packedTreeOutput packedTreeOutput_injective_proof a b eq

theorem arrow_ordered_proof (M : Model (κ := κ) Events Φ) (c : CheckedTable Φ β L)
    (y : ctxObj T β.toList) (env : Env (Sigma Atoms))
    (agree : ∀ i, env i.val =
      encodeValue Atoms (β.get i) (boundLookup T i (contextMap T β y).2))
    (ordered : ModelTree Events (Transfer (Sigma Atoms)))
    (readback : LambdaSSA.Semantics.Interaction.term M.raw env (erase c.toLetCase.1) =
      ordered >>= fun out => pure (packedExitValue out.1 out.2)) :
    exitTree L (arrow M c) y = ordered := by
  apply packed_injective_proof
  rw [arrow_packed_proof M c y env agree, readback]
  simp only [bind_assoc, pure_bind]
  rfl

end Arrow

end Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Categorical.WeakTree
