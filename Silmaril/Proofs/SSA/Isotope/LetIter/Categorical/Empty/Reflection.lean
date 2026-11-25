module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Empty.Defs
import Silmaril.SSA.Isotope.Bridge.Packing.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Empty.Sequencing
import Silmaril.SSA.Thesis.Monadic.Thms
import Silmaril.Semantics.ElgotMonads.Thms

noncomputable section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.AbortCounterexample

open Silmaril.Thesis.LambdaIter (Sig)
open Silmaril.Thesis.LambdaIter.LocallyNameless
open Silmaril.Thesis.LambdaIter.LocallyNameless.Tm
open Silmaril.Thesis.LambdaIter.LocallyNameless.Syntax
open Silmaril.Thesis.LambdaIter.Syn.SynCat

local instance : Silmaril.HasTy Bool (Ty Empty) where
  src _ := .unit
  trg _ := .empty

local instance : Silmaril.HasEff Bool Bool where
  eff _ := true

private abbrev S : Sig := Syntactic.signature (τ := Ty Empty) (Φ := Bool) false
local instance : Silmaril.Thesis.LambdaIter.TypeFormers (Ty Empty) := S.formers
local instance : Silmaril.Thesis.LambdaIter.HasTy Bool (Ty Empty) := S.hasTy
local instance : Silmaril.Thesis.LambdaIter.HasEff Bool Bool := S.hasEff

-- Under an empty elimination, reroute every instruction to the false exception.
-- Both instructions are impure, so this translation fixes all pure substituends.
@[simp] private def mask : {n : Nat} → Bool → Tm Empty Bool n → Tm Empty Bool n
  | _, _, .fv i => .fv i
  | _, _, .bv i => .bv i
  | _, mode, .op f a => .op (if mode then false else f) (mask mode a)
  | _, mode, .let₁ a b => .let₁ (mask mode a) (mask mode b)
  | _, _, .unit => .unit
  | _, mode, .pair a b => .pair (mask mode a) (mask mode b)
  | _, mode, .let₂ a b => .let₂ (mask mode a) (mask mode b)
  | _, mode, .inl a => .inl (mask mode a)
  | _, mode, .inr a => .inr (mask mode a)
  | _, mode, .case a l r => .case (mask mode a) (mask mode l) (mask mode r)
  | _, _, .abort a => .abort (mask true a)
  | _, mode, .iter a b => .iter (mask mode a) (mask mode b)

private theorem mask_rename {n m : Nat} (t : Tm Empty Bool n) (ρ : Fin n → Fin m)
    (mode : Bool) : mask mode (rename ρ t) = rename ρ (mask mode t) := by
  induction t generalizing m mode <;> cases mode <;> simp_all

@[simp] private theorem mask_lift {n : Nat} (t : Tm Empty Bool n) (mode : Bool) :
    mask mode (lift t) = lift (mask mode t) := mask_rename t _ mode

@[simp] private theorem mask_underBinder {n : Nat} (t : Tm Empty Bool (n + 1)) (mode : Bool) :
    mask mode (underBinder t) = underBinder (mask mode t) := mask_rename t _ mode

@[simp] private theorem mask_underTwoBinders {n : Nat} (t : Tm Empty Bool (n + 2)) (mode : Bool) :
    mask mode (underTwoBinders t) = underTwoBinders (mask mode t) := mask_rename t _ mode

private theorem mask_eq_of_pure {n : Nat} {t : Tm Empty Bool n} (h : Pure false t) (mode : Bool) :
    mask mode t = t := by
  induction h generalizing mode with
  | op h _ _ => cases (show true = false from h)
  | _ => cases mode <;> simp_all

private theorem pure_upSub {n m : Nat} {σ : Fin n → Tm Empty Bool m}
    (h : ∀ i, Pure false (σ i)) : ∀ i, Pure false (upSub σ i) :=
  Fin.cases .bv (fun i => (h i).rename Fin.succ)

private theorem mask_bsubst {n m : Nat} (t : Tm Empty Bool n) (σ : Fin n → Tm Empty Bool m)
    (h : ∀ i, Pure false (σ i)) (mode : Bool) :
    mask mode (bsubst σ t) = bsubst σ (mask mode t) := by
  induction t generalizing m mode with
  | bv i => exact mask_eq_of_pure (h i) mode
  | let₁ a b iha ihb | iter a b iha ihb =>
      simp [iha σ h, ihb (upSub σ) (pure_upSub h)]
  | let₂ a b iha ihb =>
      simp [iha σ h, ihb (upSub (upSub σ)) (pure_upSub (pure_upSub h))]
  | case e l r ihe ihl ihr =>
      simp [ihe σ h, ihl (upSub σ) (pure_upSub h), ihr (upSub σ) (pure_upSub h)]
  | _ => cases mode <;> simp_all

private theorem mask_instantiate {n : Nat} (b : Tm Empty Bool (n + 1)) {a : Tm Empty Bool n}
    (ha : Pure false a) (mode : Bool) :
    mask mode (instantiate b a) = instantiate (mask mode b) (mask mode a) := by
  rw [mask_eq_of_pure ha, instantiate, instantiate]
  exact mask_bsubst b _ (Fin.cases ha (fun _ => .bv)) mode

private def mask_typing {n : Nat} {β : Silmaril.Thesis.LambdaIter.LocallyNameless.BoundCtx (Ty Empty) n} {t : Tm Empty Bool n} {A : Ty Empty}
    (h : HasType Bool .nil β t A) (mode : Bool) : HasType Bool .nil β (mask mode t) A := by
  induction h generalizing mode with
  | fv h => exact .fv h
  | bv => exact .bv
  | op _ ih => exact .op (ih mode)
  | let₁ _ _ iha ihb => exact .let₁ (iha mode) (ihb mode)
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair (iha mode) (ihb mode)
  | let₂ _ _ iha ihb => exact .let₂ (iha mode) (ihb mode)
  | inl _ ih => exact .inl (ih mode)
  | inr _ ih => exact .inr (ih mode)
  | case _ _ _ ihe ihl ihr => exact .case (ihe mode) (ihl mode) (ihr mode)
  | abort _ ih => exact .abort (ih true)
  | iter _ _ iha ihb => exact .iter (iha mode) (ihb mode)

private theorem mask_axiom {n : Nat} {t t' : Tm Empty Bool n} (mode : Bool)
    (h : CoreAxiom false t t') : CoreAxiom false (mask mode t) (mask mode t') := by
  cases h with
  | structural h =>
    apply CoreAxiom.structural
    cases h with
    | letBeta hp =>
      rw [mask_instantiate _ hp]
      exact .letBeta (by rwa [mask_eq_of_pure hp])
    | letEta => exact .letEta _
    | unitEta => exact .unitEta _
    | pairBeta => simpa only [mask, mask_lift] using StructuralAxiom.pairBeta (pureEff := false) _ _ _
    | pairEta => exact .pairEta _
    | caseBetaL => exact .caseBetaL _ _ _
    | caseBetaR => exact .caseBetaR _ _ _
    | caseEta => exact .caseEta _
    | emptyInitial => exact .emptyInitial _ _ _
  | sequencing h =>
    apply CoreAxiom.sequencing
    cases h with
    | bindOp a c =>
      simpa only [mask, mask_underBinder] using
        SequencingAxiom.bindOp (pureEff := false) (mask mode a) (mask mode c)
    | bindLet a b c =>
      simpa only [mask, mask_underBinder] using
        SequencingAxiom.bindLet (pureEff := false) (mask mode a) (mask mode b) (mask mode c)
    | bindLetPair e c d =>
      simpa only [mask, mask_underBinder] using
        SequencingAxiom.bindLetPair (pureEff := false) (mask mode e) (mask mode c) (mask mode d)
    | bindLetCase e l r d =>
      simpa only [mask, mask_underBinder] using
        SequencingAxiom.bindLetCase (pureEff := false) (mask mode e) (mask mode l) (mask mode r) (mask mode d)
    | bindPair a c =>
      simpa only [mask, mask_underTwoBinders] using
        SequencingAxiom.bindPair (pureEff := false) (mask mode a) (mask mode c)
    | bindCase e l r =>
      simpa only [mask, mask_underBinder] using
        SequencingAxiom.bindCase (pureEff := false) (mask mode e) (mask mode l) (mask mode r)
  | iteration h =>
    apply CoreAxiom.iteration
    cases h with
    | fixpoint a b =>
      simpa only [mask, mask_underBinder] using
        IterationAxiom.fixpoint (pureEff := false) (mask mode a) (mask mode b)
    | naturality a b c =>
      simpa only [mask, mask_underBinder] using
        IterationAxiom.naturality (pureEff := false) (mask mode a) (mask mode b) (mask mode c)
    | codiagonal a b =>
      simpa only [mask, mask_underBinder] using
        IterationAxiom.codiagonal (pureEff := false) (mask mode a) (mask mode b)
    | iterBind a b =>
      simpa only [mask, mask_underBinder] using
        IterationAxiom.iterBind (pureEff := false) (mask mode a) (mask mode b)

private theorem mask_eqv {n : Nat} {β : Silmaril.Thesis.LambdaIter.LocallyNameless.BoundCtx (Ty Empty) n} {t t' : Tm Empty Bool n}
    {A : Ty Empty} (e : Eqv false .nil β t t' A) (mode : Bool) :
    Eqv false .nil β (mask mode t) (mask mode t') A := by
  induction e generalizing mode with
  | refl ht => exact .refl (mask_typing ht mode)
  | symm _ ih => exact .symm (ih mode)
  | trans _ _ ih ih' => exact .trans (ih mode) (ih' mode)
  | op _ ih => exact .op (ih mode)
  | let₁ _ _ ih ih' => exact .let₁ (ih mode) (ih' mode)
  | unit => exact .unit
  | pair _ _ ih ih' => exact .pair (ih mode) (ih' mode)
  | let₂ _ _ ih ih' => exact .let₂ (ih mode) (ih' mode)
  | inl _ ih => exact .inl (ih mode)
  | inr _ ih => exact .inr (ih mode)
  | case _ _ _ ihe ihl ihr => exact .case (ihe mode) (ihl mode) (ihr mode)
  | abort _ ih => exact .abort (ih true)
  | iter _ _ ih ih' => exact .iter (ih mode) (ih' mode)
  | ax ax hl hr => exact .ax (mask_axiom mode ax) (mask_typing hl mode) (mask_typing hr mode)
  | uniformity ha hh hp hb hb' _ ih =>
      have square := ih mode
      rw [mask_instantiate _ hp] at square
      simp only [mask, mask_underBinder] at square ⊢
      have pureMapped : Pure false (mask mode _) := (mask_eq_of_pure hp mode).symm ▸ hp
      exact Eqv.uniformity (mask_typing ha mode) (mask_typing hh mode) pureMapped
        (mask_typing hb mode) (mask_typing hb' mode) square

open Silmaril.Thesis.LambdaIter (InjectiveFormers)
open Silmaril.Thesis.LambdaIter.Monadic

private abbrev Errors := ExceptT Bool Part

local instance : Silmaril.Thesis.Elgot.Iterate Errors where
  iter := Silmaril.Elgot.iter (m := Errors)

local instance : Silmaril.Thesis.Elgot.LawfulElgotMonad Errors where
  fixpoint := Silmaril.Elgot.LawfulElgotMonad.fixpoint (m := Errors)
  naturality := Silmaril.Elgot.LawfulElgotMonad.naturality (m := Errors)
  codiagonal := Silmaril.Elgot.LawfulElgotMonad.codiagonal (m := Errors)
  uniformity := Silmaril.Elgot.LawfulElgotMonad.uniformity (m := Errors)

local instance : InjectiveFormers (Ty Empty) where
  tensor_inj h := by
    cases h
    exact ⟨rfl, rfl⟩
  coprod_inj h := by
    cases h
    exact ⟨rfl, rfl⟩
  tensor_ne_coprod h := by cases h

private def interp : Ty Empty → Type
  | .base x => x.elim
  | .product A B => interp A × interp B
  | .unit => Unit
  | .coprod A B => interp A ⊕ interp B
  | .empty => Empty

private def exception {A : Type} (f : Bool) : Errors A := ExceptT.mk (Part.some (.error f))

private def model : Model S Errors where
  interp := interp
  denoteInstr f _ := exception f
  denotePureInstr _ hf := Bool.noConfusion (show true = false from hf)
  denoteInstr_pure _ hf _ := Bool.noConfusion (show true = false from hf)
  tensorEquiv _ _ := Equiv.refl _
  unitEquiv := Equiv.refl _
  coprodEquiv _ _ := Equiv.refl _
  emptyEquiv := Equiv.refl _

private abbrev scrutinee : Tm Empty Bool 0 := .op true .unit
private abbrev direct : Tm Empty Bool 0 := .abort scrutinee
private abbrev sequenced : Tm Empty Bool 0 := .let₁ scrutinee (.abort (.bv 0))

private def scrutineeType (f : Bool) :
    HasType Bool (Silmaril.Thesis.LambdaIter.Ctx.nil : Silmaril.Thesis.LambdaIter.Ctx Empty (Ty Empty))
      .nil (.op f .unit) (Ty.empty : Ty Empty) :=
  .op .unit

private theorem abort_equation_unprovable : ¬ Eqv false .nil .nil direct sequenced (Ty.unit : Ty Empty) := by
  intro h
  have eq := Silmaril.Thesis.LambdaIter.Monadic.sound (S := S) model (mask_eqv h false)
    (HasType.abort (C := Ty.unit) (scrutineeType false))
    (HasType.let₁ (scrutineeType true) (HasType.abort (C := Ty.unit) .newest)) PUnit.unit
  let e₀ : Errors Empty := pure () >>= fun _ => exception false
  let e₁ : Errors Empty := pure () >>= fun _ => exception true
  change e₀ >>= (fun z => z.elim : Empty → Errors Unit) =
    e₁ >>= (fun z => pure z >>= fun w => w.elim : Empty → Errors Unit) at eq
  have exception_bind {A B : Type} (f : Bool) (g : A → Errors B) :
      exception f >>= g = exception f := by
    change Part.bind (Part.some (Except.error f)) (ExceptT.bindCont g) =
      Part.some (Except.error f)
    exact Part.bind_some _ _
  dsimp only [e₀, e₁] at eq
  rw [pure_bind, pure_bind, exception_bind, exception_bind] at eq
  have errors := congrArg ExceptT.run eq
  exact Bool.noConfusion (Except.error.inj (Part.some_injective errors))

private def nativeScrutinee :
    LocallyNameless.Derivation Bool (Ctx.nil : Ctx Empty (Ty Empty)) .nil (.op true .unit) Ty.empty :=
  .op .unit

private theorem native_denote_eq :
    Syntactic.denoteInSyntax false (.abort (C := Ty.unit) nativeScrutinee) =
      Syntactic.denoteInSyntax false (.let₁ nativeScrutinee (.abort (C := Ty.unit) (.bv (ι := 0)))) := by
  let _ := Syntactic.instructionModel (τ := Ty Empty) (Φ := Bool) false
  exact (denote_let_abort_proof (values S) (Syntactic.typeModel (Φ := Bool) false) nativeScrutinee Ty.unit).symm

public theorem closedReflection_fails_proof : ¬ Syntactic.ClosedReflection := by
  intro reflection
  have eq := reflection false (.abort (C := Ty.unit) nativeScrutinee)
    (.let₁ nativeScrutinee (.abort (C := Ty.unit) (.bv (ι := 0)))) native_denote_eq
  apply abort_equation_unprovable
  exact (Bridge.equiv_iff (Bridge.TypeCompat.canonical (Ty Empty))
    (Bridge.InstrCompat.canonical Bool (Ty Empty)) (Bridge.EffCompat.canonical Bool Bool) false).mp eq

public theorem closedReification_fails_proof : ¬ Syntactic.ClosedReification := by
  intro reify
  let h := HasType.abort (C := (Ty.unit : Ty Empty)) (scrutineeType true)
  let k := HasType.let₁ (scrutineeType true) (HasType.abort (C := (Ty.unit : Ty Empty)) .newest)
  have a := reify false (.abort (C := Ty.unit) nativeScrutinee) h
  have b := reify false (.let₁ nativeScrutinee (.abort (C := Ty.unit) (.bv (ι := 0)))) k
  rw [native_denote_eq] at a
  exact abort_equation_unprovable ((packedArrow_eq_iff h k).mp (a.symm.trans b))

end Silmaril.Isotope.LetIter.Semantics.Categorical.AbortCounterexample
