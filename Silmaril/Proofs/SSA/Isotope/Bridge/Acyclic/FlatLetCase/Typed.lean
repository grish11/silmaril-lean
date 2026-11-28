module

public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Defs
public import Silmaril.Raw.SSA.Isotope.LetCase.Semantics.Monadic

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.FlatLetCase

open Silmaril.Isotope Silmaril.Isotope.Semantics
open LetCase.LocallyNameless (Derivation Tm)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (Primitive term)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues Compatible ModelTree)
open Morphism.CaseSSA (erase)

universe u v
variable {κ : Type (u + 1)} [AtomValues κ] {Events : Type u → Type u}
  {Φ : Type v} [HasTy Φ (Ty κ)]

local notation "C" => AtomValues.carrier (κ := κ)

private theorem snoc_agrees {n : Nat} {β : BoundCtx (Ty κ) n} {A : Ty κ}
    {ρ : BoundEnv (Ty.denote C) β} {env : Env (Sigma C)}
    (agree : ∀ i : Fin n, env i.val = encodeValue C (β.get i) (ρ i)) (a : Ty.denote C A) :
    ∀ i : Fin (n + 1), extend env (encodeValue C A a) i.val =
      encodeValue C ((β.snoc A).get i) (ρ.snoc a i) :=
  Fin.cases rfl agree

theorem denote_tree (M : InstructionModel (Ty.denote C) Φ (ModelTree Events))
    (raw : Primitive Events Φ (Sigma C)) (compatible : Compatible M raw)
    {n : Nat} {β : BoundCtx (Ty κ) n} {A : Ty κ} {t : Tm Empty Φ n}
    (d : Derivation Φ (.nil : Ctx Empty (Ty κ)) β t A)
    (ρ : BoundEnv (Ty.denote C) β) (env : Env (Sigma C))
    (agree : ∀ i : Fin n, env i.val = encodeValue C (β.get i) (ρ i)) :
    (d.denote (Ty.denote C) M (fun x => x.elim) ρ >>= fun a => pure (encodeValue C A a)) =
      term raw env (erase t) := by
  induction d generalizing env with
  | fv h => rename_i x _; exact x.elim
  | bv => simp [Derivation.denote, erase, term, agree]
  | unit => rw [Derivation.denote, pure_bind]; rfl
  | op h ih =>
    simp only [Derivation.denote, erase, term, ← ih _ _ agree, bind_assoc, pure_bind]
    exact bind_congr fun a => (compatible _ a).symm
  | let₁ h b ihA ihB =>
    simp only [Derivation.denote, erase, term, ← ihA _ _ agree, bind_assoc, pure_bind]
    exact bind_congr fun a => ihB (ρ.snoc a) _ (snoc_agrees agree a)
  | pair h b ihA ihB =>
    simp only [Derivation.denote, erase, term, ← ihA _ _ agree, ← ihB _ _ agree, bind_assoc, pure_bind]
    rfl
  | let₂ h b ihA ihB =>
    simp only [Derivation.denote, erase, term, ← ihA _ _ agree, bind_assoc, pure_bind]
    apply bind_congr
    rintro ⟨a, b⟩
    exact ihB ((ρ.snoc a).snoc b) _ (snoc_agrees (snoc_agrees agree a) b)
  | inl h ih =>
    simp only [Derivation.denote, erase, term, ← ih _ _ agree, bind_assoc, pure_bind]
    rfl
  | inr h ih =>
    simp only [Derivation.denote, erase, term, ← ih _ _ agree, bind_assoc, pure_bind]
    rfl
  | case h l r ihA ihL ihR =>
    simp only [Derivation.denote, erase, term, ← ihA _ _ agree, bind_assoc, pure_bind]
    apply bind_congr
    intro x
    cases x with
    | inl a => exact ihL (ρ.snoc a) _ (snoc_agrees agree a)
    | inr b => exact ihR (ρ.snoc b) _ (snoc_agrees agree b)
  | abort h ih =>
    simp only [Derivation.denote, erase, term, ← ih _ _ agree, bind_assoc, pure_bind]
    exact bind_congr fun a => a.elim

end Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.FlatLetCase
