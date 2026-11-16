module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.LookupStructure.Defs
import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.LookupStructure

public section

/-!
# Structural semantics for arbitrary universe lookups

Opening, substitution, weakening and fresh-name binder arguments require no
universe closure laws. These lemmas use the actual `denoteIn`, `SatIn` and
`ValidIn` interpretations, so finite towers can use them directly.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

universe u

/-- Only the free names present in a term affect its interpretation. -/
theorem ETm.denoteIn_congr_fvs (U : ℕ → ZFSet.{u})
    {k : ℕ} (t : ETm k) (β : Fin k → ZFSet.{u}) (ρ ρ' : String → ZFSet.{u})
    (h : ∀ x ∈ t.fvs, ρ x = ρ' x) : t.denoteIn U ρ β = t.denoteIn U ρ' β :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.LookupStructure.congr_fvs U t β ρ ρ' h

/-- Scope extension preserves the represented bound variables. -/
theorem ETm.denoteIn_castLE (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u})
    {n m : ℕ} (h : n ≤ m) (β : Fin m → ZFSet.{u}) (t : ETm n) :
    (t.castLE h).denoteIn U ρ β = t.denoteIn U ρ (fun i => β (i.castLE h)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.LookupStructure.castLE U ρ h β t

/-- Closed terms ignore scope-extension entries in their bound-variable environment. -/
theorem ETm.denoteIn_castLE_closed (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u})
    {k : ℕ} (β : Fin k → ZFSet.{u}) (t : ETm 0) :
    (t.castLE (Nat.zero_le k)).denoteIn U ρ β = t.denoteIn U ρ Fin.elim0 :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.LookupStructure.castLE_closed U ρ β t

/-- Opening supplies the chosen free name's value to the outermost variable. -/
theorem ETm.denoteIn_open (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u}) {k : ℕ}
    (β : Fin k → ZFSet.{u}) (t : ETm (k + 1)) (x : String) :
    (t.open x).denoteIn U ρ β = t.denoteIn U ρ (Fin.snoc β (ρ x)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.LookupStructure.open_denote U ρ β t x

/-- Instantiation supplies the closed argument's denotation to the outermost variable. -/
theorem ETm.denoteIn_lst (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u}) {k : ℕ}
    (β : Fin k → ZFSet.{u}) (t : ETm (k + 1)) (a : ETm 0) :
    (t.lst a).denoteIn U ρ β = t.denoteIn U ρ (Fin.snoc β (a.denoteIn U ρ Fin.elim0)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.LookupStructure.lst U ρ β t a

/-- Weakening skips the added bound-variable environment entry. -/
theorem ETm.denoteIn_wkn (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u}) {k : ℕ}
    (β : Fin (k + 1) → ZFSet.{u}) (t : ETm k) (j : ℕ) :
    (t.wkn j).denoteIn U ρ β = t.denoteIn U ρ (fun i => if i.val < j then β i.castSucc else β i.succ) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.LookupStructure.wkn U ρ β t j

/-- Innermost weakening ignores the newly added value. -/
theorem ETm.denoteIn_wk0 (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u}) {k : ℕ}
    (β : Fin k → ZFSet.{u}) (t : ETm k) (a : ZFSet.{u}) :
    t.wk0.denoteIn U ρ (Fin.cons a β) = t.denoteIn U ρ β :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.LookupStructure.wk0 U ρ β t a

/-- Updating a name outside the term's support preserves its interpretation. -/
theorem ETm.denoteIn_update (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u}) {k : ℕ}
    (β : Fin k → ZFSet.{u}) (t : ETm k) (x : String) (a : ZFSet.{u}) (hx : x ∉ t.fvs) :
    t.denoteIn U (Function.update ρ x a) β = t.denoteIn U ρ β :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.LookupStructure.update U ρ β t x a hx

/-- Updating a name outside a context's support preserves its satisfaction. -/
theorem ECtx.satIn_update (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u})
    (Γ : ECtx) (x : String) (a : ZFSet.{u}) (hx : x ∉ Γ.fvs) :
    Γ.SatIn U (Function.update ρ x a) ↔ Γ.SatIn U ρ :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.LookupStructure.sat_update U ρ Γ x a hx

/-- Fresh opening followed by environment update supplies a chosen semantic argument. -/
theorem ETm.denoteIn_open_update (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u})
    (t : ETm 1) (x : String) (z : ZFSet.{u}) (hx : x ∉ t.fvs) :
    (t.open x).denoteIn U (Function.update ρ x z) Fin.elim0 =
      t.denoteIn U ρ (Fin.cons z Fin.elim0) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.LookupStructure.open_update U ρ t x z hx

/-- A cofinite valid binder family is valid at every semantic argument. -/
theorem binder_validIn (U : ℕ → ZFSet.{u}) {Γ : ECtx} {A : ETm 0} {C a b : ETm 1} {L : Finset String}
    (h : ∀ x ∉ L, (⟨Γ.cons x A, C.open x, a.open x, b.open x⟩ : EJdg).ValidIn U)
    (ρ : String → ZFSet.{u}) (hΓ : Γ.SatIn U ρ) (z : ZFSet.{u}) (hz : z ∈ A.denoteIn U ρ Fin.elim0) :
    a.denoteIn U ρ (Fin.cons z Fin.elim0) = b.denoteIn U ρ (Fin.cons z Fin.elim0) ∧
      a.denoteIn U ρ (Fin.cons z Fin.elim0) ∈ C.denoteIn U ρ (Fin.cons z Fin.elim0) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.LookupStructure.binder_valid U h ρ hΓ z hz

/-- Closed one-variable instantiation is semantic substitution by the argument's value. -/
theorem ETm.denoteIn_lst0 (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u}) (t : ETm 1) (a : ETm 0) :
    (t.lst a).denoteIn U ρ Fin.elim0 = t.denoteIn U ρ (Fin.cons (a.denoteIn U ρ Fin.elim0) Fin.elim0) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.LookupStructure.lst0 U ρ t a

/-- Nondependent arrows denote constant-fibre dependent products. -/
theorem ETm.denoteIn_arr (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u}) (A B : ETm 0) :
    (ETm.arr A B).denoteIn U ρ Fin.elim0 =
      SetSem.pi (A.denoteIn U ρ Fin.elim0) (fun _ => B.denoteIn U ρ Fin.elim0) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.LookupStructure.arr U ρ A B

/-- A satisfied context validates each actual variable lookup. -/
theorem ECtx.Lookup.satIn {Γ : ECtx} {x : String} {A : ETm 0} (hx : Γ.Lookup x A)
    (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u}) (hΓ : Γ.SatIn U ρ) :
    ρ x ∈ A.denoteIn U ρ Fin.elim0 :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.LookupStructure.lookup_sat hx U ρ hΓ

/-- A cofinite Nat step family acts at every natural input under the same lookup. -/
theorem natstep_validIn (U : ℕ → ZFSet.{u}) {Γ : ECtx} {C s s' : ETm 1} {L : Finset String}
    (h : ∀ x ∉ L, (⟨Γ.cons x .nats,
      ETm.arr (C.open x) (C.lst (.succ (.fv x))), s.open x, s'.open x⟩ : EJdg).ValidIn U)
    (ρ : String → ZFSet.{u}) (hΓ : Γ.SatIn U ρ) (m : ZFSet.{u}) (hm : m ∈ ZFSet.omega) :
    s.denoteIn U ρ (Fin.cons m Fin.elim0) = s'.denoteIn U ρ (Fin.cons m Fin.elim0) ∧
      s.denoteIn U ρ (Fin.cons m Fin.elim0) ∈
        SetSem.pi (C.denoteIn U ρ (Fin.cons m Fin.elim0))
          (fun _ => C.denoteIn U ρ (Fin.cons (insert m m) Fin.elim0)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.LookupStructure.natstep_valid U h ρ hΓ m hm

end Silmaril.Logic.TypeTheory.ExtensionalMLTT
