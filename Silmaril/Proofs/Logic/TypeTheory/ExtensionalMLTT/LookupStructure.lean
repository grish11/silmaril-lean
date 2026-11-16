module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.LookupStructure.Defs
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.LookupStructure

open Silmaril.Logic.TypeTheory.ExtensionalMLTT

universe u

noncomputable section

/-- The interpretation reads only the free names present in a term. -/
theorem congr_fvs (U : ℕ → ZFSet.{u}) :
    ∀ {k : ℕ} (t : ETm k) (β : Fin k → ZFSet.{u}) (ρ ρ' : String → ZFSet.{u}),
      (∀ x ∈ t.fvs, ρ x = ρ' x) → t.denoteIn U ρ β = t.denoteIn U ρ' β := by
  intro k t
  induction t with
  | fv x =>
    intro β ρ ρ' h
    exact h x (by simp [ETm.fvs])
  | bv | univ | empty | unit | star | nats | zero | refl | absurd =>
    intros
    rfl
  | succ t ih =>
    intro β ρ ρ' h
    exact congrArg (fun a => insert a a) (ih β ρ ρ' h)
  | pi A B ihA ihB =>
    intro β ρ ρ' h
    apply congrArg₂ SetSem.pi (ihA β ρ ρ' (fun x hx => h x (by simp [ETm.fvs, hx])))
    funext x
    exact ihB (Fin.cons x β) ρ ρ' (fun y hy => h y (by simp [ETm.fvs, hy]))
  | sigma A B ihA ihB =>
    intro β ρ ρ' h
    apply congrArg₂ SetSem.sigma (ihA β ρ ρ' (fun x hx => h x (by simp [ETm.fvs, hx])))
    funext x
    exact ihB (Fin.cons x β) ρ ρ' (fun y hy => h y (by simp [ETm.fvs, hy]))
  | abs A b ihA ihb =>
    intro β ρ ρ' h
    apply congrArg₂ SetSem.lam (ihA β ρ ρ' (fun x hx => h x (by simp [ETm.fvs, hx])))
    funext x
    exact ihb (Fin.cons x β) ρ ρ' (fun y hy => h y (by simp [ETm.fvs, hy]))
  | app f a ihf iha =>
    intro β ρ ρ' h
    exact congrArg₂ SetSem.app (ihf β ρ ρ' (fun x hx => h x (by simp [ETm.fvs, hx])))
      (iha β ρ ρ' (fun x hx => h x (by simp [ETm.fvs, hx])))
  | pair a b iha ihb =>
    intro β ρ ρ' h
    exact congrArg₂ SetSem.pair (iha β ρ ρ' (fun x hx => h x (by simp [ETm.fvs, hx])))
      (ihb β ρ ρ' (fun x hx => h x (by simp [ETm.fvs, hx])))
  | fst p ih =>
    intro β ρ ρ' h
    exact congrArg SetSem.fst (ih β ρ ρ' h)
  | snd p ih =>
    intro β ρ ρ' h
    exact congrArg SetSem.snd (ih β ρ ρ' h)
  | id A a b ihA iha ihb =>
    intro β ρ ρ' h
    dsimp only [ETm.denoteIn]
    rw [iha β ρ ρ' (fun x hx => h x (by simp [ETm.fvs, hx])),
      ihb β ρ ρ' (fun x hx => h x (by simp [ETm.fvs, hx]))]
  | natrec C s z n ihC ihs ihz ihn =>
    intro β ρ ρ' h
    dsimp only [ETm.denoteIn]
    rw [ihz β ρ ρ' (fun x hx => h x (by simp [ETm.fvs, hx])),
      ihn β ρ ρ' (fun x hx => h x (by simp [ETm.fvs, hx]))]
    congr 1
    funext m acc
    rw [ihs (Fin.cons m β) ρ ρ' (fun x hx => h x (by simp [ETm.fvs, hx]))]

private theorem cons_castLE {n m : ℕ} (h : n ≤ m) (a : ZFSet.{u}) (β : Fin m → ZFSet.{u}) :
    (fun i : Fin (n + 1) => (Fin.cons a β : Fin (m + 1) → ZFSet.{u})
      (i.castLE (Nat.succ_le_succ h))) =
      (Fin.cons a (fun i => β (i.castLE h)) : Fin (n + 1) → ZFSet.{u}) := by
  funext i
  cases i using Fin.cases <;> rfl

/-- Scope extension leaves the represented bound variables unchanged. -/
theorem castLE (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u})
    {n m : ℕ} (h : n ≤ m) (β : Fin m → ZFSet.{u}) (t : ETm n) :
    (t.castLE h).denoteIn U ρ β = t.denoteIn U ρ (fun i => β (i.castLE h)) := by
  fun_induction ETm.castLE h t <;> simp_all [ETm.denoteIn, cons_castLE]

/-- Closed terms ignore any bound-variable environment added by a scope extension. -/
theorem castLE_closed (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u})
    {k : ℕ} (β : Fin k → ZFSet.{u}) (t : ETm 0) :
    (t.castLE (Nat.zero_le k)).denoteIn U ρ β = t.denoteIn U ρ Fin.elim0 := by
  rw [castLE]
  congr 1
  funext i
  exact i.elim0

/-- Opening the outermost variable supplies the value of the chosen free name. -/
theorem open_denote (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u}) {k : ℕ}
    (β : Fin k → ZFSet.{u}) (t : ETm (k + 1)) (x : String) :
    (t.open x).denoteIn U ρ β = t.denoteIn U ρ (Fin.snoc β (ρ x)) := by
  fun_induction ETm.open t x <;> simp_all [ETm.denoteIn, Fin.cons_snoc_eq_snoc_cons]
  case case2 =>
    rename_i k' i
    cases i using Fin.lastCases <;> simp [ETm.denoteIn]

/-- Instantiating the outermost variable supplies the denotation of the closed term. -/
theorem lst (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u}) {k : ℕ}
    (β : Fin k → ZFSet.{u}) (t : ETm (k + 1)) (a : ETm 0) :
    (t.lst a).denoteIn U ρ β = t.denoteIn U ρ (Fin.snoc β (a.denoteIn U ρ Fin.elim0)) := by
  fun_induction ETm.lst t a <;>
    simp_all [ETm.denoteIn, Fin.cons_snoc_eq_snoc_cons]
  case case2 =>
    rename_i k' i
    cases i using Fin.lastCases <;> simp [ETm.denoteIn, castLE_closed]

private theorem cons_skip {k : Nat} (j : Nat) (x : ZFSet.{u}) (β : Fin (k+1) → ZFSet.{u}) :
    (fun i : Fin (k+1) => if i.val < j+1 then
      (Fin.cons x β : Fin (k+2) → ZFSet.{u}) i.castSucc else (Fin.cons x β : Fin (k+2) → ZFSet.{u}) i.succ) =
      (Fin.cons x (fun i : Fin k => if i.val < j then β i.castSucc else β i.succ) :
        Fin (k+1) → ZFSet.{u}) := by
  funext i
  cases i using Fin.cases <;> simp
theorem wkn (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u}) {k : Nat}
    (β : Fin (k+1) → ZFSet.{u}) (t : ETm k) (j : Nat) :
    (t.wkn j).denoteIn U ρ β =
      t.denoteIn U ρ (fun i => if i.val < j then β i.castSucc else β i.succ) := by
  fun_induction ETm.wkn j t <;> simp_all only [ETm.denoteIn, cons_skip, ↓reduceIte]


/-- Weakening under an innermost variable ignores the added environment entry. -/
theorem wk0 (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u}) {k : ℕ}
    (β : Fin k → ZFSet.{u}) (t : ETm k) (a : ZFSet.{u}) :
    t.wk0.denoteIn U ρ (Fin.cons a β) = t.denoteIn U ρ β := by
  simp only [ETm.wk0, wkn, Nat.not_lt_zero, ↓reduceIte, Fin.cons_succ]

/-- Updating a name outside the support of a term leaves its interpretation unchanged. -/
theorem update (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u}) {k : ℕ}
    (β : Fin k → ZFSet.{u}) (t : ETm k) (x : String) (a : ZFSet.{u})
    (hx : x ∉ t.fvs) :
    t.denoteIn U (Function.update ρ x a) β = t.denoteIn U ρ β := by
  apply congr_fvs
  intro y hy
  have hyx : y ≠ x := by
    intro h
    exact hx (h ▸ hy)
  exact Function.update_of_ne hyx a ρ

/-- Updating a name outside a context's support preserves context satisfaction. -/
theorem sat_update (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u})
    (Γ : ECtx) (x : String) (a : ZFSet.{u}) (hx : x ∉ Γ.fvs) :
    Γ.SatIn U (Function.update ρ x a) ↔ Γ.SatIn U ρ := by
  induction Γ with
  | nil => rfl
  | cons Γ y A ih =>
    simp only [ECtx.fvs, Finset.mem_insert, Finset.mem_union, not_or] at hx
    simp only [ECtx.SatIn, ih hx.2.1, update U ρ Fin.elim0 A x a hx.2.2,
      Function.update_of_ne (Ne.symm hx.1)]

/-- Opening at a fresh name and updating that name supplies a chosen semantic argument. -/
theorem open_update (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u})
    (t : ETm 1) (x : String) (z : ZFSet.{u}) (hx : x ∉ t.fvs) :
    (t.open x).denoteIn U (Function.update ρ x z) Fin.elim0 =
      t.denoteIn U ρ (Fin.cons z Fin.elim0) := by
  rw [open_denote, Function.update_self, update U ρ _ t x z hx]
  congr 1
  funext i
  have hi : i = 0 := by
    apply Fin.ext
    have := i.isLt
    omega
  subst i
  rfl

/-- A cofinite premise is valid at every semantic argument of its binding type. -/
theorem binder_valid (U : ℕ → ZFSet.{u}) {Γ : ECtx} {A : ETm 0}
    {C a b : ETm 1} {L : Finset String}
    (h : ∀ x ∉ L, (⟨Γ.cons x A, C.open x, a.open x, b.open x⟩ : EJdg).ValidIn U)
    (ρ : String → ZFSet.{u}) (hΓ : Γ.SatIn U ρ) (z : ZFSet.{u})
    (hz : z ∈ A.denoteIn U ρ Fin.elim0) :
    a.denoteIn U ρ (Fin.cons z Fin.elim0) = b.denoteIn U ρ (Fin.cons z Fin.elim0) ∧
      a.denoteIn U ρ (Fin.cons z Fin.elim0) ∈ C.denoteIn U ρ (Fin.cons z Fin.elim0) := by
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset (L ∪ Γ.fvs ∪ A.fvs ∪ C.fvs ∪ a.fvs ∪ b.fvs)
  have hxL : x ∉ L := fun h => hx (by simp [h])
  have hxΓ : x ∉ Γ.fvs := fun h => hx (by simp [h])
  have hxA : x ∉ A.fvs := fun h => hx (by simp [h])
  have hxC : x ∉ C.fvs := fun h => hx (by simp [h])
  have hxa : x ∉ a.fvs := fun h => hx (by simp [h])
  have hxb : x ∉ b.fvs := fun h => hx (by simp [h])
  have hΓ' : Γ.SatIn U (Function.update ρ x z) := (sat_update U ρ Γ x z hxΓ).mpr hΓ
  have hz' : (Function.update ρ x z) x ∈ A.denoteIn U (Function.update ρ x z) Fin.elim0 := by
    simpa only [Function.update_self, update U ρ Fin.elim0 A x z hxA] using hz
  have hv := h x hxL (Function.update ρ x z) ⟨hΓ', hz'⟩
  simpa only [open_update U ρ a x z hxa,
    open_update U ρ b x z hxb, open_update U ρ C x z hxC] using hv

private theorem snoc_empty (z : ZFSet.{u}) :
    (Fin.snoc (Fin.elim0 : Fin 0 → ZFSet.{u}) z : Fin 1 → ZFSet.{u}) =
      (Fin.cons z Fin.elim0 : Fin 1 → ZFSet.{u}) := by
  funext i
  have hi : i = 0 := by
    apply Fin.ext
    have hi : i.val < 1 := i.isLt
    omega
  subst i
  rfl

/-- Substituting in a one-variable term evaluates its argument in that variable. -/
theorem lst0 (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u})
    (t : ETm 1) (a : ETm 0) :
    (t.lst a).denoteIn U ρ Fin.elim0 = t.denoteIn U ρ (Fin.cons (a.denoteIn U ρ Fin.elim0) Fin.elim0) := by
  rw [lst, snoc_empty]

/-- Nondependent arrows are constant-fibre dependent products. -/
theorem arr (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u})
    (A B : ETm 0) :
    (ETm.arr A B).denoteIn U ρ Fin.elim0 =
      SetSem.pi (A.denoteIn U ρ Fin.elim0) (fun _ => B.denoteIn U ρ Fin.elim0) := by
  simp only [ETm.arr, ETm.denoteIn]
  congr 1
  funext z
  exact wk0 U ρ Fin.elim0 B z


/-- Context satisfaction validates every declared-variable lookup. -/
theorem lookup_sat {Γ : ECtx} {x : String} {A : ETm 0}
    (hx : Γ.Lookup x A) (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u})
    (hΓ : Γ.SatIn U ρ) : ρ x ∈ A.denoteIn U ρ Fin.elim0 := by
  induction hx with
  | here => exact hΓ.2
  | there _ _ _ _ _ _ _ ih => exact ih hΓ.1

/-- The cofinite natural-recursion step premise is valid at every natural input. -/
theorem natstep_valid (U : ℕ → ZFSet.{u}) {Γ : ECtx} {C s s' : ETm 1}
    {L : Finset String}
    (h : ∀ x ∉ L, (⟨Γ.cons x .nats,
      ETm.arr (C.open x) (C.lst (.succ (.fv x))), s.open x, s'.open x⟩ : EJdg).ValidIn U)
    (ρ : String → ZFSet.{u}) (hΓ : Γ.SatIn U ρ) (m : ZFSet.{u}) (hm : m ∈ ZFSet.omega) :
    s.denoteIn U ρ (Fin.cons m Fin.elim0) = s'.denoteIn U ρ (Fin.cons m Fin.elim0) ∧
    s.denoteIn U ρ (Fin.cons m Fin.elim0) ∈
      SetSem.pi (C.denoteIn U ρ (Fin.cons m Fin.elim0))
        (fun _ => C.denoteIn U ρ (Fin.cons (insert m m) Fin.elim0)) := by
  classical
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset (L ∪ Γ.fvs ∪ C.fvs ∪ s.fvs ∪ s'.fvs)
  have hxL : x ∉ L := fun h => hx (by simp [h])
  have hxΓ : x ∉ Γ.fvs := fun h => hx (by simp [h])
  have hxC : x ∉ C.fvs := fun h => hx (by simp [h])
  have hxs : x ∉ s.fvs := fun h => hx (by simp [h])
  have hxs' : x ∉ s'.fvs := fun h => hx (by simp [h])
  have hΓ' := (sat_update U ρ Γ x m hxΓ).2 hΓ
  have hv := h x hxL (Function.update ρ x m) ⟨hΓ', by simpa [ETm.denoteIn] using hm⟩
  change (s.open x).denoteIn U (Function.update ρ x m) Fin.elim0 = _ ∧
    (s.open x).denoteIn U (Function.update ρ x m) Fin.elim0 ∈
      (ETm.arr (C.open x) (C.lst (.succ (.fv x)))).denoteIn U (Function.update ρ x m) Fin.elim0 at hv
  rw [open_update U ρ s x m hxs,
    open_update U ρ s' x m hxs', arr,
    open_update U ρ C x m hxC, lst0] at hv
  simp only [ETm.denoteIn, Function.update_self] at hv
  rw [update U ρ _ C x m hxC] at hv
  exact hv


end

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.LookupStructure
