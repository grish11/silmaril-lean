module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.SetSemantics
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

universe u

noncomputable section

/-- The interpretation reads only the free names present in a term. -/
theorem ETm.denote_congr_fvs (T : SetHierarchy.{u}) :
    ∀ {k : ℕ} (t : ETm k) (β : Fin k → ZFSet.{u}) (ρ ρ' : String → ZFSet.{u}),
      (∀ x ∈ t.fvs, ρ x = ρ' x) → t.denote T ρ β = t.denote T ρ' β := by
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
    dsimp only [ETm.denote]
    rw [iha β ρ ρ' (fun x hx => h x (by simp [ETm.fvs, hx])),
      ihb β ρ ρ' (fun x hx => h x (by simp [ETm.fvs, hx]))]
  | natrec C s z n ihC ihs ihz ihn =>
    intro β ρ ρ' h
    dsimp only [ETm.denote]
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
theorem ETm.denote_castLE (T : SetHierarchy.{u}) (ρ : String → ZFSet.{u})
    {n m : ℕ} (h : n ≤ m) (β : Fin m → ZFSet.{u}) (t : ETm n) :
    (t.castLE h).denote T ρ β = t.denote T ρ (fun i => β (i.castLE h)) := by
  fun_induction ETm.castLE h t <;> simp_all [ETm.denote, cons_castLE]

/-- Closed terms ignore any bound-variable environment added by a scope extension. -/
theorem ETm.denote_castLE_closed (T : SetHierarchy.{u}) (ρ : String → ZFSet.{u})
    {k : ℕ} (β : Fin k → ZFSet.{u}) (t : ETm 0) :
    (t.castLE (Nat.zero_le k)).denote T ρ β = t.denote T ρ Fin.elim0 := by
  rw [ETm.denote_castLE]
  congr 1
  funext i
  exact i.elim0

/-- Opening the outermost variable supplies the value of the chosen free name. -/
theorem ETm.denote_open (T : SetHierarchy.{u}) (ρ : String → ZFSet.{u}) {k : ℕ}
    (β : Fin k → ZFSet.{u}) (t : ETm (k + 1)) (x : String) :
    (t.open x).denote T ρ β = t.denote T ρ (Fin.snoc β (ρ x)) := by
  fun_induction ETm.open t x <;> simp_all [ETm.denote, Fin.cons_snoc_eq_snoc_cons]
  case case2 =>
    rename_i k' i
    cases i using Fin.lastCases <;> simp [ETm.denote]

/-- Instantiating the outermost variable supplies the denotation of the closed term. -/
theorem ETm.denote_lst (T : SetHierarchy.{u}) (ρ : String → ZFSet.{u}) {k : ℕ}
    (β : Fin k → ZFSet.{u}) (t : ETm (k + 1)) (a : ETm 0) :
    (t.lst a).denote T ρ β = t.denote T ρ (Fin.snoc β (a.denote T ρ Fin.elim0)) := by
  fun_induction ETm.lst t a <;>
    simp_all [ETm.denote, Fin.cons_snoc_eq_snoc_cons]
  case case2 =>
    rename_i k' i
    cases i using Fin.lastCases <;> simp [ETm.denote, ETm.denote_castLE_closed]

private theorem cons_skip {k : Nat} (j : Nat) (x : ZFSet.{u}) (β : Fin (k+1) → ZFSet.{u}) :
    (fun i : Fin (k+1) => if i.val < j+1 then
      (Fin.cons x β : Fin (k+2) → ZFSet.{u}) i.castSucc else (Fin.cons x β : Fin (k+2) → ZFSet.{u}) i.succ) =
      (Fin.cons x (fun i : Fin k => if i.val < j then β i.castSucc else β i.succ) :
        Fin (k+1) → ZFSet.{u}) := by
  funext i
  cases i using Fin.cases <;> simp
theorem ETm.denote_wkn (T : SetHierarchy.{u}) (ρ : String → ZFSet.{u}) {k : Nat}
    (β : Fin (k+1) → ZFSet.{u}) (t : ETm k) (j : Nat) :
    (t.wkn j).denote T ρ β =
      t.denote T ρ (fun i => if i.val < j then β i.castSucc else β i.succ) := by
  fun_induction ETm.wkn j t <;> simp_all only [ETm.denote, cons_skip, ↓reduceIte]


/-- Weakening under an innermost variable ignores the added environment entry. -/
theorem ETm.denote_wk0 (T : SetHierarchy.{u}) (ρ : String → ZFSet.{u}) {k : ℕ}
    (β : Fin k → ZFSet.{u}) (t : ETm k) (a : ZFSet.{u}) :
    t.wk0.denote T ρ (Fin.cons a β) = t.denote T ρ β := by
  simp only [ETm.wk0, ETm.denote_wkn, Nat.not_lt_zero, ↓reduceIte, Fin.cons_succ]

/-- Updating a name outside the support of a term leaves its interpretation unchanged. -/
theorem ETm.denote_update (T : SetHierarchy.{u}) (ρ : String → ZFSet.{u}) {k : ℕ}
    (β : Fin k → ZFSet.{u}) (t : ETm k) (x : String) (a : ZFSet.{u})
    (hx : x ∉ t.fvs) :
    t.denote T (Function.update ρ x a) β = t.denote T ρ β := by
  apply ETm.denote_congr_fvs
  intro y hy
  have hyx : y ≠ x := by
    intro h
    exact hx (h ▸ hy)
  exact Function.update_of_ne hyx a ρ

/-- Updating a name outside a context's support preserves context satisfaction. -/
theorem ECtx.sat_update (T : SetHierarchy.{u}) (ρ : String → ZFSet.{u})
    (Γ : ECtx) (x : String) (a : ZFSet.{u}) (hx : x ∉ Γ.fvs) :
    Γ.Sat T (Function.update ρ x a) ↔ Γ.Sat T ρ := by
  induction Γ with
  | nil => rfl
  | cons Γ y A ih =>
    simp only [ECtx.fvs, Finset.mem_insert, Finset.mem_union, not_or] at hx
    simp only [ECtx.Sat, ih hx.2.1, ETm.denote_update T ρ Fin.elim0 A x a hx.2.2,
      Function.update_of_ne (Ne.symm hx.1)]

/-- Opening at a fresh name and updating that name supplies a chosen semantic argument. -/
theorem ETm.denote_open_update (T : SetHierarchy.{u}) (ρ : String → ZFSet.{u})
    (t : ETm 1) (x : String) (z : ZFSet.{u}) (hx : x ∉ t.fvs) :
    (t.open x).denote T (Function.update ρ x z) Fin.elim0 =
      t.denote T ρ (Fin.cons z Fin.elim0) := by
  rw [ETm.denote_open, Function.update_self, ETm.denote_update T ρ _ t x z hx]
  congr 1
  funext i
  have hi : i = 0 := by
    apply Fin.ext
    have := i.isLt
    omega
  subst i
  rfl

/-- A cofinite premise is valid at every semantic argument of its binding type. -/
theorem binder_valid (T : SetHierarchy.{u}) {Γ : ECtx} {A : ETm 0}
    {C a b : ETm 1} {L : Finset String}
    (h : ∀ x ∉ L, (⟨Γ.cons x A, C.open x, a.open x, b.open x⟩ : EJdg).Valid T)
    (ρ : String → ZFSet.{u}) (hΓ : Γ.Sat T ρ) (z : ZFSet.{u})
    (hz : z ∈ A.denote T ρ Fin.elim0) :
    a.denote T ρ (Fin.cons z Fin.elim0) = b.denote T ρ (Fin.cons z Fin.elim0) ∧
      a.denote T ρ (Fin.cons z Fin.elim0) ∈ C.denote T ρ (Fin.cons z Fin.elim0) := by
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset (L ∪ Γ.fvs ∪ A.fvs ∪ C.fvs ∪ a.fvs ∪ b.fvs)
  have hxL : x ∉ L := fun h => hx (by simp [h])
  have hxΓ : x ∉ Γ.fvs := fun h => hx (by simp [h])
  have hxA : x ∉ A.fvs := fun h => hx (by simp [h])
  have hxC : x ∉ C.fvs := fun h => hx (by simp [h])
  have hxa : x ∉ a.fvs := fun h => hx (by simp [h])
  have hxb : x ∉ b.fvs := fun h => hx (by simp [h])
  have hΓ' : Γ.Sat T (Function.update ρ x z) := (ECtx.sat_update T ρ Γ x z hxΓ).mpr hΓ
  have hz' : (Function.update ρ x z) x ∈ A.denote T (Function.update ρ x z) Fin.elim0 := by
    simpa only [Function.update_self, ETm.denote_update T ρ Fin.elim0 A x z hxA] using hz
  have hv := h x hxL (Function.update ρ x z) ⟨hΓ', hz'⟩
  simpa only [ETm.denote_open_update T ρ a x z hxa,
    ETm.denote_open_update T ρ b x z hxb, ETm.denote_open_update T ρ C x z hxC] using hv

end

end Silmaril.Logic.TypeTheory.ExtensionalMLTT
