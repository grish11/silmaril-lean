module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.SetSemantics.Defs
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

universe u

noncomputable section

/-- The interpretation reads only the free names present in a term. -/
theorem Tm.denoteIn_congr_fvs (U : ℕ → ZFSet.{u}) :
    ∀ {k : ℕ} (t : Tm k) (β : Fin k → ZFSet.{u}) (ρ ρ' : String → ZFSet.{u}),
      (∀ x ∈ t.fvs, ρ x = ρ' x) → t.denoteIn U ρ β = t.denoteIn U ρ' β := by
  intro k t
  induction t with
  | fv x =>
    intro β ρ ρ' h
    exact h x (by simp [Tm.fvs])
  | bv | univ | empty | unit | star | nats | zero | refl | absurd =>
    intros
    rfl
  | succ t ih =>
    intro β ρ ρ' h
    exact congrArg (fun a => insert a a) (ih β ρ ρ' h)
  | pi A B ihA ihB =>
    intro β ρ ρ' h
    apply congrArg₂ SetSem.pi (ihA β ρ ρ' (fun x hx => h x (by simp [Tm.fvs, hx])))
    funext x
    exact ihB (Fin.cons x β) ρ ρ' (fun y hy => h y (by simp [Tm.fvs, hy]))
  | sigma A B ihA ihB =>
    intro β ρ ρ' h
    apply congrArg₂ SetSem.sigma (ihA β ρ ρ' (fun x hx => h x (by simp [Tm.fvs, hx])))
    funext x
    exact ihB (Fin.cons x β) ρ ρ' (fun y hy => h y (by simp [Tm.fvs, hy]))
  | abs A b ihA ihb =>
    intro β ρ ρ' h
    apply congrArg₂ SetSem.lam (ihA β ρ ρ' (fun x hx => h x (by simp [Tm.fvs, hx])))
    funext x
    exact ihb (Fin.cons x β) ρ ρ' (fun y hy => h y (by simp [Tm.fvs, hy]))
  | app f a ihf iha =>
    intro β ρ ρ' h
    exact congrArg₂ SetSem.app (ihf β ρ ρ' (fun x hx => h x (by simp [Tm.fvs, hx])))
      (iha β ρ ρ' (fun x hx => h x (by simp [Tm.fvs, hx])))
  | pair a b iha ihb =>
    intro β ρ ρ' h
    exact congrArg₂ SetSem.pair (iha β ρ ρ' (fun x hx => h x (by simp [Tm.fvs, hx])))
      (ihb β ρ ρ' (fun x hx => h x (by simp [Tm.fvs, hx])))
  | fst p ih =>
    intro β ρ ρ' h
    exact congrArg SetSem.fst (ih β ρ ρ' h)
  | snd p ih =>
    intro β ρ ρ' h
    exact congrArg SetSem.snd (ih β ρ ρ' h)
  | id A a b ihA iha ihb =>
    intro β ρ ρ' h
    dsimp only [Tm.denoteIn]
    rw [iha β ρ ρ' (fun x hx => h x (by simp [Tm.fvs, hx])),
      ihb β ρ ρ' (fun x hx => h x (by simp [Tm.fvs, hx]))]
  | natrec C s z n ihC ihs ihz ihn =>
    intro β ρ ρ' h
    dsimp only [Tm.denoteIn]
    rw [ihz β ρ ρ' (fun x hx => h x (by simp [Tm.fvs, hx])),
      ihn β ρ ρ' (fun x hx => h x (by simp [Tm.fvs, hx]))]
    congr 1
    funext m acc
    rw [ihs (Fin.cons m β) ρ ρ' (fun x hx => h x (by simp [Tm.fvs, hx]))]
  | wtype A B ihA ihB =>
    intro β ρ ρ' h
    apply congrArg₂ WSet.carrier (ihA β ρ ρ' (fun x hx => h x (by simp [Tm.fvs, hx])))
    funext x
    exact ihB (Fin.cons x β) ρ ρ' (fun y hy => h y (by simp [Tm.fvs, hy]))
  | sup A B a f ihA ihB iha ihf =>
    show ∀ β (ρ ρ' : String → ZFSet.{u}),
      (∀ x ∈ (Tm.sup A B a f).fvs, ρ x = ρ' x) →
        (Tm.sup A B a f).denoteIn U ρ β = (Tm.sup A B a f).denoteIn U ρ' β
    intro β ρ ρ' h
    dsimp only [Tm.denoteIn]
    rw [ihA β ρ ρ' (fun x hx => h x (by simp [Tm.fvs, hx])),
      iha β ρ ρ' (fun x hx => h x (by simp [Tm.fvs, hx])),
      ihf β ρ ρ' (fun x hx => h x (by simp [Tm.fvs, hx]))]
    congr 1
    funext x
    exact ihB (Fin.cons x β) ρ ρ' (fun y hy => h y (by simp [Tm.fvs, hy]))
  | wrec A B C s t ihA ihB _ ihs iht =>
    show ∀ β (ρ ρ' : String → ZFSet.{u}),
      (∀ x ∈ (Tm.wrec A B C s t).fvs, ρ x = ρ' x) →
        (Tm.wrec A B C s t).denoteIn U ρ β = (Tm.wrec A B C s t).denoteIn U ρ' β
    intro β ρ ρ' h
    dsimp only [Tm.denoteIn]
    rw [ihA β ρ ρ' (fun x hx => h x (by simp [Tm.fvs, hx])),
      ihs β ρ ρ' (fun x hx => h x (by simp [Tm.fvs, hx])),
      iht β ρ ρ' (fun x hx => h x (by simp [Tm.fvs, hx]))]
    congr 1
    funext x
    exact ihB (Fin.cons x β) ρ ρ' (fun y hy => h y (by simp [Tm.fvs, hy]))

private theorem cons_castLE {n m : ℕ} (h : n ≤ m) (a : ZFSet.{u}) (β : Fin m → ZFSet.{u}) :
    (fun i : Fin (n + 1) => (Fin.cons a β : Fin (m + 1) → ZFSet.{u})
      (i.castLE (Nat.succ_le_succ h))) =
      (Fin.cons a (fun i => β (i.castLE h)) : Fin (n + 1) → ZFSet.{u}) := by
  funext i
  cases i using Fin.cases <;> rfl

/-- Scope extension leaves the represented bound variables unchanged. -/
theorem Tm.denoteIn_castLE (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u})
    {n m : ℕ} (h : n ≤ m) (β : Fin m → ZFSet.{u}) (t : Tm n) :
    (t.castLE h).denoteIn U ρ β = t.denoteIn U ρ (fun i => β (i.castLE h)) := by
  fun_induction Tm.castLE h t <;> simp_all [Tm.denoteIn, cons_castLE]

/-- Closed terms ignore any bound-variable environment added by a scope extension. -/
theorem Tm.denoteIn_castLE_closed (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u})
    {k : ℕ} (β : Fin k → ZFSet.{u}) (t : Tm 0) :
    (t.castLE (Nat.zero_le k)).denoteIn U ρ β = t.denoteIn U ρ Fin.elim0 := by
  rw [Tm.denoteIn_castLE]
  congr 1
  funext i
  exact i.elim0

/-- Opening the outermost variable supplies the value of the chosen free name. -/
theorem Tm.denoteIn_open (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u}) {k : ℕ}
    (β : Fin k → ZFSet.{u}) (t : Tm (k + 1)) (x : String) :
    (t.open x).denoteIn U ρ β = t.denoteIn U ρ (Fin.snoc β (ρ x)) := by
  fun_induction Tm.open t x <;> simp_all [Tm.denoteIn, Fin.cons_snoc_eq_snoc_cons]
  case case2 =>
    rename_i k' i
    cases i using Fin.lastCases <;> simp [Tm.denoteIn]

/-- Instantiating the outermost variable supplies the denotation of the closed term. -/
theorem Tm.denoteIn_lst (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u}) {k : ℕ}
    (β : Fin k → ZFSet.{u}) (t : Tm (k + 1)) (a : Tm 0) :
    (t.lst a).denoteIn U ρ β = t.denoteIn U ρ (Fin.snoc β (a.denoteIn U ρ Fin.elim0)) := by
  fun_induction Tm.lst t a <;>
    simp_all [Tm.denoteIn, Fin.cons_snoc_eq_snoc_cons]
  case case2 =>
    rename_i k' i
    cases i using Fin.lastCases <;> simp [Tm.denoteIn, Tm.denoteIn_castLE_closed]

private theorem cons_skip {k : Nat} (j : Nat) (x : ZFSet.{u}) (β : Fin (k+1) → ZFSet.{u}) :
    (fun i : Fin (k+1) => if i.val < j+1 then
      (Fin.cons x β : Fin (k+2) → ZFSet.{u}) i.castSucc else (Fin.cons x β : Fin (k+2) → ZFSet.{u}) i.succ) =
      (Fin.cons x (fun i : Fin k => if i.val < j then β i.castSucc else β i.succ) :
        Fin (k+1) → ZFSet.{u}) := by
  funext i
  cases i using Fin.cases <;> simp
theorem Tm.denoteIn_wkn (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u}) {k : Nat}
    (β : Fin (k+1) → ZFSet.{u}) (t : Tm k) (j : Nat) :
    (t.wkn j).denoteIn U ρ β =
      t.denoteIn U ρ (fun i => if i.val < j then β i.castSucc else β i.succ) := by
  fun_induction Tm.wkn j t <;> simp_all only [Tm.denoteIn, cons_skip, ↓reduceIte]


/-- Weakening under an innermost variable ignores the added environment entry. -/
theorem Tm.denoteIn_wk0 (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u}) {k : ℕ}
    (β : Fin k → ZFSet.{u}) (t : Tm k) (a : ZFSet.{u}) :
    t.wk0.denoteIn U ρ (Fin.cons a β) = t.denoteIn U ρ β := by
  simp only [Tm.wk0, Tm.denoteIn_wkn, Nat.not_lt_zero, ↓reduceIte, Fin.cons_succ]

private theorem liftSub_denoteIn (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u})
    {n m : ℕ} (σ : Fin n → Tm m) (β : Fin m → ZFSet.{u}) (x : ZFSet.{u}) :
    (fun i => (Tm.liftSub σ i).denoteIn U ρ (Fin.cons x β)) =
      Fin.cons x (fun i => (σ i).denoteIn U ρ β) := by
  funext i
  cases i using Fin.cases <;> simp [Tm.liftSub, Tm.denoteIn, Tm.denoteIn_wk0]

/-- Simultaneous substitution evaluates the substituted terms in the original environment. -/
theorem Tm.denoteIn_bsubst (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u})
    {n m : ℕ} (σ : Fin n → Tm m) (β : Fin m → ZFSet.{u}) (t : Tm n) :
    (t.bsubst σ).denoteIn U ρ β = t.denoteIn U ρ (fun i => (σ i).denoteIn U ρ β) := by
  fun_induction Tm.bsubst σ t <;> simp_all [Tm.denoteIn, liftSub_denoteIn]

/-- Updating a name outside the support of a term leaves its interpretation unchanged. -/
theorem Tm.denoteIn_update (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u}) {k : ℕ}
    (β : Fin k → ZFSet.{u}) (t : Tm k) (x : String) (a : ZFSet.{u})
    (hx : x ∉ t.fvs) :
    t.denoteIn U (Function.update ρ x a) β = t.denoteIn U ρ β := by
  apply Tm.denoteIn_congr_fvs
  intro y hy
  have hyx : y ≠ x := by
    intro h
    exact hx (h ▸ hy)
  exact Function.update_of_ne hyx a ρ

/-- Updating a name outside a context's support preserves context satisfaction. -/
theorem Ctx.satIn_update (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u})
    (Γ : Ctx) (x : String) (a : ZFSet.{u}) (hx : x ∉ Γ.fvs) :
    Γ.SatIn U (Function.update ρ x a) ↔ Γ.SatIn U ρ := by
  induction Γ with
  | nil => rfl
  | cons Γ y A ih =>
    simp only [Ctx.fvs, Finset.mem_insert, Finset.mem_union, not_or] at hx
    simp only [Ctx.SatIn, ih hx.2.1, Tm.denoteIn_update U ρ Fin.elim0 A x a hx.2.2,
      Function.update_of_ne (Ne.symm hx.1)]

/-- Opening at a fresh name and updating that name supplies a chosen semantic argument. -/
theorem Tm.denoteIn_open_update (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u})
    (t : Tm 1) (x : String) (z : ZFSet.{u}) (hx : x ∉ t.fvs) :
    (t.open x).denoteIn U (Function.update ρ x z) Fin.elim0 =
      t.denoteIn U ρ (Fin.cons z Fin.elim0) := by
  rw [Tm.denoteIn_open, Function.update_self, Tm.denoteIn_update U ρ _ t x z hx]
  congr 1
  funext i
  have hi : i = 0 := by
    apply Fin.ext
    have := i.isLt
    omega
  subst i
  rfl

/-- A cofinite premise is valid at every semantic argument of its binding type. -/
theorem binder_validIn (U : ℕ → ZFSet.{u}) {Γ : Ctx} {A : Tm 0}
    {C a b : Tm 1} {L : Finset String}
    (h : ∀ x ∉ L, (⟨Γ.cons x A, C.open x, a.open x, b.open x⟩ : Jdg).ValidIn U)
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
  have hΓ' : Γ.SatIn U (Function.update ρ x z) := (Ctx.satIn_update U ρ Γ x z hxΓ).mpr hΓ
  have hz' : (Function.update ρ x z) x ∈ A.denoteIn U (Function.update ρ x z) Fin.elim0 := by
    simpa only [Function.update_self, Tm.denoteIn_update U ρ Fin.elim0 A x z hxA] using hz
  have hv := h x hxL (Function.update ρ x z) ⟨hΓ', hz'⟩
  simpa only [Tm.denoteIn_open_update U ρ a x z hxa,
    Tm.denoteIn_open_update U ρ b x z hxb, Tm.denoteIn_open_update U ρ C x z hxC] using hv

end

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
