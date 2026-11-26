module

public import Silmaril.SSA.Isotope.LetPar.Equations.Defs

@[expose] public section

namespace Silmaril.Isotope.Parallel.Proofs

universe u v w x

variable {tier target : Tier} {ν : Type v} {Φ : Type w} {n m : Nat}

namespace Tm

theorem widen_injective (h : Tier.Inclusion tier target) :
    Function.Injective (Parallel.Tm.widen h : Parallel.Tm tier ν Φ n → _) := by
  intro a
  induction a <;> intro b eq <;> cases b <;> simp_all [Parallel.Tm.widen] <;> grind

theorem widen_rename (h : Tier.Inclusion tier target) (ρ : Fin n → Fin m)
    (t : Parallel.Tm tier ν Φ n) :
    (t.rename ρ).widen h = (t.widen h).rename ρ := by
  induction t generalizing m <;> simp [Parallel.Tm.widen, Parallel.Tm.rename, *]

theorem widen_upSub (h : Tier.Inclusion tier target) (σ : Fin n → Parallel.Tm tier ν Φ m) :
    (fun i => (Parallel.Tm.upSub σ i).widen h) =
      Parallel.Tm.upSub (fun i => (σ i).widen h) := by
  funext i
  exact Fin.cases rfl (fun j => widen_rename h Fin.succ (σ j)) i

theorem widen_bsubst (h : Tier.Inclusion tier target) (σ : Fin n → Parallel.Tm tier ν Φ m)
    (t : Parallel.Tm tier ν Φ n) :
    (t.bsubst σ).widen h = (t.widen h).bsubst (fun i => (σ i).widen h) := by
  induction t generalizing m <;>
    simp [Parallel.Tm.widen, Parallel.Tm.bsubst, widen_upSub, *]

theorem widen_instantiate (h : Tier.Inclusion tier target) (b : Parallel.Tm tier ν Φ (n + 1))
    (a : Parallel.Tm tier ν Φ n) :
    (b.instantiate a).widen h = (b.widen h).instantiate (a.widen h) := by
  rw [Parallel.Tm.instantiate, widen_bsubst, Parallel.Tm.instantiate]
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

end Tm

variable {τ : Type u} [HasProduct τ] [HasUnit τ] [CaseTypes tier τ]
  [DecidableEq ν] [HasTy Φ τ] {Γ : Ctx ν τ}
  {β : BoundCtx τ n} {a : Parallel.Tm tier ν Φ n} {A : τ}

theorem hasType_rename {β' : BoundCtx τ m} (ρ : BoundCtx.Renaming β β')
    (h : HasType Φ Γ β a A) : HasType Φ Γ β' (a.rename ρ.toFun) A := by
  obtain ⟨d⟩ := h
  induction d generalizing m with
  | fv h => exact ⟨.fv h⟩
  | bv => exact ⟨ρ.typed _ ▸ .bv⟩
  | op _ ih => obtain ⟨d⟩ := ih ρ; exact ⟨.op d⟩
  | let₁ _ _ iha ihb =>
    obtain ⟨da⟩ := iha ρ
    obtain ⟨db⟩ := ihb (ρ.up _)
    exact ⟨.let₁ da db⟩
  | unit => exact ⟨.unit⟩
  | pair _ _ iha ihb =>
    obtain ⟨da⟩ := iha ρ
    obtain ⟨db⟩ := ihb ρ
    exact ⟨.pair da db⟩
  | let₂ _ _ iha ihb =>
    obtain ⟨da⟩ := iha ρ
    obtain ⟨db⟩ := ihb ((ρ.up _).up _)
    exact ⟨.let₂ da db⟩
  | inl _ ih => obtain ⟨d⟩ := ih ρ; exact ⟨.inl d⟩
  | inr _ ih => obtain ⟨d⟩ := ih ρ; exact ⟨.inr d⟩
  | case _ _ _ ihe ihl ihr =>
    obtain ⟨de⟩ := ihe ρ
    obtain ⟨dl⟩ := ihl (ρ.up _)
    obtain ⟨dr⟩ := ihr (ρ.up _)
    exact ⟨.case de dl dr⟩
  | abort _ ih => obtain ⟨d⟩ := ih ρ; exact ⟨.abort d⟩
  | iter _ _ iha ihb =>
    obtain ⟨da⟩ := iha ρ
    obtain ⟨db⟩ := ihb (ρ.up _)
    exact ⟨.iter da db⟩
  | par _ _ iha ihb =>
    obtain ⟨da⟩ := iha ρ
    obtain ⟨db⟩ := ihb ρ
    exact ⟨.par da db⟩

variable {ε : Type x} [HasEff Φ ε] {pureEff : ε}

omit [DecidableEq ν] in
theorem pure_widen {t : Parallel.Tm tier ν Φ n} (h : Tier.Inclusion tier target)
    (hp : Pure pureEff t) : Pure pureEff (t.widen h) := by
  induction hp with
  | fv => exact .fv
  | bv => exact .bv
  | op hf _ ih => exact .op hf ih
  | let₁ _ _ iha ihb => exact .let₁ iha ihb
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair iha ihb
  | let₂ _ _ iha ihb => exact .let₂ iha ihb
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ihe ihl ihr => exact .case ihe ihl ihr
  | abort _ ih => exact .abort ih
  | par _ _ iha ihb => exact .par iha ihb

end Silmaril.Isotope.Parallel.Proofs
