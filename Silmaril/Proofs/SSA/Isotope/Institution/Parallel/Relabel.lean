module

public import Silmaril.SSA.Isotope.Institution.Parallel.Relabel.Defs

@[expose] public section

namespace Silmaril.Isotope.Parallel.InstitutionProofs

open Silmaril.Isotope.Institution CategoryTheory

universe u v w

namespace Tm

variable {tier target : Tier} {ν : Type v} {Φ Ψ Ω : Type w} {n m : Nat}
  (f : Φ → Ψ) (g : Ψ → Ω)

@[simp] theorem map_id (t : Tm tier ν Φ n) : t.mapInstr id = t := by
  induction t <;> simp_all [Parallel.Tm.mapInstr]

theorem map_comp (t : Tm tier ν Φ n) :
    (t.mapInstr f).mapInstr g = t.mapInstr (g ∘ f) := by
  induction t <;> simp_all [Parallel.Tm.mapInstr, Function.comp_def]

@[simp] theorem map_rename (ρ : Fin n → Fin m) (t : Tm tier ν Φ n) :
    (t.rename ρ).mapInstr f = (t.mapInstr f).rename ρ := by
  induction t generalizing m <;> simp_all [Parallel.Tm.mapInstr, Parallel.Tm.rename]

private theorem map_upSub (σ : Fin n → Tm tier ν Φ m) :
    (fun i => (Parallel.Tm.upSub σ i).mapInstr f) =
      Parallel.Tm.upSub (fun i => (σ i).mapInstr f) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact map_rename f Fin.succ (σ j)

@[simp] theorem map_bsubst (σ : Fin n → Tm tier ν Φ m) (t : Tm tier ν Φ n) :
    (t.bsubst σ).mapInstr f = (t.mapInstr f).bsubst (fun i => (σ i).mapInstr f) := by
  induction t generalizing m <;>
    simp_all only [Parallel.Tm.mapInstr, Parallel.Tm.bsubst, map_upSub]

@[simp] theorem map_instantiate (b : Tm tier ν Φ (n + 1)) (a : Tm tier ν Φ n) :
    (b.instantiate a).mapInstr f = (b.mapInstr f).instantiate (a.mapInstr f) := by
  unfold Parallel.Tm.instantiate
  rw [map_bsubst]
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

@[simp] theorem map_widen (h : tier.Inclusion target) (t : Tm tier ν Φ n) :
    (t.widen h).mapInstr f = (t.mapInstr f).widen h := by
  induction t <;> simp_all [Parallel.Tm.mapInstr, Parallel.Tm.widen]

end Tm

variable {τ ε : Type u} {S S' S'' : InstrSig τ ε} {tier : Tier} {ν : Type v}
  {n : Nat} {e : ε} {a b : Tm tier ν S.Instr n} (f : S ⟶ S')

theorem pure_map (h : Pure e a) : Pure e (a.mapInstr f.instr) := by
  induction h with
  | op hf _ ih => exact .op ((f.effect _).trans hf) ih
  | fv => exact .fv
  | bv => exact .bv
  | unit => exact .unit
  | let₁ _ _ ia ib => exact .let₁ ia ib
  | pair _ _ ia ib => exact .pair ia ib
  | let₂ _ _ ia ib => exact .let₂ ia ib
  | inl _ ia => exact .inl ia
  | inr _ ia => exact .inr ia
  | case _ _ _ ie il ir => exact .case ie il ir
  | abort _ ia => exact .abort ia
  | par _ _ ia ib => exact .par ia ib

theorem seqRule_map (h : SeqRule e a b) :
    SeqRule e (a.mapInstr f.instr) (b.mapInstr f.instr) := by
  cases h with
  | letBeta hp => simpa only [Parallel.Tm.mapInstr, Tm.map_instantiate] using
      SeqRule.letBeta (pure_map f hp)
  | letEta => exact .letEta _
  | unitEta => exact .unitEta _
  | pairEta => exact .pairEta _
  | pairBeta => simpa only [Parallel.Tm.mapInstr, Parallel.Tm.lift, Tm.map_rename] using
      SeqRule.pairBeta _ _ _
  | bindOp => simpa only [Parallel.Tm.mapInstr, Parallel.Tm.underBinder, Tm.map_rename] using
      SeqRule.bindOp _ _
  | bindLet => simpa only [Parallel.Tm.mapInstr, Parallel.Tm.underBinder, Tm.map_rename] using
      SeqRule.bindLet _ _ _
  | bindLetPair => simpa only [Parallel.Tm.mapInstr, Parallel.Tm.underBinder, Tm.map_rename] using
      SeqRule.bindLetPair _ _ _
  | bindPair => simpa only [Parallel.Tm.mapInstr, Parallel.Tm.underTwoBinders, Tm.map_rename] using
      SeqRule.bindPair _ _

theorem parRule_map (h : ParRule e a b) :
    ParRule e (a.mapInstr f.instr) (b.mapInstr f.instr) := by
  cases h with
  | swap => exact .swap _ _
  | assoc => exact .assoc _ _ _
  | purePair ha hb => exact .purePair (pure_map f ha) (pure_map f hb)
  | unitLeft => exact .unitLeft _
  | unitRight => exact .unitRight _
  | map hf hg =>
      simpa only [Parallel.Tm.mapInstr, Parallel.Tm.leftResult, Parallel.Tm.underBinder,
        Tm.map_rename] using ParRule.map (pure_map f hf) (pure_map f hg)

theorem caseRule_map (h : CaseRule e a b) :
    CaseRule e (a.mapInstr f.instr) (b.mapInstr f.instr) := by
  cases h with
  | betaL hc => exact .betaL hc _ _ _
  | betaR hc => exact .betaR hc _ _ _
  | eta hc => exact .eta hc _
  | emptyInitial hc => exact .emptyInitial hc _ _ _
  | bindLetCase hc =>
      simpa only [Parallel.Tm.mapInstr, Parallel.Tm.underBinder, Tm.map_rename] using
        CaseRule.bindLetCase hc _ _ _ _
  | bindCase hc =>
      simpa only [Parallel.Tm.mapInstr, Parallel.Tm.underBinder, Tm.map_rename] using
        CaseRule.bindCase hc _ _ _
  | parCaseLeft hc hp => simpa only [Parallel.Tm.mapInstr, Parallel.Tm.lift, Tm.map_rename] using
      CaseRule.parCaseLeft hc (pure_map f hp)
  | parCaseRight hc hp => simpa only [Parallel.Tm.mapInstr, Parallel.Tm.lift, Tm.map_rename] using
      CaseRule.parCaseRight hc (pure_map f hp)

variable [HasProduct τ] [HasUnit τ] [CaseTypes tier τ] [DecidableEq ν]
  {Γ : Ctx ν τ} {β : BoundCtx τ n} {A : τ}

theorem hasType_map (h : HasType S.Instr Γ β a A) :
    HasType S'.Instr Γ β (a.mapInstr f.instr) A :=
  ⟨h.some.mapInstr f⟩

theorem equiv_map {rules : EqScheme tier ν S.Instr} {rules' : EqScheme tier ν S'.Instr}
    (extra : ∀ {k} {l r : Parallel.Tm tier ν S.Instr k}, rules l r →
      rules' (l.mapInstr f.instr) (r.mapInstr f.instr))
    (h : Equiv e rules Γ β a b A) :
    Equiv e rules' Γ β (a.mapInstr f.instr) (b.mapInstr f.instr) A := by
  induction h with
  | refl h => exact .refl (hasType_map f h)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | @op _ _ _ _ op _ ih =>
      exact f.target op ▸ Equiv.op ((f.source op).symm ▸ ih)
  | let₁ _ _ ia ib => exact .let₁ ia ib
  | pair _ _ ia ib => exact .pair ia ib
  | let₂ _ _ ia ib => exact .let₂ ia ib
  | inl _ ia => exact .inl ia
  | inr _ ia => exact .inr ia
  | case _ _ _ ie il ir => exact .case ie il ir
  | abort _ ia => exact .abort ia
  | iter _ _ ia ib => exact .iter ia ib
  | par _ _ ia ib => exact .par ia ib
  | seqRule h ha hb => exact .seqRule (seqRule_map f h) (hasType_map f ha) (hasType_map f hb)
  | parRule h ha hb => exact .parRule (parRule_map f h) (hasType_map f ha) (hasType_map f hb)
  | extraRule h ha hb => exact .extraRule (extra h) (hasType_map f ha) (hasType_map f hb)

end Silmaril.Isotope.Parallel.InstitutionProofs

@[expose] public section

namespace Silmaril.Isotope.Parallel.InstitutionProofs

open Silmaril.Isotope.Institution CategoryTheory

universe u v

variable {τ ε : Type u} {S S' S'' : InstrSig τ ε} {tier : Tier} {ν : Type v}
  [HasProduct τ] [HasUnit τ] [CaseTypes tier τ] [DecidableEq ν] {Γ : Ctx ν τ}
  {n : Nat} {β : BoundCtx τ n} {A B : τ} {t : Parallel.Tm tier ν S.Instr n}

theorem derivation_map_cast (f : S ⟶ S') (h : A = B)
    (d : Derivation S.Instr Γ β t A) :
    (Derivation.castResult h d).mapInstr f =
      Derivation.castResult h (d.mapInstr f) := by
  cases h
  rfl

theorem derivation_map_id (d : Derivation S.Instr Γ β t A) :
    HEq (d.mapInstr (𝟙 S)) d := by
  induction d <;>
    simp only [Derivation.mapInstr, Derivation.castResult, InstrSig.id_instr] <;>
    congr 1 <;> simp only [Tm.map_id]

theorem derivation_map_comp (f : S ⟶ S') (g : S' ⟶ S'')
    (d : Derivation S.Instr Γ β t A) :
    HEq ((d.mapInstr f).mapInstr g) (d.mapInstr (f ≫ g)) := by
  induction d with
  | @op k b a p d ih =>
      change HEq
        ((Derivation.castResult (f.target p)
          (Derivation.op (f := f.instr p)
            (Derivation.castResult (f.source p).symm (d.mapInstr f)))).mapInstr g) _
      rw [derivation_map_cast]
      change HEq
        (Derivation.castResult (f.target p) (Derivation.castResult (g.target (f.instr p))
          (Derivation.op (f := g.instr (f.instr p))
            (Derivation.castResult (g.source (f.instr p)).symm
              ((Derivation.castResult (f.source p).symm (d.mapInstr f)).mapInstr g)))))
        (Derivation.castResult ((f ≫ g).target p)
          (Derivation.op (f := (f ≫ g).instr p)
            (Derivation.castResult ((f ≫ g).source p).symm (d.mapInstr (f ≫ g)))))
      rw [derivation_map_cast]
      simp only [Derivation.castResult, eqRec_heq_iff, heq_eqRec_iff]
      congr 1
      · exact Tm.map_comp f.instr g.instr a
      · simpa only [eqRec_heq_iff, heq_eqRec_iff] using ih
  | _ =>
      simp only [Derivation.mapInstr]
      congr 1 <;> simp only [InstrSig.comp_instr, Tm.map_comp]

end Silmaril.Isotope.Parallel.InstitutionProofs
