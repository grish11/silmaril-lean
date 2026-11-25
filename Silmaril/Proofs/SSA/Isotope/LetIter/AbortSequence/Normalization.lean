module

public import Silmaril.SSA.Isotope.LetIter.AbortSequence.Normalization.Defs
public import Silmaril.SSA.Isotope.LetIter.AbortSequence.Thms

/-! # Exact comparison of terms with explicitly sequenced aborts -/

public section

namespace Silmaril.Isotope.LetIter.LocallyNameless.AbortNormalization.Proofs

universe u v w r

variable {ν : Type w} {Φ : Type v} {n m : Nat}

theorem sequenceAborts_rename (ρ : Fin n → Fin m) (t : Tm ν Φ n) :
    sequenceAborts (Tm.rename ρ t) = Tm.rename ρ (sequenceAborts t) := by
  induction t generalizing m <;> simp only [sequenceAborts, Tm.rename, *]
  rfl

private theorem sequenceAborts_lift (t : Tm ν Φ n) :
    sequenceAborts t.lift = (sequenceAborts t).lift :=
  sequenceAborts_rename _ _

private theorem sequenceAborts_underBinder (t : Tm ν Φ (n + 1)) :
    sequenceAborts t.underBinder = (sequenceAborts t).underBinder :=
  sequenceAborts_rename _ _

private theorem sequenceAborts_underTwoBinders (t : Tm ν Φ (n + 2)) :
    sequenceAborts t.underTwoBinders = (sequenceAborts t).underTwoBinders :=
  sequenceAborts_rename _ _

private theorem sequenceAborts_upSub (σ : Fin n → Tm ν Φ m) :
    (fun i => sequenceAborts (Tm.upSub σ i)) = Tm.upSub (fun i => sequenceAborts (σ i)) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  exact sequenceAborts_lift (σ j)

private theorem sequenceAborts_bsubst (σ : Fin n → Tm ν Φ m) (t : Tm ν Φ n) :
    sequenceAborts (Tm.bsubst σ t) = Tm.bsubst (fun i => sequenceAborts (σ i)) (sequenceAborts t) := by
  induction t generalizing m <;>
    simp only [sequenceAborts, Tm.bsubst, sequenceAborts_upSub, *]
  rfl

private theorem sequenceAborts_instantiate (b : Tm ν Φ (n + 1)) (a : Tm ν Φ n) :
    sequenceAborts (Tm.instantiate b a) = Tm.instantiate (sequenceAborts b) (sequenceAborts a) := by
  unfold Tm.instantiate
  rw [sequenceAborts_bsubst]
  exact Tm.bsubst_congr (fun i => Fin.cases rfl (fun _ => rfl) i) _

variable {τ : Type u} [TypeFormers τ] [HasTy Φ τ] [DecidableEq ν]
  {Γ : Isotope.Ctx ν τ} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}

theorem sequenceAborts_typing (h : HasType Φ Γ β t A) : HasType Φ Γ β (sequenceAborts t) A := by
  induction h with
  | fv h => exact .fv h
  | bv => exact .bv
  | op _ ih => exact .op ih
  | let₁ _ _ ih₁ ih₂ => exact .let₁ ih₁ ih₂
  | unit => exact .unit
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | let₂ _ _ ih₁ ih₂ => exact .let₂ ih₁ ih₂
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ih₁ ih₂ ih₃ => exact .case ih₁ ih₂ ih₃
  | abort _ ih => exact .let₁ ih (.abort .bv)
  | iter _ _ ih₁ ih₂ => exact .iter ih₁ ih₂

variable {ε : Type r} [HasEff Φ ε] {pe : ε}

omit [DecidableEq ν] in
theorem sequenceAborts_pure (h : Pure pe t) : Pure pe (sequenceAborts t) := by
  induction h with
  | fv => exact .fv
  | bv => exact .bv
  | op hf _ ih => exact .op hf ih
  | let₁ _ _ ih₁ ih₂ => exact .let₁ ih₁ ih₂
  | unit => exact .unit
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | let₂ _ _ ih₁ ih₂ => exact .let₂ ih₁ ih₂
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ih₁ ih₂ ih₃ => exact .case ih₁ ih₂ ih₃
  | abort _ ih => exact .let₁ ih (.abort .bv)

/-- The two typed lets can choose different types for the abort result. -/
private theorem sequenceAborts_emptyInitial {a : Tm ν Φ n} {b c : Tm ν Φ (n + 1)}
    (hl : HasType Φ Γ β (.let₁ (.abort a) b) A)
    (hr : HasType Φ Γ β (.let₁ (.abort a) c) A) :
    Equiv pe Γ β (sequenceAborts (.let₁ (.abort a) b)) (sequenceAborts (.let₁ (.abort a) c)) A := by
  cases hl with
  | let₁ hl hb =>
    cases hl with
    | abort ha =>
      cases hr with
      | let₁ hr hc =>
        cases hr with
        | abort _ =>
          have hn := sequenceAborts_typing ha
          have hbn := sequenceAborts_typing hb
          have hcn := sequenceAborts_typing hc
          have hz : HasType Φ Γ (β.snoc (empty : τ)) (.bv 0) (empty : τ) := .bv
          have inner := Equiv.ax (pureEff := pe) (.structural (.emptyInitial _ _ _))
            (.let₁ (.abort hz) (hbn.underBinder (X := empty)))
            (.let₁ (.abort hz) (hcn.underBinder (X := empty)))
          exact (Equiv.bindLet hn (.abort hz) hbn).trans
            ((Equiv.let₁ (.refl hn) inner).trans (Equiv.bindLet hn (.abort hz) hcn).symm)

private theorem sequenceAborts_axiom {a b : Tm ν Φ n}
    (ax : CoreAxiom pe a b) (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b A) :
    Equiv pe Γ β (sequenceAborts a) (sequenceAborts b) A := by
  have hleft := sequenceAborts_typing ha
  have hright := sequenceAborts_typing hb
  cases ax with
  | structural rule =>
    cases rule with
    | letBeta hp =>
      simp only [sequenceAborts, sequenceAborts_instantiate] at hleft hright ⊢
      exact .ax (.structural (.letBeta (sequenceAborts_pure hp))) hleft hright
    | letEta => exact .ax (.structural (.letEta _)) hleft hright
    | unitEta => exact .ax (.structural (.unitEta _)) hleft hright
    | pairBeta =>
      simp only [sequenceAborts, sequenceAborts_lift] at hleft hright ⊢
      exact .ax (.structural (.pairBeta _ _ _)) hleft hright
    | pairEta => exact .ax (.structural (.pairEta _)) hleft hright
    | caseBetaL => exact .ax (.structural (.caseBetaL _ _ _)) hleft hright
    | caseBetaR => exact .ax (.structural (.caseBetaR _ _ _)) hleft hright
    | caseEta => exact .ax (.structural (.caseEta _)) hleft hright
    | emptyInitial => exact sequenceAborts_emptyInitial ha hb
  | sequencing rule =>
    cases rule <;>
      simp only [sequenceAborts, sequenceAborts_underBinder, sequenceAborts_underTwoBinders]
        at hleft hright ⊢
    · exact .ax (.sequencing (.bindOp _ _)) hleft hright
    · exact .ax (.sequencing (.bindLet _ _ _)) hleft hright
    · exact .ax (.sequencing (.bindLetPair _ _ _)) hleft hright
    · exact .ax (.sequencing (.bindLetCase _ _ _ _)) hleft hright
    · exact .ax (.sequencing (.bindPair _ _)) hleft hright
    · exact .ax (.sequencing (.bindCase _ _ _)) hleft hright
  | iteration rule =>
    cases rule <;> simp only [sequenceAborts, sequenceAborts_underBinder] at hleft hright ⊢
    · exact .ax (.iteration (.fixpoint _ _)) hleft hright
    · exact .ax (.iteration (.naturality _ _ _)) hleft hright
    · exact .ax (.iteration (.codiagonal _ _)) hleft hright
    · exact .ax (.iteration (.iterBind _ _)) hleft hright

theorem sequenceAborts_exact {a b : Tm ν Φ n} (eq : Equiv pe Γ β a b A) :
    Equiv pe Γ β (sequenceAborts a) (sequenceAborts b) A := by
  induction eq with
  | refl h => exact .refl (sequenceAborts_typing h)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | op _ ih => exact .op ih
  | let₁ _ _ ih₁ ih₂ => exact .let₁ ih₁ ih₂
  | unit => exact .unit
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | let₂ _ _ ih₁ ih₂ => exact .let₂ ih₁ ih₂
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ih₁ ih₂ ih₃ => exact .case ih₁ ih₂ ih₃
  | abort _ ih => exact .let₁ ih (.abort (.refl .bv))
  | iter _ _ ih₁ ih₂ => exact .iter ih₁ ih₂
  | ax ax ha hb => exact sequenceAborts_axiom ax ha hb
  | uniformity ha hh hp hb hb' _ ih =>
    apply Equiv.uniformity (sequenceAborts_typing ha) (sequenceAborts_typing hh)
      (sequenceAborts_pure hp) (sequenceAborts_typing hb) (sequenceAborts_typing hb')
    simpa only [sequenceAborts, sequenceAborts_underBinder, sequenceAborts_instantiate] using ih

private theorem sequenceAborts_generator_forward {a : Tm ν Φ n}
    (h : HasType Φ Γ β a (empty : τ)) :
    Equiv pe Γ β (sequenceAborts (.abort a)) (sequenceAborts (.let₁ a (.abort (.bv 0)))) A := by
  have x : HasType Φ Γ (β.snoc (empty : τ)) (.bv 0) (empty : τ) := .bv
  have y : HasType Φ Γ ((β.snoc (empty : τ)).snoc (empty : τ)) (.bv 0) (empty : τ) := .bv
  exact .let₁ (.refl (sequenceAborts_typing h))
    (Equiv.letBeta (pureEff := pe) .bv x (.abort (C := A) y)).symm

theorem sequenceAborts_repaired {a b : Tm ν Φ n} (eq : AbortEquiv pe Γ β a b A) :
    Equiv pe Γ β (sequenceAborts a) (sequenceAborts b) A := by
  induction eq with
  | equiv h => exact sequenceAborts_exact h
  | primitive h _ _ =>
    cases h with
    | sequence ha => exact sequenceAborts_generator_forward ha
    | unsequence ha => exact (sequenceAborts_generator_forward ha).symm
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | op _ ih => exact .op ih
  | let₁ _ _ ih₁ ih₂ => exact .let₁ ih₁ ih₂
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | let₂ _ _ ih₁ ih₂ => exact .let₂ ih₁ ih₂
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ih₁ ih₂ ih₃ => exact .case ih₁ ih₂ ih₃
  | abort _ ih => exact .let₁ ih (.abort (.refl .bv))
  | iter _ _ ih₁ ih₂ => exact .iter ih₁ ih₂

theorem repaired_sequenceAborts (ht : HasType Φ Γ β t A) :
    AbortEquiv pe Γ β t (sequenceAborts t) A := by
  induction ht with
  | fv h => exact .refl (.fv h)
  | bv => exact .refl .bv
  | op _ ih => exact .op ih
  | let₁ _ _ ih₁ ih₂ => exact .let₁ ih₁ ih₂
  | unit => exact .refl .unit
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | let₂ _ _ ih₁ ih₂ => exact .let₂ ih₁ ih₂
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ih₁ ih₂ ih₃ => exact .case ih₁ ih₂ ih₃
  | abort h ih => exact (Refinement.abort ih).trans (AbortEquiv.sequence (sequenceAborts_typing h))
  | iter _ _ ih₁ ih₂ => exact .iter ih₁ ih₂

/-- The original repair is exactly equality of the sequenced translations in the exact theory. -/
theorem repaired_iff_sequenceAborts_exact {a b : Tm ν Φ n}
    (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b A) :
    AbortEquiv pe Γ β a b A ↔ Equiv pe Γ β (sequenceAborts a) (sequenceAborts b) A :=
  ⟨sequenceAborts_repaired, fun eq => (repaired_sequenceAborts ha).trans
    ((Refinement.equiv eq).trans (repaired_sequenceAborts hb).symm)⟩

/-- The pure-uniformity rule is admissible with a square in the existing AbortEquiv. -/
theorem repaired_uniformity {a : Tm ν Φ n} {h b b' : Tm ν Φ (n + 1)}
    {A' B : τ}
    (ha : HasType Φ Γ β a A)
    (hh : HasType Φ Γ (β.snoc A) h A') (hp : Pure pe h)
    (hb : HasType Φ Γ (β.snoc A) b (coprod B A))
    (hb' : HasType Φ Γ (β.snoc A') b' (coprod B A'))
    (square : AbortEquiv pe Γ (β.snoc A)
      (.case b (.inl (.bv (0 : Fin (n + 2)))) (.inr (Tm.underBinder h)))
      (Tm.instantiate (Tm.underBinder b') h) (coprod B A')) :
    AbortEquiv pe Γ β (.iter a b) (.iter (.let₁ a h) b') B := by
  apply (repaired_iff_sequenceAborts_exact (.iter ha hb) (.iter (.let₁ ha hh) hb')).mpr
  apply Equiv.uniformity (sequenceAborts_typing ha) (sequenceAborts_typing hh)
    (sequenceAborts_pure hp) (sequenceAborts_typing hb) (sequenceAborts_typing hb')
  simpa only [sequenceAborts, sequenceAborts_underBinder, sequenceAborts_instantiate] using
    sequenceAborts_repaired square

end Silmaril.Isotope.LetIter.LocallyNameless.AbortNormalization.Proofs
