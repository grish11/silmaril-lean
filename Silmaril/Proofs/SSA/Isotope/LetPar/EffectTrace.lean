module

public import Silmaril.SSA.Isotope.LetPar.EffectTrace.Defs
public import Silmaril.SSA.Isotope.LetPar.Native.Thms

public section

namespace Silmaril.Isotope.LetPar.EffectTrace.Proofs

open Parallel (Tier)

universe u v w r

variable {ν : Type w} {Φ : Type v} {ε : Type r} [HasEff Φ ε] [DecidableEq ε] {pureEff : ε}

private theorem seq_empty_left (a : Trace Φ) : seq empty a = a := by
  cases a <;> rfl

private theorem seq_empty_right (a : Trace Φ) : seq a empty = a := by
  cases a <;> simp [seq]

private theorem seq_assoc (a b c : Trace Φ) : seq (seq a b) c = seq a (seq b c) := by
  cases a <;> cases b <;> cases c <;> simp [seq, List.append_assoc]

private theorem par_empty_right (a : Trace Φ) : par a empty = a := by
  rcases a with _ | (_ | ⟨_, _⟩) <;> rfl

private theorem par_comm (a b : Trace Φ) : par a b = par b a := by
  rcases a with _ | (_ | ⟨_, _⟩) <;> rcases b with _ | (_ | ⟨_, _⟩) <;> rfl

private theorem par_assoc (a b c : Trace Φ) : par (par a b) c = par a (par b c) := by
  rcases a with _ | (_ | ⟨_, _⟩) <;> rcases b with _ | (_ | ⟨_, _⟩) <;>
    rcases c with _ | (_ | ⟨_, _⟩) <;> rfl

attribute [local simp] seq_empty_left seq_empty_right par_empty_right

variable {n m : Nat} {a b : Tm ν Φ n}

private theorem observe_rename (ρ : Fin n → Fin m) (t : Tm ν Φ n) :
    observe pureEff (t.rename ρ) = observe pureEff t := by
  induction t generalizing m <;> simp only [Parallel.Tm.rename, observe, *]

private theorem observe_pure (h : Parallel.Pure pureEff a) : observe pureEff a = empty := by
  induction h with
  | op hf _ ih =>
    simp [observe, instruction, IsPure] at hf ⊢
    simp [hf, ih]
  | fv | bv | unit => rfl
  | let₁ _ _ iha ihb | pair _ _ iha ihb | let₂ _ _ iha ihb | par _ _ iha ihb =>
    simp [observe, iha, ihb, par]
  | inl | inr | case | abort => exact False.elim (‹Tier.HasCase .seq› rfl)

private theorem observe_upSub {σ : Fin n → Tm ν Φ m}
    (h : ∀ i, observe pureEff (σ i) = empty) (i : Fin (n + 1)) :
    observe pureEff (Parallel.Tm.upSub σ i) = empty :=
  Fin.cases rfl (fun j => (observe_rename Fin.succ (σ j)).trans (h j)) i

private theorem observe_bsubst (t : Tm ν Φ n) (σ : Fin n → Tm ν Φ m)
    (h : ∀ i, observe pureEff (σ i) = empty) :
    observe pureEff (t.bsubst σ) = observe pureEff t := by
  induction t generalizing m with
  | fv | unit => rfl
  | bv i => exact h i
  | op _ _ ih => simp only [Parallel.Tm.bsubst, observe, ih σ h]
  | let₁ _ _ iha ihb => simp only [Parallel.Tm.bsubst, observe, iha σ h,
      ihb _ (observe_upSub h)]
  | let₂ _ _ iha ihb => simp only [Parallel.Tm.bsubst, observe, iha σ h,
      ihb _ (observe_upSub (observe_upSub h))]
  | pair _ _ iha ihb | par _ _ iha ihb => simp only [Parallel.Tm.bsubst, observe, iha σ h, ihb σ h]
  | inl | inr | case | abort => exact False.elim (‹Tier.HasCase .seq› rfl)
  | iter => exact nomatch ‹Tier.HasIter .seq›

private theorem observe_instantiate (t : Tm ν Φ (n + 1)) (h : Parallel.Pure pureEff a) :
    observe pureEff (t.instantiate a) = observe pureEff t :=
  observe_bsubst t _ (Fin.cases (observe_pure h) (fun _ => rfl))

private theorem observe_seqRule (h : Parallel.SeqRule pureEff a b) :
    observe pureEff a = observe pureEff b := by
  cases h with
  | letBeta hp => simp only [observe, observe_pure hp, seq_empty_left, observe_instantiate _ hp]
  | _ => simp [observe, seq_assoc, Parallel.Tm.lift, Parallel.Tm.underBinder,
      Parallel.Tm.underTwoBinders, observe_rename]

private theorem observe_parRule (h : Parallel.ParRule pureEff a b) :
    observe pureEff a = observe pureEff b := by
  cases h with
  | swap => simp [observe, Parallel.Tm.swap, par_comm]
  | assoc => simp [observe, Parallel.Tm.assoc, par_assoc]
  | purePair ha hb => simp [observe, observe_pure ha, observe_pure hb]
  | unitLeft => simp [observe, Parallel.Tm.dropLeft, par]
  | unitRight => simp [observe, Parallel.Tm.dropRight]
  | map hf hg => simp [observe, Parallel.Tm.leftResult, Parallel.Tm.underBinder,
      observe_rename, observe_pure hf, observe_pure hg]

section Equations

variable {τ : Type u} [HasProduct τ] [HasUnit τ] [DecidableEq ν] [HasTy Φ τ]
  {Γ : Ctx ν τ} {β : BoundCtx τ n} {A : τ}

/-- Every derivable LetPar equation preserves the trace, including proofs that use parallel terms
as intermediate terms. -/
theorem observe_equiv (h : LetPar.Equiv pureEff Γ β a b A) :
    observe pureEff a = observe pureEff b := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact ih.trans ik
  | op _ ih => simp only [observe, ih]
  | let₁ _ _ ih ik | let₂ _ _ ih ik | pair _ _ ih ik | par _ _ ih ik =>
    simp only [observe, ih, ik]
  | seqRule h _ _ => exact observe_seqRule h
  | parRule h _ _ => exact observe_parRule h
  | extraRule h _ _ => exact False.elim h
  | inl | inr | case | abort => exact False.elim (‹Tier.HasCase .seq› rfl)
  | iter => exact nomatch ‹Tier.HasIter .seq›

end Equations

/-- An effectful instruction word is observed in its original order. -/
theorem observe_word (fs : List Φ) (effectful : ∀ f ∈ fs, (instrEff f : ε) ≠ pureEff) :
    observe pureEff (LetPar.embed (word (ν := ν) (n := n) fs)) = some fs := by
  induction fs generalizing n with
  | nil => rfl
  | cons f fs ih =>
    have first := effectful f (List.mem_cons_self ..)
    have rest : ∀ g ∈ fs, (instrEff g : ε) ≠ pureEff := fun g hg => effectful g (List.mem_cons_of_mem _ hg)
    simp [word, LetPar.embed, observe, instruction, first, ih rest, seq]

variable {τ : Type u} [HasProduct τ] [HasUnit τ] [DecidableEq ν] [HasTy Φ τ]
  {Γ : Ctx ν τ} {β : BoundCtx τ n} {A : τ}

theorem word_hasType (fs : List Φ) (source : ∀ f ∈ fs, instrSrc f = (Silmaril.unit : τ)) :
    LetSeq.LocallyNameless.HasType Φ Γ β (word fs) Silmaril.unit := by
  induction fs generalizing n with
  | nil => exact .unit
  | cons f fs ih =>
    have argument : LetSeq.LocallyNameless.HasType Φ Γ β .unit (instrSrc f) := by
      rw [source f (List.mem_cons_self ..)]
      exact .unit
    exact .let₁ (.op argument) (ih fun g hg => source g (List.mem_cons_of_mem _ hg))

/-- Equations in the full parallel theory separate any two distinct effectful instruction words. -/
theorem word_eq_of_equiv {fs gs : List Φ}
    (effectfulF : ∀ f ∈ fs, (instrEff f : ε) ≠ pureEff)
    (effectfulG : ∀ g ∈ gs, (instrEff g : ε) ≠ pureEff)
    (h : LetPar.Equiv pureEff Γ β (LetPar.embed (word fs)) (LetPar.embed (word gs)) Silmaril.unit) :
    fs = gs := by
  have traceEq := observe_equiv h
  rw [observe_word fs effectfulF, observe_word gs effectfulG] at traceEq
  exact Option.some.inj traceEq

/-- The vertical inclusion reflects equations on effectful words fed a unit argument. -/
theorem word_equiv_iff {fs gs : List Φ}
    (source : ∀ f ∈ fs, instrSrc f = (Silmaril.unit : τ))
    (effectfulF : ∀ f ∈ fs, (instrEff f : ε) ≠ pureEff)
    (effectfulG : ∀ g ∈ gs, (instrEff g : ε) ≠ pureEff) :
    LetPar.Equiv pureEff Γ β (LetPar.embed (word fs)) (LetPar.embed (word gs)) Silmaril.unit ↔
      LetSeq.LocallyNameless.Equiv pureEff Γ β (word fs) (word gs) Silmaril.unit := by
  refine ⟨fun h => ?_, LetPar.embed_equiv⟩
  obtain rfl := word_eq_of_equiv effectfulF effectfulG h
  exact .refl (word_hasType fs source)


end Silmaril.Isotope.LetPar.EffectTrace.Proofs

namespace Silmaril.Isotope.LetPar.EffectTrace.Singleton.Proofs

open scoped Silmaril.Isotope.LetPar.EffectTrace.Singleton

open LetSeq.LocallyNameless (Tm HasType Pure)
open LetSeq.LocallyNameless.Equiv (bindLet bindOp bindPair letBeta pairBeta pairEta unitEta)

universe v r

variable {Φ : Type v} {ε : Type r} [HasEff Φ ε] {pe : ε}
local notation "Γ" => (Ctx.nil : Ctx Empty Unit)

local notation "SeqTm" => LetSeq.LocallyNameless.Tm Empty Φ

variable {n : Nat} {β : BoundCtx Unit n}

private theorem typed (t : SeqTm n) : HasType Φ Γ β t Silmaril.unit := by
  induction t with
  | fv x => exact x.elim
  | bv => exact .bv
  | unit => exact .unit
  | op _ _ ih => exact .op ih
  | let₁ _ _ iha ihb => exact .let₁ iha ihb
  | pair _ _ iha ihb => exact .pair iha ihb
  | let₂ _ _ iha ihb => exact .let₂ (A := ()) (B := ()) iha ihb

private theorem refl_term (t : SeqTm n) : LetSeq.LocallyNameless.Equiv pe Γ β t t Silmaril.unit :=
  .refl (typed t)

private theorem pure_unit {t : SeqTm n} (h : Pure pe t) : LetSeq.LocallyNameless.Equiv pe Γ β t .unit Silmaril.unit :=
  (unitEta (typed t)).symm.trans (letBeta h (typed t) .unit)

private theorem word_rename {m : Nat} (ρ : Fin n → Fin m) (fs : List Φ) :
    (word (ν := Empty) fs).rename ρ = word fs := by
  induction fs generalizing n m <;> simp [word, Tm.rename, *]

private theorem word_bsubst {m : Nat} (σ : Fin n → SeqTm m) (fs : List Φ) :
    (word fs).bsubst σ = word fs := by
  induction fs generalizing n m <;> simp [word, Tm.bsubst, *]

private theorem let_unit_word (fs : List Φ) :
    LetSeq.LocallyNameless.Equiv pe Γ β (.let₁ .unit (word fs)) (word fs) Silmaril.unit := by
  simpa only [Tm.instantiate, word_bsubst] using
    (letBeta (β := β) (.unit : Pure pe (.unit : SeqTm n)) .unit (typed (word fs)))

private theorem bind_words (fs gs : List Φ) :
    LetSeq.LocallyNameless.Equiv pe Γ β (.let₁ (word fs) (word gs)) (word (fs ++ gs)) Silmaril.unit := by
  induction fs generalizing n with
  | nil => exact let_unit_word gs
  | cons f fs ih =>
    have h := bindLet (c := word gs) (typed (β := β) (.op f .unit))
      (typed (word fs)) (typed (word gs)) (pureEff := pe)
    rw [Tm.underBinder, word_rename] at h
    exact h.trans (LetSeq.LocallyNameless.Equiv.let₁ (refl_term _) (ih (β := .snoc β Silmaril.unit)))

private theorem op_as_let (f : Φ) (a : SeqTm n) :
    LetSeq.LocallyNameless.Equiv pe Γ β (.op f a) (.let₁ a (.op f .unit)) Silmaril.unit := by
  refine (unitEta (typed (.op f a))).symm.trans ?_
  refine (bindOp (f := f) (typed a) .unit).trans (LetSeq.LocallyNameless.Equiv.let₁ (refl_term a) ?_)
  exact (unitEta (typed (.op f (.bv 0)))).trans (.op (pure_unit .bv))

private theorem pair_words (fs gs : List Φ) :
    LetSeq.LocallyNameless.Equiv pe Γ β (.pair (word fs) (word gs)) (word (fs ++ gs)) Silmaril.unit := by
  refine (pairEta (A := ()) (B := ()) (typed (.pair (word fs) (word gs)))).symm.trans ?_
  have beta := pairBeta (β := β) (typed (word fs)) (typed (word gs))
    (typed (.pair (.bv 1) (.bv 0))) (pureEff := pe)
  rw [Tm.lift, word_rename] at beta
  have discardResult : LetSeq.LocallyNameless.Equiv pe Γ (.snoc β Silmaril.unit)
      (.let₁ (word gs) (.pair (.bv 1) (.bv 0))) (word gs) Silmaril.unit :=
    (LetSeq.LocallyNameless.Equiv.let₁ (refl_term (word gs)) (pure_unit (.pair .bv .bv))).trans
      (unitEta (typed (word gs)))
  exact beta.trans
    ((LetSeq.LocallyNameless.Equiv.let₁ (refl_term (word fs)) discardResult).trans (bind_words fs gs))

private theorem let₂_words (fs gs : List Φ) :
    LetSeq.LocallyNameless.Equiv pe Γ β (.let₂ (word fs) (word gs)) (word (fs ++ gs)) Silmaril.unit := by
  have bound := bindPair (A := ()) (B := ()) (β := β) (typed (word fs)) (typed (word gs)) (pureEff := pe)
  rw [Tm.underTwoBinders, word_rename] at bound
  refine bound.trans ?_
  refine (LetSeq.LocallyNameless.Equiv.let₁ (refl_term (word fs)) ?_).trans (bind_words fs gs)
  have binderAsPair : LetSeq.LocallyNameless.Equiv (Φ := Φ) pe Γ (.snoc β Silmaril.unit)
      (.bv 0) (.pair .unit .unit) Silmaril.unit :=
    (pure_unit .bv).trans (pure_unit (.pair .unit .unit)).symm
  refine (LetSeq.LocallyNameless.Equiv.let₂ (A := ()) (B := ()) binderAsPair
    (refl_term (word gs))).trans ?_
  refine (pairBeta (typed .unit) (typed .unit) (typed (word gs))).trans ?_
  exact (LetSeq.LocallyNameless.Equiv.let₁ (refl_term .unit) (let_unit_word gs)).trans (let_unit_word gs)

private abbrev Effectful (pe : ε) (fs : List Φ) := ∀ f ∈ fs, (instrEff f : ε) ≠ pe

private theorem append_effectful {fs gs : List Φ} (hf : Effectful pe fs) (hg : Effectful pe gs) :
    Effectful pe (fs ++ gs) :=
  fun f hmem => (List.mem_append.1 hmem).elim (hf f) (hg f)

variable [DecidableEq ε]

private theorem normalize (t : SeqTm n) :
    ∃ fs, Effectful pe fs ∧ LetSeq.LocallyNameless.Equiv pe Γ β t (word fs) Silmaril.unit := by
  induction t with
  | fv x => exact x.elim
  | bv => exact ⟨[], by simp [Effectful], pure_unit .bv⟩
  | unit => exact ⟨[], by simp [Effectful], .unit⟩
  | op f a ih =>
    obtain ⟨fs, effects, eq⟩ := ih (β := β)
    by_cases h : (instrEff f : ε) = pe
    · refine ⟨fs, effects, (op_as_let f a).trans ?_⟩
      exact (LetSeq.LocallyNameless.Equiv.let₁ (refl_term a) (pure_unit (.op h .unit))).trans
        ((unitEta (typed a)).trans eq)
    · have letter : Effectful pe [f] := by
        intro g hg
        cases List.mem_singleton.mp hg
        exact h
      refine ⟨fs ++ [f], append_effectful effects letter, (op_as_let f a).trans ?_⟩
      exact (LetSeq.LocallyNameless.Equiv.let₁ eq (unitEta (typed (.op f .unit))).symm).trans
        (bind_words fs [f])
  | let₁ _ _ iha ihb =>
    obtain ⟨fs, hf, ea⟩ := iha (β := β)
    obtain ⟨gs, hg, eb⟩ := ihb (β := .snoc β Silmaril.unit)
    exact ⟨fs ++ gs, append_effectful hf hg, (LetSeq.LocallyNameless.Equiv.let₁ ea eb).trans (bind_words fs gs)⟩
  | pair _ _ iha ihb =>
    obtain ⟨fs, hf, ea⟩ := iha (β := β)
    obtain ⟨gs, hg, eb⟩ := ihb (β := β)
    exact ⟨fs ++ gs, append_effectful hf hg, (LetSeq.LocallyNameless.Equiv.pair ea eb).trans (pair_words fs gs)⟩
  | let₂ _ _ iha ihb =>
    obtain ⟨fs, hf, ea⟩ := iha (β := β)
    obtain ⟨gs, hg, eb⟩ := ihb (β := .snoc (.snoc β Silmaril.unit) Silmaril.unit)
    exact ⟨fs ++ gs, append_effectful hf hg,
      (LetSeq.LocallyNameless.Equiv.let₂ (A := ()) (B := ()) ea eb).trans (let₂_words fs gs)⟩

/-- The trace is a complete invariant for the native terms over the single object type. -/
theorem observe_eq_iff {a b : SeqTm n} :
    observe pe (LetPar.embed a) = observe pe (LetPar.embed b) ↔
      LetSeq.LocallyNameless.Equiv pe Γ β a b Silmaril.unit := by
  refine ⟨fun h => ?_, fun eq => EffectTrace.Proofs.observe_equiv (LetPar.embed_equiv eq)⟩
  obtain ⟨fs, ef, ea⟩ := normalize (β := β) (pe := pe) a
  obtain ⟨gs, eg, eb⟩ := normalize (β := β) (pe := pe) b
  rw [EffectTrace.Proofs.observe_equiv (LetPar.embed_equiv ea),
    EffectTrace.Proofs.observe_equiv (LetPar.embed_equiv eb),
    EffectTrace.Proofs.observe_word fs ef, EffectTrace.Proofs.observe_word gs eg] at h
  obtain rfl := Option.some.inj h
  exact ea.trans eb.symm

end Silmaril.Isotope.LetPar.EffectTrace.Singleton.Proofs
