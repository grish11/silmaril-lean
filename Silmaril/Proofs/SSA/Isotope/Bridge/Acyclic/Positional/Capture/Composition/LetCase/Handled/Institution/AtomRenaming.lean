module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Defs

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open LetSeq.StraightLine.Structural (Slot Assembly)
open scoped LetSeq.StraightLine.Structural Tagged

variable {α Φ : Type} {L : List (Ty α)}

/-! ## Renaming of exits and payloads -/

section Terms

variable {n : Nat} {β : BoundCtx (Ty α) n}

/-- Renaming commutes with returning at an exit. -/
theorem exit_term_rename_proof {A : Ty α} (e : ExitAt L A) {m : Nat} (ξ : Fin n → Fin m)
    (t : LetCase.LocallyNameless.Tm Empty Φ n) : (e.term t).rename ξ = e.term (t.rename ξ) := by
  induction e with
  | here => rfl
  | there later ih => exact congrArg LetCase.LocallyNameless.Tm.inr ih

/-- Renaming commutes with assembling a payload. -/
theorem argTerm_rename_proof {A : Ty α} (p : Assembly β A) {m : Nat} {γ : BoundCtx (Ty α) m}
    (ρ : BoundCtx.Renaming β γ) :
    (argTerm (Φ := Φ) p).rename ρ.toFun = argTerm (p.rename ρ) := by
  induction p with
  | atom s => rfl
  | unit => rfl
  | pair a b iha ihb => exact congrArg₂ LetCase.LocallyNameless.Tm.pair iha ihb

end Terms

/-! ## Renamings -/

section Algebra

variable [TaggedSignature α Φ] {n m k : Nat} {β : BoundCtx (Ty α) n} {γ : BoundCtx (Ty α) m}
  {δ : BoundCtx (Ty α) k}

omit [TaggedSignature α Φ] in
/-- Two renamings with the same function are equal. -/
theorem renaming_ext_proof {ρ π : BoundCtx.Renaming β γ} (same : ∀ i, ρ.toFun i = π.toFun i) : ρ = π := by
  cases ρ
  cases π
  congr
  funext i
  exact same i

omit [TaggedSignature α Φ] in
/-- Lifting under a new slot commutes with composition. -/
theorem renaming_up_comp_proof (ρ : BoundCtx.Renaming β γ) (π : BoundCtx.Renaming γ δ) (X : Ty α) :
    (ρ.up X).comp (π.up X) = (ρ.comp π).up X :=
  renaming_ext_proof (Fin.cases rfl (fun _ => rfl))

omit [TaggedSignature α Φ] in
/-- Renaming an assembled payload twice is renaming along the composite. -/
theorem assembly_rename_comp_proof {A : Ty α} (p : Assembly β A) (ρ : BoundCtx.Renaming β γ)
    (π : BoundCtx.Renaming γ δ) : (p.rename ρ).rename π = p.rename (ρ.comp π) := by
  induction p with
  | atom s => rfl
  | unit => rfl
  | pair a b iha ihb => exact congrArg₂ Assembly.pair iha ihb

end Algebra

/-! ## The renaming action on case trees -/

variable [TaggedSignature α Φ]

theorem renamed_term_proof {pending : Pending α} {n : Nat} {β : BoundCtx (Ty α) n}
    {t : LetCase.LocallyNameless.Tm Empty Φ n} (tree : CaseTree pending β L t) :
    ∀ {m : Nat} {γ : BoundCtx (Ty α) m} (ρ : CaseTree.Along pending β γ),
      CaseTree.RenamedTerm pending β γ t ρ (tree.renamed ρ) := by
  induction tree with
  | ret exit payload =>
    intro m γ ρ
    exact ((exit_term_rename_proof exit ρ.toFun _).trans (congrArg exit.term (argTerm_rename_proof payload ρ))).symm
  | ask f argument reply ih =>
    intro m γ ρ
    exact congrArg₂ LetCase.LocallyNameless.Tm.let₁
      (congrArg (LetCase.LocallyNameless.Tm.op f) (argTerm_rename_proof argument ρ).symm) (ih ρ)
  | only atoms payload ih => exact fun ρ => ih ρ
  | split atoms next rest left right ihl ihr =>
    intro m γ ρ
    exact congrArg₂ (LetCase.LocallyNameless.Tm.case (.bv 0)) (ihl (ρ.up _)) (ihr (ρ.up _))
  | unit body ih => exact fun ρ => ih (ρ.up _)
  | atom a body ih => exact fun ρ => ih (ρ.up _)
  | pair a b rest later ih =>
    intro m γ ρ
    exact congrArg (LetCase.LocallyNameless.Tm.let₂ (.bv 0)) (ih ((ρ.up _).up _))

theorem renamed_comp_proof {pending : Pending α} {n : Nat} {β : BoundCtx (Ty α) n}
    {t : LetCase.LocallyNameless.Tm Empty Φ n} (tree : CaseTree pending β L t) :
    CaseTree.RenamedComp pending β tree := by
  induction tree with
  | ret exit payload =>
    intro m γ k δ ρ π
    simp only [CaseTree.renamed]
    rw [assembly_rename_comp_proof]
  | ask f argument reply ih =>
    intro m γ k δ ρ π
    have h := ih ρ π
    simp only [CaseTree.renamed]
    rw [assembly_rename_comp_proof, h]
  | only atoms payload ih =>
    intro m γ k δ ρ π
    have h := ih ρ π
    simp only [CaseTree.renamed]
    rw [h]
  | split atoms next rest left right ihl ihr =>
    intro m γ k δ ρ π
    have hl := ihl (ρ.up _) (π.up _)
    have hr := ihr (ρ.up _) (π.up _)
    rw [renaming_up_comp_proof] at hl hr
    simp only [CaseTree.renamed]
    rw [hl, hr]
  | unit body ih =>
    intro m γ k δ ρ π
    have h := ih (ρ.up _) (π.up _)
    rw [renaming_up_comp_proof] at h
    simp only [CaseTree.renamed]
    rw [h]
  | atom a body ih =>
    intro m γ k δ ρ π
    have h := ih (ρ.up _) (π.up _)
    rw [renaming_up_comp_proof] at h
    simp only [CaseTree.renamed]
    rw [h]
  | pair a b rest later ih =>
    intro m γ k δ ρ π
    have h := ih ((ρ.up _).up _) ((π.up _).up _)
    rw [renaming_up_comp_proof, renaming_up_comp_proof] at h
    simp only [CaseTree.renamed]
    rw [h]

/-! ## Telescopes -/

section Tele

omit [TaggedSignature α Φ]

/-- Lifting under a telescope commutes with composition. -/
theorem upTele_comp_proof : (tel : List (Ty α)) → {k j i : Nat} → {Ω : BoundCtx (Ty α) k} →
    {Ω' : BoundCtx (Ty α) j} → {Ω'' : BoundCtx (Ty α) i} → (ρ : BoundCtx.Renaming Ω Ω') →
    (π : BoundCtx.Renaming Ω' Ω'') → (upTele ρ tel).comp (upTele π tel) = upTele (ρ.comp π) tel
  | [], _, _, _, _, _, _, _, _ => rfl
  | X :: tel, _, _, _, _, _, _, ρ, π =>
    (upTele_comp_proof tel (ρ.up X) (π.up X)).trans (congrArg (fun r => upTele r tel) (renaming_up_comp_proof ρ π X))

/-- Weakening past a telescope commutes with renaming. -/
theorem weakenTele_natural_proof : (tel : List (Ty α)) → {k j : Nat} → {Ω : BoundCtx (Ty α) k} →
    {Ω' : BoundCtx (Ty α) j} → (ρ : BoundCtx.Renaming Ω Ω') →
    (weakenTele Ω tel).comp (upTele ρ tel) = ρ.comp (weakenTele Ω' tel)
  | [], _, _, _, _, _ => rfl
  | X :: tel, _, _, Ω, Ω', ρ => by
    have ih := weakenTele_natural_proof tel (ρ.up X)
    show (BoundCtx.Renaming.succ Ω X).comp ((weakenTele (Ω.snoc X) tel).comp (upTele (ρ.up X) tel)) = _
    rw [ih]
    rfl

/-- Exchanging two slots commutes with renaming beneath them. -/
theorem swapRenaming_natural_proof {k j : Nat} {Ω : BoundCtx (Ty α) k} {Ω' : BoundCtx (Ty α) j}
    (ω : BoundCtx.Renaming Ω Ω') (X T : Ty α) :
    (swapRenaming Ω X T).comp ((ω.up T).up X) = ((ω.up X).up T).comp (swapRenaming Ω' X T) :=
  renaming_ext_proof (Fin.cases rfl (fun i => Fin.cases rfl (fun _ => rfl) i))

/-- Moving a slot beneath a telescope commutes with renaming. -/
theorem swapTele_natural_proof : (tel : List (Ty α)) → {k j : Nat} → {Ω : BoundCtx (Ty α) k} →
    {Ω' : BoundCtx (Ty α) j} → (ω : BoundCtx.Renaming Ω Ω') → (T : Ty α) →
    (swapTele Ω tel T).comp (upTele (ω.up T) tel) = ((upTele ω tel).up T).comp (swapTele Ω' tel T)
  | [], _, _, _, _, _, _ => rfl
  | X :: tel, _, _, Ω, Ω', ω, T => by
    have ih := swapTele_natural_proof tel (ω.up X) T
    show (swapTele (Ω.snoc X) tel T).comp ((upTele (swapRenaming Ω X T) tel).comp
      (upTele ((ω.up T).up X) tel)) =
      ((upTele (ω.up X) tel).up T).comp ((swapTele (Ω'.snoc X) tel T).comp (upTele (swapRenaming Ω' X T) tel))
    rw [upTele_comp_proof, swapRenaming_natural_proof, ← upTele_comp_proof]
    show ((swapTele (Ω.snoc X) tel T).comp (upTele ((ω.up X).up T) tel)).comp
      (upTele (swapRenaming Ω' X T) tel) = _
    rw [ih]
    rfl

/-- Weakening past a telescope, under a new slot, and then moving the slot
beneath the telescope, is weakening past the telescope over the slot. -/
theorem swapTele_weaken_proof : (tel : List (Ty α)) → {k : Nat} → (Ω : BoundCtx (Ty α) k) → (T : Ty α) →
    ((weakenTele Ω tel).up T).comp (swapTele Ω tel T) = weakenTele (Ω.snoc T) tel
  | [], _, _, _ => renaming_ext_proof (Fin.cases rfl (fun _ => rfl))
  | X :: tel, _, Ω, T => by
    have ih := swapTele_weaken_proof tel (Ω.snoc X) T
    have nat := weakenTele_natural_proof tel (swapRenaming Ω X T)
    have split : (weakenTele Ω (X :: tel)).up T =
        ((BoundCtx.Renaming.succ Ω X).up T).comp ((weakenTele (Ω.snoc X) tel).up T) :=
      (renaming_up_comp_proof _ _ T).symm
    show ((weakenTele Ω (X :: tel)).up T).comp ((swapTele (Ω.snoc X) tel T).comp
      (upTele (swapRenaming Ω X T) tel)) = _
    rw [split]
    show ((BoundCtx.Renaming.succ Ω X).up T).comp
      ((((weakenTele (Ω.snoc X) tel).up T).comp (swapTele (Ω.snoc X) tel T)).comp
        (upTele (swapRenaming Ω X T) tel)) = _
    rw [ih, nat]
    exact renaming_ext_proof (fun i => by
      show (weakenTele ((Ω.snoc T).snoc X) tel).toFun
        ((swapRenaming Ω X T).toFun (((BoundCtx.Renaming.succ Ω X).up T).toFun i)) = _
      exact congrArg _ (Fin.cases rfl (fun _ => rfl) i))

/-- Moving two slots beneath a telescope commutes with renaming. -/
theorem pairPastTele_natural_proof (tel : List (Ty α)) {k j : Nat} {Ω : BoundCtx (Ty α) k}
    {Ω' : BoundCtx (Ty α) j} (ω : BoundCtx.Renaming Ω Ω') (A B : Ty α) :
    (pairPastTele Ω tel A B).comp (upTele ((ω.up A).up B) tel) =
      (((upTele ω tel).up A).up B).comp (pairPastTele Ω' tel A B) := by
  have first := swapTele_natural_proof tel ω A
  have second := swapTele_natural_proof tel (ω.up A) B
  show ((swapTele Ω tel A).up B).comp ((swapTele (Ω.snoc A) tel B).comp (upTele ((ω.up A).up B) tel)) = _
  rw [second]
  show (((swapTele Ω tel A).up B).comp ((upTele (ω.up A) tel).up B)).comp (swapTele (Ω'.snoc A) tel B) = _
  rw [renaming_up_comp_proof, first, ← renaming_up_comp_proof]
  rfl

/-- Moving two slots beneath a telescope with one more oldest slot: move
them beneath the rest, then beneath that slot. -/
theorem pairPastTele_cons_proof (tel : List (Ty α)) {k : Nat} (Ω : BoundCtx (Ty α) k) (X A B : Ty α) :
    pairPastTele Ω (X :: tel) A B =
      (pairPastTele (Ω.snoc X) tel A B).comp (upTele (afterPairRenaming Ω X A B) tel) := by
  have nat := swapTele_natural_proof tel (swapRenaming Ω X A) B
  have split : afterPairRenaming Ω X A B =
      ((swapRenaming Ω X A).up B).comp (swapRenaming (Ω.snoc A) X B) :=
    renaming_ext_proof (Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun _ => rfl) i) i))
  show (((swapTele (Ω.snoc X) tel A).comp (upTele (swapRenaming Ω X A) tel)).up B).comp
    ((swapTele ((Ω.snoc A).snoc X) tel B).comp (upTele (swapRenaming (Ω.snoc A) X B) tel)) = _
  rw [← renaming_up_comp_proof]
  show ((swapTele (Ω.snoc X) tel A).up B).comp
    ((((upTele (swapRenaming Ω X A) tel).up B).comp (swapTele ((Ω.snoc A).snoc X) tel B)).comp
      (upTele (swapRenaming (Ω.snoc A) X B) tel)) = _
  rw [← nat, split, ← upTele_comp_proof]
  rfl

/-- The two pairs of slots move past each other in two steps. -/
theorem afterPairPair_split_proof {k : Nat} (Γ : BoundCtx (Ty α) k) (C D A B : Ty α) :
    afterPairPairRenaming Γ C D A B =
      (afterPairRenaming (Γ.snoc C) D A B).comp ((afterPairRenaming Γ C A B).up D) :=
  renaming_ext_proof (Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl
    (fun i => Fin.cases rfl (fun _ => rfl) i) i) i))

/-- Lifting the identity under a telescope is the identity. -/
theorem upTele_id_proof : (tel : List (Ty α)) → {k : Nat} → (Ω : BoundCtx (Ty α) k) →
    upTele (BoundCtx.Renaming.id Ω) tel = .id _
  | [], _, _ => rfl
  | X :: tel, _, Ω =>
    (congrArg (fun r => upTele r tel)
      (renaming_ext_proof (ρ := (BoundCtx.Renaming.id Ω).up X) (π := .id _) (Fin.cases rfl (fun _ => rfl)))).trans
      (upTele_id_proof tel (Ω.snoc X))

/-- Moving two slots beneath one slot is the move of three slots. -/
theorem pairPastTele_single_proof {k : Nat} (Ω : BoundCtx (Ty α) k) (X A B : Ty α) :
    pairPastTele Ω [X] A B = afterPairRenaming Ω X A B :=
  renaming_ext_proof (Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun _ => rfl) i) i))

/-- The newest of two slots moved beneath a telescope lands where
weakening past the telescope puts it. -/
theorem pairPastTele_zero_proof (tel : List (Ty α)) {k : Nat} (Ω : BoundCtx (Ty α) k) (A B : Ty α) :
    (pairPastTele Ω tel A B).toFun 0 = (weakenTele ((Ω.snoc A).snoc B) tel).toFun 0 :=
  congrArg (fun r => r.toFun 0) (swapTele_weaken_proof tel (Ω.snoc A) B)

/-- Moving a telescope beneath a telescope commutes with renaming. -/
theorem swapTeles_natural_proof : (H : List (Ty α)) → {k j : Nat} → {Ω : BoundCtx (Ty α) k} →
    {Ω' : BoundCtx (Ty α) j} → (tel : List (Ty α)) → (ω : BoundCtx.Renaming Ω Ω') →
    (swapTeles Ω tel H).comp (upTele (upTele ω H) tel) = (upTele (upTele ω tel) H).comp (swapTeles Ω' tel H)
  | [], _, _, _, _, _, _ => rfl
  | X :: H, _, _, Ω, Ω', tel, ω => by
    have ih := swapTeles_natural_proof H tel (ω.up X)
    show (upTele (swapTele Ω tel X) H).comp ((swapTeles (Ω.snoc X) tel H).comp
      (upTele (upTele (ω.up X) H) tel)) = _
    rw [ih]
    show ((upTele (swapTele Ω tel X) H).comp (upTele (upTele (ω.up X) tel) H)).comp _ = _
    rw [upTele_comp_proof, swapTele_natural_proof, ← upTele_comp_proof]
    rfl

/-- Moving a telescope that starts with two slots: move the two slots,
then the rest. -/
theorem swapTeles_pair_proof (H : List (Ty α)) {k : Nat} (Ω : BoundCtx (Ty α) k) (tel : List (Ty α))
    (A B : Ty α) :
    swapTeles Ω tel (A :: B :: H) =
      (upTele (pairPastTele Ω tel A B) H).comp (swapTeles ((Ω.snoc A).snoc B) tel H) := by
  show _ = (upTele (((swapTele Ω tel A).up B).comp (swapTele (Ω.snoc A) tel B)) H).comp _
  rw [← upTele_comp_proof]
  rfl

/-- Moving a telescope beneath a telescope with one more oldest slot: move
it beneath the rest, then beneath that slot. -/
theorem swapTeles_cons_proof : (H : List (Ty α)) → {k : Nat} → (Ω : BoundCtx (Ty α) k) → (X : Ty α) →
    (tel : List (Ty α)) →
    swapTeles Ω (X :: tel) H = (swapTeles (Ω.snoc X) tel H).comp (upTele (swapTeles Ω [X] H) tel)
  | [], _, Ω, X, tel => by
    show BoundCtx.Renaming.id _ = (BoundCtx.Renaming.id _).comp (upTele (BoundCtx.Renaming.id (Ω.snoc X)) tel)
    rw [upTele_id_proof]
    rfl
  | T :: H, _, Ω, X, tel => by
    have ih := swapTeles_cons_proof H (Ω.snoc T) X tel
    have nat := swapTeles_natural_proof H tel (swapRenaming Ω X T)
    let U := upTele (swapTele (Ω.snoc X) tel T) H
    let V := upTele (upTele (swapRenaming Ω X T) tel) H
    let W := swapTeles ((Ω.snoc T).snoc X) tel H
    let W' := swapTeles ((Ω.snoc X).snoc T) tel H
    let V' := upTele (upTele (swapRenaming Ω X T) H) tel
    let S : BoundCtx.Renaming (extendCtx ((Ω.snoc T).snoc X) H) ((extendCtx (Ω.snoc T) H).snoc X) :=
      swapTeles (Ω.snoc T) [X] H
    let Z := upTele S tel
    have eA : upTele ((swapTele (Ω.snoc X) tel T).comp (upTele (swapRenaming Ω X T) tel)) H = U.comp V :=
      (upTele_comp_proof H _ _).symm
    have eD : upTele ((upTele (swapRenaming Ω X T) H).comp S) tel = V'.comp Z :=
      (upTele_comp_proof tel (upTele (swapRenaming Ω X T) H) S).symm
    have step1 : swapTeles Ω (X :: tel) (T :: H) = (U.comp V).comp (W.comp Z) :=
      congrArg₂ (fun x y => BoundCtx.Renaming.comp x y) eA ih
    have step2 : (swapTeles (Ω.snoc X) tel (T :: H)).comp (upTele (swapTeles Ω [X] (T :: H)) tel) =
        (U.comp W').comp (V'.comp Z) :=
      congrArg (fun r => (U.comp W').comp r) eD
    have mid : (U.comp V).comp (W.comp Z) = (U.comp W').comp (V'.comp Z) :=
      congrArg (fun r => U.comp (BoundCtx.Renaming.comp r Z)) nat.symm
    exact step1.trans (mid.trans step2.symm)

/-- Weakening past a telescope over a slot, and then moving the telescope
beneath the slot, is weakening past the telescope under the slot. -/
theorem swapTeles_weaken_proof : (H : List (Ty α)) → {k : Nat} → (Ω : BoundCtx (Ty α) k) → (T : Ty α) →
    (weakenTele (Ω.snoc T) H).comp (swapTeles Ω [T] H) = (weakenTele Ω H).up T
  | [], _, _, _ => renaming_ext_proof (Fin.cases rfl (fun _ => rfl))
  | X :: H, _, Ω, T => by
    have ih := swapTeles_weaken_proof H (Ω.snoc X) T
    have nat := weakenTele_natural_proof H (swapRenaming Ω T X)
    show (BoundCtx.Renaming.succ (Ω.snoc T) X).comp
      (((weakenTele ((Ω.snoc T).snoc X) H).comp (upTele (swapRenaming Ω T X) H)).comp
        (swapTeles (Ω.snoc X) [T] H)) = _
    rw [nat]
    show ((BoundCtx.Renaming.succ (Ω.snoc T) X).comp (swapRenaming Ω T X)).comp
      ((weakenTele ((Ω.snoc X).snoc T) H).comp (swapTeles (Ω.snoc X) [T] H)) = _
    rw [ih]
    exact renaming_ext_proof (fun i => by
      show ((weakenTele (Ω.snoc X) H).up T).toFun
        ((swapRenaming Ω T X).toFun i.succ) = _
      exact Fin.cases rfl (fun _ => rfl) i)

/-- Weakening past a telescope, under two new slots, and then moving the
two slots beneath the telescope, is weakening past the telescope over the
two slots. -/
theorem pairPastTele_weaken_proof (tel : List (Ty α)) {k : Nat} (Ω : BoundCtx (Ty α) k) (A B : Ty α) :
    (((weakenTele Ω tel).up A).up B).comp (pairPastTele Ω tel A B) = weakenTele ((Ω.snoc A).snoc B) tel :=
  (congrArg (fun r => BoundCtx.Renaming.comp r (swapTele (Ω.snoc A) tel B))
    ((renaming_up_comp_proof ((weakenTele Ω tel).up A) (swapTele Ω tel A) B).trans
      (congrArg (fun r : BoundCtx.Renaming _ _ => r.up B) (swapTele_weaken_proof tel Ω A)))).trans
    (swapTele_weaken_proof tel (Ω.snoc A) B)

/-- Weakening past two telescopes and then exchanging them is weakening
past them in the other order. -/
theorem swapTeles_weakenTele_proof : (H : List (Ty α)) → {k : Nat} → (Ω : BoundCtx (Ty α) k) →
    (tel : List (Ty α)) →
    ((weakenTele Ω tel).comp (weakenTele (extendCtx Ω tel) H)).comp (swapTeles Ω tel H) =
      (weakenTele Ω H).comp (weakenTele (extendCtx Ω H) tel)
  | [], _, _, _ => rfl
  | X :: H, _, Ω, tel => by
    have ih := swapTeles_weakenTele_proof H (Ω.snoc X) tel
    have nat := weakenTele_natural_proof H (swapTele Ω tel X)
    have sw := swapTele_weaken_proof tel Ω X
    have step1 : ((weakenTele Ω tel).comp (weakenTele (extendCtx Ω tel) (X :: H))).comp
        (swapTeles Ω tel (X :: H)) =
        (((weakenTele Ω tel).comp (BoundCtx.Renaming.succ (extendCtx Ω tel) X)).comp
          ((swapTele Ω tel X).comp (weakenTele (extendCtx (Ω.snoc X) tel) H))).comp
            (swapTeles (Ω.snoc X) tel H) :=
      congrArg (fun r => BoundCtx.Renaming.comp
        (((weakenTele Ω tel).comp (BoundCtx.Renaming.succ (extendCtx Ω tel) X)).comp r)
        (swapTeles (Ω.snoc X) tel H)) nat
    have step2 : (((weakenTele Ω tel).comp (BoundCtx.Renaming.succ (extendCtx Ω tel) X)).comp
          ((swapTele Ω tel X).comp (weakenTele (extendCtx (Ω.snoc X) tel) H))).comp
            (swapTeles (Ω.snoc X) tel H) =
        (BoundCtx.Renaming.succ Ω X).comp (((weakenTele (Ω.snoc X) tel).comp
          (weakenTele (extendCtx (Ω.snoc X) tel) H)).comp (swapTeles (Ω.snoc X) tel H)) :=
      congrArg (fun r => BoundCtx.Renaming.comp (BoundCtx.Renaming.succ Ω X)
        ((BoundCtx.Renaming.comp r (weakenTele (extendCtx (Ω.snoc X) tel) H)).comp
          (swapTeles (Ω.snoc X) tel H))) sw
    exact step1.trans (step2.trans (congrArg (fun r => BoundCtx.Renaming.comp (BoundCtx.Renaming.succ Ω X) r) ih))

/-- Moving a telescope beneath the empty telescope is the identity. -/
theorem swapTeles_nil_proof : (H : List (Ty α)) → {k : Nat} → (Ω : BoundCtx (Ty α) k) →
    swapTeles Ω [] H = .id _
  | [], _, _ => rfl
  | X :: H, _, Ω =>
    congrArg₂ (fun x y => BoundCtx.Renaming.comp x y) (upTele_id_proof H (Ω.snoc X))
      (swapTeles_nil_proof H (Ω.snoc X))

/-- Weakening past a telescope over another telescope, and then exchanging
the two, is weakening past the first under the second. -/
theorem swapTeles_weaken_up_proof : (tel : List (Ty α)) → {k : Nat} → (Ω : BoundCtx (Ty α) k) →
    (H : List (Ty α)) →
    (weakenTele (extendCtx Ω tel) H).comp (swapTeles Ω tel H) = upTele (weakenTele Ω H) tel
  | [], _, Ω, H => congrArg (fun r => (weakenTele Ω H).comp r) (swapTeles_nil_proof H Ω)
  | X :: tel, _, Ω, H =>
    (congrArg (fun r => (weakenTele (extendCtx (Ω.snoc X) tel) H).comp r) (swapTeles_cons_proof H Ω X tel)).trans
      ((congrArg (fun r => BoundCtx.Renaming.comp r (upTele (swapTeles Ω [X] H) tel))
        (swapTeles_weaken_up_proof tel (Ω.snoc X) H)).trans
        ((upTele_comp_proof tel _ _).trans
          (congrArg (fun r => upTele r tel) (swapTeles_weaken_proof H Ω X))))

/-- Moving two slots beneath two slots is the exchange of two pairs. -/
theorem pairPastTele_pair_proof {k : Nat} (Ω : BoundCtx (Ty α) k) (C D A B : Ty α) :
    pairPastTele Ω [C, D] A B = afterPairPairRenaming Ω C D A B :=
  renaming_ext_proof (Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl
    (fun i => Fin.cases rfl (fun _ => rfl) i) i) i))

end Tele

/-! ## Stacks of packed tuples -/

section Stack

omit [TaggedSignature α Φ]

/-- Renaming the slots of a stack twice is renaming along the composite. -/
theorem holds_rename_comp_proof {m k j : Nat} {Δ : BoundCtx (Ty α) m} {Θ : BoundCtx (Ty α) k}
    {Ξ : BoundCtx (Ty α) j} (ρ : BoundCtx.Renaming Δ Θ) (π : BoundCtx.Renaming Θ Ξ) :
    {stack : List (List α)} → (H : Holds Δ stack) → (H.rename ρ).rename π = H.rename (ρ.comp π)
  | _, .nil => rfl
  | _, .cons top older => congrArg (Holds.cons ((top.rename ρ).rename π)) (holds_rename_comp_proof ρ π older)

/-- Weakening past the unpackings of a stack commutes with renaming. -/
theorem weakenStack_natural_proof : (stack : List (List α)) → {k j : Nat} → {Ω : BoundCtx (Ty α) k} →
    {Ω' : BoundCtx (Ty α) j} → (π : BoundCtx.Renaming Ω Ω') →
    (weakenStack stack Ω).comp (upStack stack π) = π.comp (weakenStack stack Ω')
  | [], _, _, _, _, _ => rfl
  | atoms :: stack, _, _, Ω, Ω', π =>
    (congrArg (fun r => (weakenStack stack Ω).comp r)
      (weakenTele_natural_proof (pairsTele atoms) (upStack stack π))).trans
      (congrArg (fun r => BoundCtx.Renaming.comp r (weakenTele (stackCtx stack Ω') (pairsTele atoms)))
        (weakenStack_natural_proof stack π))

/-- Moving a telescope beneath the unpackings of a stack commutes with
renaming. -/
theorem swapStack_natural_proof : (stack : List (List α)) → {k j : Nat} → {Ω : BoundCtx (Ty α) k} →
    {Ω' : BoundCtx (Ty α) j} → (tel : List (Ty α)) → (π : BoundCtx.Renaming Ω Ω') →
    (swapStack stack Ω tel).comp (upTele (upStack stack π) tel) =
      (upStack stack (upTele π tel)).comp (swapStack stack Ω' tel)
  | [], _, _, _, _, _, _ => rfl
  | atoms :: stack, _, _, Ω, Ω', tel, π =>
    (congrArg (fun r => (upTele (swapStack stack Ω tel) (pairsTele atoms)).comp r)
      (swapTeles_natural_proof (pairsTele atoms) tel (upStack stack π))).trans
      (congrArg (fun r => BoundCtx.Renaming.comp r (swapTeles (stackCtx stack Ω') tel (pairsTele atoms)))
        ((upTele_comp_proof (pairsTele atoms) (swapStack stack Ω tel) (upTele (upStack stack π) tel)).trans
          ((congrArg (fun r => upTele r (pairsTele atoms)) (swapStack_natural_proof stack tel π)).trans
            (upTele_comp_proof (pairsTele atoms) (upStack stack (upTele π tel))
              (swapStack stack Ω' tel)).symm)))

/-- Weakening past the unpackings of a stack over a telescope, and then
moving the telescope beneath them, is weakening past them under the
telescope. -/
theorem swapStack_weaken_proof : (stack : List (List α)) → {k : Nat} → (Ω : BoundCtx (Ty α) k) →
    (tel : List (Ty α)) →
    (weakenStack stack (extendCtx Ω tel)).comp (swapStack stack Ω tel) = upTele (weakenStack stack Ω) tel
  | [], _, Ω, tel => (upTele_id_proof tel Ω).symm
  | atoms :: stack, _, Ω, tel =>
    (congrArg (fun r => (weakenStack stack (extendCtx Ω tel)).comp
        (BoundCtx.Renaming.comp r (swapTeles (stackCtx stack Ω) tel (pairsTele atoms))))
      (weakenTele_natural_proof (pairsTele atoms) (swapStack stack Ω tel))).trans
      ((congrArg (fun r => ((weakenStack stack (extendCtx Ω tel)).comp (swapStack stack Ω tel)).comp r)
        (swapTeles_weaken_up_proof tel (stackCtx stack Ω) (pairsTele atoms))).trans
        ((congrArg (fun r => BoundCtx.Renaming.comp r (upTele (weakenTele (stackCtx stack Ω) (pairsTele atoms)) tel))
          (swapStack_weaken_proof stack Ω tel)).trans
          (upTele_comp_proof tel (weakenStack stack Ω) (weakenTele (stackCtx stack Ω) (pairsTele atoms)))))

/-- Weakening past a telescope and then past the unpackings of a stack,
and then moving the telescope beneath them, is weakening in the other
order. -/
theorem swapStack_weakenTele_proof (stack : List (List α)) {k : Nat} (Ω : BoundCtx (Ty α) k)
    (tel : List (Ty α)) :
    ((weakenTele Ω tel).comp (weakenStack stack (extendCtx Ω tel))).comp (swapStack stack Ω tel) =
      (weakenStack stack Ω).comp (weakenTele (stackCtx stack Ω) tel) :=
  (congrArg (fun r => (weakenTele Ω tel).comp r) (swapStack_weaken_proof stack Ω tel)).trans
    (weakenTele_natural_proof tel (weakenStack stack Ω))

/-- Moving a telescope with one more oldest slot beneath the unpackings of
a stack: move the rest, then that slot. -/
theorem swapStack_cons_proof : (stack : List (List α)) → {k : Nat} → (Ω : BoundCtx (Ty α) k) → (X : Ty α) →
    (tel : List (Ty α)) →
    swapStack stack Ω (X :: tel) =
      (swapStack stack (Ω.snoc X) tel).comp (upTele (swapStack stack Ω [X]) tel)
  | [], _, Ω, X, tel =>
    (congrArg (fun r => (BoundCtx.Renaming.id (extendCtx (Ω.snoc X) tel)).comp r)
      (upTele_id_proof tel (Ω.snoc X))).symm
  | atoms :: stack, _, Ω, X, tel =>
    (congrArg₂ (fun x y => BoundCtx.Renaming.comp x y)
      ((congrArg (fun r => upTele r (pairsTele atoms)) (swapStack_cons_proof stack Ω X tel)).trans
        (upTele_comp_proof (pairsTele atoms) (swapStack stack (Ω.snoc X) tel)
          (upTele (swapStack stack Ω [X]) tel)).symm)
      (swapTeles_cons_proof (pairsTele atoms) (stackCtx stack Ω) X tel)).trans
      ((congrArg (fun r => (upTele (swapStack stack (Ω.snoc X) tel) (pairsTele atoms)).comp
          (BoundCtx.Renaming.comp r (upTele (swapTeles (stackCtx stack Ω) [X] (pairsTele atoms)) tel)))
        (swapTeles_natural_proof (pairsTele atoms) tel (swapStack stack Ω [X])).symm).trans
        (congrArg (fun r => ((upTele (swapStack stack (Ω.snoc X) tel) (pairsTele atoms)).comp
            (swapTeles (stackCtx stack (Ω.snoc X)) tel (pairsTele atoms))).comp r)
          (upTele_comp_proof tel (upTele (swapStack stack Ω [X]) (pairsTele atoms))
            (swapTeles (stackCtx stack Ω) [X] (pairsTele atoms)))))

/-- The slot of a selected tuple along a renaming. -/
theorem holds_pick_rename_proof {m k : Nat} {Δ : BoundCtx (Ty α) m} {Θ : BoundCtx (Ty α) k}
    (ρ : BoundCtx.Renaming Δ Θ) : {stack : List (List α)} → {atoms : List α} → {rest : List (List α)} →
    (sel : Select stack atoms rest) → (H : Holds Δ stack) → (H.rename ρ).pick sel = (H.pick sel).rename ρ
  | _, _, _, .here, .cons _ _ => rfl
  | _, _, _, .there sel, .cons _ older => holds_pick_rename_proof ρ sel older

/-- The slots of the other tuples along a renaming. -/
theorem holds_drop_rename_proof {m k : Nat} {Δ : BoundCtx (Ty α) m} {Θ : BoundCtx (Ty α) k}
    (ρ : BoundCtx.Renaming Δ Θ) : {stack : List (List α)} → {atoms : List α} → {rest : List (List α)} →
    (sel : Select stack atoms rest) → (H : Holds Δ stack) → (H.rename ρ).drop sel = (H.drop sel).rename ρ
  | _, _, _, .here, .cons _ _ => rfl
  | _, _, _, .there sel, .cons top older =>
    congrArg (Holds.cons (top.rename ρ)) (holds_drop_rename_proof ρ sel older)

/-- Selecting a tuple commutes with renaming the slots of the stack. -/
theorem holds_select_rename_proof {m k : Nat} {Δ : BoundCtx (Ty α) m} {Θ : BoundCtx (Ty α) k}
    (ρ : BoundCtx.Renaming Δ Θ) {stack : List (List α)} {atoms : List α} {rest : List (List α)}
    (sel : Select stack atoms rest) (H : Holds Δ stack) :
    (H.rename ρ).select sel = (H.select sel).rename ρ :=
  congrArg₂ Holds.cons (holds_pick_rename_proof ρ sel H) (holds_drop_rename_proof ρ sel H)

/-- Weakening past the unpackings of a stack with a tuple selected, and
then moving the selected unpacking to its place, is weakening past the
unpackings of the stack. -/
theorem selectRen_weaken_proof : {stack : List (List α)} → {atoms : List α} → {rest : List (List α)} →
    (sel : Select stack atoms rest) → {k : Nat} → (Ω : BoundCtx (Ty α) k) →
    (weakenStack (atoms :: rest) Ω).comp (selectRen sel Ω) = weakenStack stack Ω
  | _, _, _, .here, _, _ => rfl
  | _, atoms, _, @Select.there _ x stack _ rest sel, _, Ω =>
    (congrArg (fun r => (weakenStack rest Ω).comp
        (BoundCtx.Renaming.comp r (upTele (selectRen sel Ω) (pairsTele x))))
      (swapTeles_weakenTele_proof (pairsTele atoms) (stackCtx rest Ω) (pairsTele x))).trans
      ((congrArg (fun r => ((weakenStack rest Ω).comp (weakenTele (stackCtx rest Ω) (pairsTele atoms))).comp r)
        (weakenTele_natural_proof (pairsTele x) (selectRen sel Ω))).trans
        (congrArg (fun r => BoundCtx.Renaming.comp r (weakenTele (stackCtx stack Ω) (pairsTele x)))
          (selectRen_weaken_proof sel Ω)))

/-- Moving a selected unpacking to its place commutes with renaming. -/
theorem selectRen_natural_proof : {stack : List (List α)} → {atoms : List α} → {rest : List (List α)} →
    (sel : Select stack atoms rest) → {k j : Nat} → {Ω : BoundCtx (Ty α) k} → {Ω' : BoundCtx (Ty α) j} →
    (π : BoundCtx.Renaming Ω Ω') →
    (selectRen sel Ω).comp (upStack stack π) = (upStack (atoms :: rest) π).comp (selectRen sel Ω')
  | _, _, _, .here, _, _, _, _, _ => rfl
  | _, atoms, _, @Select.there _ x stack _ rest sel, _, _, Ω, Ω', π =>
    (congrArg (fun r => (swapTeles (stackCtx rest Ω) (pairsTele x) (pairsTele atoms)).comp r)
      ((upTele_comp_proof (pairsTele x) (selectRen sel Ω) (upStack stack π)).trans
        ((congrArg (fun r => upTele r (pairsTele x)) (selectRen_natural_proof sel π)).trans
          (upTele_comp_proof (pairsTele x) (upStack (atoms :: rest) π) (selectRen sel Ω')).symm))).trans
      (congrArg (fun r => BoundCtx.Renaming.comp r (upTele (selectRen sel Ω') (pairsTele x)))
        (swapTeles_natural_proof (pairsTele atoms) (pairsTele x) (upStack rest π)))

end Stack

/-! ## Unpacking a tuple slot -/

omit [TaggedSignature α Φ] in
/-- Renaming commutes with unpacking. -/
theorem unpackAt_rename_proof : (atoms : List α) → {k j : Nat} → {Γ : BoundCtx (Ty α) k} →
    {Γ' : BoundCtx (Ty α) j} → (ρ : BoundCtx.Renaming Γ Γ') → (i : Fin k) →
    (u : LetCase.LocallyNameless.Tm Empty Φ (teleSize k (pairsTele atoms))) →
    (unpackAt atoms i u).rename ρ.toFun =
      unpackAt atoms (ρ.toFun i) (u.rename (upTele ρ (pairsTele atoms)).toFun)
  | [], _, _, _, _, _, _, _ => rfl
  | [_], _, _, _, _, _, _, _ => rfl
  | c :: d :: more, _, _, _, _, ρ, i, u =>
    congrArg (LetCase.LocallyNameless.Tm.let₂ (.bv (ρ.toFun i)))
      (unpackAt_rename_proof (d :: more) ((ρ.up (.base c)).up (tupleTy (d :: more))) 0 u)

/-- Renaming the pending tuple whose unpacking ends in a body is the
pending tuple whose unpacking ends in the renamed body. -/
theorem packed_renamed_proof : (atoms : List α) → {k j : Nat} → {Ω : BoundCtx (Ty α) k} →
    {Ω' : BoundCtx (Ty α) j} → {u : LetCase.LocallyNameless.Tm Empty Φ (teleSize k (unpackTele atoms))} →
    (r : CaseTree .body (extendCtx Ω (unpackTele atoms)) L u) → (ω : BoundCtx.Renaming Ω Ω') →
    CaseTree.renamed (pending := .tuple atoms) (β := Ω.snoc (tupleTy atoms)) (CaseTree.packed atoms r) ω =
      ⟨_, CaseTree.packed atoms (CaseTree.renamed (pending := .body) r (upTele ω (unpackTele atoms))).2⟩
  | [], _, _, _, _, _, _, _ => rfl
  | [_], _, _, _, _, _, _, _ => rfl
  | c :: d :: more, _, _, _, _, _, r, ω => by
    have ih := packed_renamed_proof (d :: more) r ((ω.up (tupleTy (c :: d :: more))).up (.base c))
    simp only [CaseTree.packed, CaseTree.renamed]
    rw [ih]
    rfl

/-! ## Renaming and binding under a pending tuple -/

/-- Binding a telescope under a renamed pending tuple is binding it under
the tuple along the composite renaming. -/
theorem pushed_pre_proof {pending : Pending α} {n : Nat} {β : BoundCtx (Ty α) n}
    {t : LetCase.LocallyNameless.Tm Empty Φ n} (tree : CaseTree pending β L t) :
    CaseTree.PushedPre pending β tree := by
  induction tree with
  | ret exit payload => trivial
  | ask f argument reply ih => trivial
  | only atoms payload ih => trivial
  | split atoms next rest left right ihl ihr => trivial
  | unit body ih =>
    intro j Ξ' ρ m Ω tel π wrap
    have h := renamed_comp_proof body (ρ.up _) ((π.up _).comp (swapTele Ω tel _))
    have e : (ρ.up (tupleTy ([] : List α))).comp ((π.up _).comp (swapTele Ω tel _)) =
        ((ρ.comp π).up _).comp (swapTele Ω tel _) := by
      rw [← renaming_up_comp_proof]
      rfl
    rw [e] at h
    simp only [CaseTree.renamed, CaseTree.pushed]
    rw [h]
  | atom a body ih =>
    intro j Ξ' ρ m Ω tel π wrap
    have h := renamed_comp_proof body (ρ.up _) ((π.up _).comp (swapTele Ω tel _))
    have e : (ρ.up (tupleTy [a])).comp ((π.up _).comp (swapTele Ω tel _)) =
        ((ρ.comp π).up _).comp (swapTele Ω tel _) := by
      rw [← renaming_up_comp_proof]
      rfl
    rw [e] at h
    simp only [CaseTree.renamed, CaseTree.pushed]
    rw [h]
  | @pair _ Ξ L a b rest body later ih =>
    intro j Ξ' ρ m Ω tel π wrap
    let T : Ty α := tupleTy (a :: b :: rest)
    have h := ih ((ρ.up T).up (Ty.base a)) (((π.up T).up (Ty.base a)).comp (pairPastTele Ω tel T (Ty.base a)))
      (fun ω => wrap ((pastPair Ω T (Ty.base a)).comp ω))
    have e : ((ρ.up T).up (Ty.base a)).comp
        (((π.up T).up (Ty.base a)).comp (pairPastTele Ω tel T (Ty.base a))) =
        (((ρ.comp π).up T).up (Ty.base a)).comp (pairPastTele Ω tel T (Ty.base a)) :=
      congrArg (fun r => r.comp (pairPastTele Ω tel T (Ty.base a)))
        ((renaming_up_comp_proof (ρ.up T) (π.up T) (Ty.base a)).trans
          (congrArg (fun r => r.up (Ty.base a)) (renaming_up_comp_proof ρ π T)))
    rw [e] at h
    simp only [CaseTree.renamed, CaseTree.pushed]
    rw [h]

/-- Renaming commutes with binding a telescope under a pending tuple, when
the way to bind the telescope commutes with renaming. -/
theorem pushed_post_proof {pending : Pending α} {n : Nat} {β : BoundCtx (Ty α) n}
    {t : LetCase.LocallyNameless.Tm Empty Φ n} (tree : CaseTree pending β L t) :
    CaseTree.PushedPost pending β tree := by
  induction tree with
  | ret exit payload => trivial
  | ask f argument reply ih => trivial
  | only atoms payload ih => trivial
  | split atoms next rest left right ihl ihr => trivial
  | unit body ih =>
    intro m Ω tel π wrap natural j Ω' ω
    let T : Ty α := tupleTy ([] : List α)
    have step := natural (BoundCtx.Renaming.succ Ω T) (body.renamed ((π.up T).comp (swapTele Ω tel T))).2
      (ω.up T)
    have h := renamed_comp_proof body ((π.up T).comp (swapTele Ω tel T)) (upTele (ω.up T) tel)
    have e : ((π.up T).comp (swapTele Ω tel T)).comp (upTele (ω.up T) tel) =
        ((π.comp (upTele ω tel)).up T).comp (swapTele Ω' tel T) := by
      show (π.up T).comp ((swapTele Ω tel T).comp (upTele (ω.up T) tel)) = _
      rw [swapTele_natural_proof, ← renaming_up_comp_proof]
      rfl
    have e' : (BoundCtx.Renaming.succ Ω T).comp (ω.up T) = ω.comp (BoundCtx.Renaming.succ Ω' T) :=
      renaming_ext_proof (fun _ => rfl)
    rw [e] at h
    rw [h, e'] at step
    simp only [CaseTree.renamed, CaseTree.pushed]
    rw [step]
  | atom a body ih =>
    intro m Ω tel π wrap natural j Ω' ω
    let T : Ty α := tupleTy [a]
    have step := natural (BoundCtx.Renaming.succ Ω T) (body.renamed ((π.up T).comp (swapTele Ω tel T))).2
      (ω.up T)
    have h := renamed_comp_proof body ((π.up T).comp (swapTele Ω tel T)) (upTele (ω.up T) tel)
    have e : ((π.up T).comp (swapTele Ω tel T)).comp (upTele (ω.up T) tel) =
        ((π.comp (upTele ω tel)).up T).comp (swapTele Ω' tel T) := by
      show (π.up T).comp ((swapTele Ω tel T).comp (upTele (ω.up T) tel)) = _
      rw [swapTele_natural_proof, ← renaming_up_comp_proof]
      rfl
    have e' : (BoundCtx.Renaming.succ Ω T).comp (ω.up T) = ω.comp (BoundCtx.Renaming.succ Ω' T) :=
      renaming_ext_proof (fun _ => rfl)
    rw [e] at h
    rw [h, e'] at step
    simp only [CaseTree.renamed, CaseTree.pushed]
    rw [step]
  | @pair _ Ξ L a b rest body later ih =>
    intro m Ω tel π wrap natural j Ω' ω
    let T : Ty α := tupleTy (a :: b :: rest)
    have h := ih (((π.up T).up (Ty.base a)).comp (pairPastTele Ω tel T (Ty.base a)))
      (fun ω' => wrap ((pastPair Ω T (Ty.base a)).comp ω'))
      (fun ω₁ _ r _ _ ω₂ => natural ((pastPair Ω T (Ty.base a)).comp ω₁) r ω₂)
      ((ω.up T).up (Ty.base a))
    have e : (((π.up T).up (Ty.base a)).comp (pairPastTele Ω tel T (Ty.base a))).comp
        (upTele ((ω.up T).up (Ty.base a)) tel) =
        (((π.comp (upTele ω tel)).up T).up (Ty.base a)).comp (pairPastTele Ω' tel T (Ty.base a)) := by
      show ((π.up T).up (Ty.base a)).comp ((pairPastTele Ω tel T (Ty.base a)).comp
        (upTele ((ω.up T).up (Ty.base a)) tel)) = _
      rw [pairPastTele_natural_proof, ← renaming_up_comp_proof, ← renaming_up_comp_proof]
      rfl
    rw [e] at h
    simp only [CaseTree.renamed, CaseTree.pushed]
    rw [h]
    rfl

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
