module

public import Silmaril.SSA.Isotope.LetCase.HandledTrace.Category.Defs

public section

namespace Silmaril.Isotope.LetCase.HandledTrace

open LocallyNameless Silmaril.Isotope.Semantics Silmaril.Elgot.ITree

universe u v e s

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {D : τ → Type (e + 1)} [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
  {Events : Type e → Type e} {State : Type s}
  {M : InstructionModel D Φ (Tree Events)} {policy : Handler State Events}

namespace Proofs

omit [TypeFormers τ] [HasTy Φ τ] [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D] in
private theorem extend_agreement {n m : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ m}
    (ren : BoundCtx.Renaming β δ) {src : BoundEnv D β} {tgt : BoundEnv D δ}
    (agree : ∀ i, HEq (tgt (ren.toFun i)) (src i)) {A : τ} (a : D A) :
    ∀ i, HEq ((tgt.snoc a) ((ren.up A).toFun i)) ((src.snoc a) i) :=
  Fin.cases HEq.rfl (fun i => agree i)

set_option backward.isDefEq.respectTransparency false in
theorem denote_rename {n m : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ m}
    {t : Tm Empty Φ n} {A : τ} (d : Derivation Φ Ctx.nil β t A)
    (ren : BoundCtx.Renaming β δ) (src : BoundEnv D β) (tgt : BoundEnv D δ)
    (agree : ∀ i, HEq (tgt (ren.toFun i)) (src i)) :
    (d.rename ren).denote D M (fun x => Empty.elim x) tgt = d.denote D M (fun x => Empty.elim x) src := by
  induction d generalizing m with
  | fv | unit => rfl
  | @bv n β i =>
    rw [Derivation.rename]
    have typed : δ.get (ren.toFun i) = β.get i := ren.typed i
    have interpret : ∀ {B} (h : δ.get (ren.toFun i) = B),
        (h ▸ (.bv : Derivation Φ Ctx.nil δ (.bv (ren.toFun i)) _) :
          Derivation Φ Ctx.nil δ (.bv (ren.toFun i)) B).denote D M (fun x => Empty.elim x) tgt =
        pure (cast (congrArg D h) (tgt (ren.toFun i))) := by
      intro B h
      cases h
      rfl
    exact (interpret typed).trans (congrArg pure (eq_of_heq ((cast_heq _ _).trans (agree i))))
  | op _ ih | inl _ ih | inr _ ih | abort _ ih =>
    simp only [Derivation.rename, Derivation.denote, ih ren src tgt agree]
  | pair _ _ left right =>
    simp only [Derivation.rename, Derivation.denote, left ren src tgt agree, right ren src tgt agree]
  | let₁ _ _ producer body =>
    simp only [Derivation.rename, Derivation.denote, producer ren src tgt agree]
    apply bind_congr
    intro value
    exact body _ _ _ (extend_agreement ren agree value)
  | let₂ _ _ producer body =>
    simp only [Derivation.rename, Derivation.denote, producer ren src tgt agree]
    apply bind_congr
    intro value
    exact body _ _ _ (extend_agreement _ (extend_agreement ren agree _) _)
  | case _ _ _ scrutinee left right =>
    simp only [Derivation.rename, Derivation.denote, scrutinee ren src tgt agree]
    apply bind_congr
    intro value
    cases CoproductModel.coprodEquiv (D := D) _ _ value with
    | inl a => exact left _ _ _ (extend_agreement ren agree a)
    | inr b => exact right _ _ _ (extend_agreement ren agree b)

variable {A B C F : τ}

/-- The selected body sees its native single input even under an older slot. -/
theorem run_underBinder (q : Program Φ B C) (a : D A) (b : D B) :
    q.2.underBinder.denote D M (fun x => Empty.elim x)
      ((BoundEnv.snoc (β := .nil) (fun i => i.elim0) a).snoc b) = q.run M b :=
  denote_rename q.2 (BoundCtx.Renaming.underBinder .nil A B) _ _
    (Fin.cases HEq.rfl (fun i => i.elim0))

set_option backward.isDefEq.respectTransparency false in
theorem run_seq (p : Program Φ A B) (q : Program Φ B C) (a : D A) :
    (p.seq q).run M a = (p.run M a >>= q.run M) := by
  change (p.run M a >>= fun b => q.2.underBinder.denote D M (fun x => Empty.elim x)
    ((BoundEnv.snoc (β := .nil) (fun i => i.elim0) a).snoc b)) = (p.run M a >>= q.run M)
  exact bind_congr (run_underBinder q a)

theorem seq_mono {p p' : Program Φ A B} {q q' : Program Φ B C}
    (hp : Program.Refines M policy p p') (hq : Program.Refines M policy q q') :
    Program.Refines M policy (p.seq q) (p'.seq q') := by
  intro a x
  rw [run_seq, run_seq]
  exact (hp a x).bind (fun {y b} _ => hq b y)

private theorem equiv_of_run_eq {p q : Program Φ A B}
    (eq : ∀ a, p.run M a = q.run M a) : (Program.setoid M policy A B).r p q :=
  ⟨fun a _ => eq a ▸ .refl _, fun a _ => (eq a).symm ▸ .refl _⟩

theorem id_seq (p : Program Φ A B) :
    (Program.setoid M policy A B).r ((Program.id A).seq p) p :=
  equiv_of_run_eq (fun a => (run_seq _ _ a).trans (pure_bind a _))

theorem seq_id (p : Program Φ A B) :
    (Program.setoid M policy A B).r (p.seq (Program.id B)) p :=
  equiv_of_run_eq (fun a => (run_seq _ _ a).trans (bind_pure (p.run M a)))

theorem seq_assoc (p : Program Φ A B) (q : Program Φ B C) (r : Program Φ C F) :
    (Program.setoid M policy A F).r ((p.seq q).seq r) (p.seq (q.seq r)) := by
  apply equiv_of_run_eq
  intro a
  simp only [run_seq, bind_assoc]
  exact bind_congr fun b => (run_seq q r b).symm

theorem le_refl {A B : Interface M policy} (p : Arrow A B) : Arrow.le p p := by
  induction p using Quotient.ind with
  | _ p => exact .refl M policy p

theorem le_trans {A B : Interface M policy} {p q r : Arrow A B}
    (hp : Arrow.le p q) (hq : Arrow.le q r) : Arrow.le p r := by
  induction p, q, r using Quotient.inductionOn₃
  exact Program.Refines.trans hp hq

theorem le_antisymm {A B : Interface M policy} {p q : Arrow A B}
    (hp : Arrow.le p q) (hq : Arrow.le q p) : p = q := by
  induction p, q using Quotient.inductionOn₂
  exact Quotient.sound ⟨hp, hq⟩

end Proofs
end Silmaril.Isotope.LetCase.HandledTrace
