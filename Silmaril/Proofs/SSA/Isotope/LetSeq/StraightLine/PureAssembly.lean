module

public import Silmaril.SSA.Isotope.LetSeq.StraightLine.Defs

import Silmaril.SSA.Isotope.LetSeq.StraightLine.Binders.Thms

public section

namespace Silmaril.Isotope.LetSeq.StraightLine

open LocallyNameless (Derivation Equiv HasType Pure Tm TypedSubst)

open Binders

set_option backward.isDefEq.respectTransparency false

def extend {n m : Nat} {source : BoundCtx Types n} {target : BoundCtx Types m}
    {A : Types} (σ : AssemblyEnv source target) (v : Assembly target A) :
    AssemblyEnv (source.snoc A) target :=
  Fin.cases v σ

theorem terms_typed {n m : Nat} {source : BoundCtx Types n} {target : BoundCtx Types m}
    (σ : AssemblyEnv source target) : TypedSubst (Γ := Γ₀) source target σ.terms :=
  fun i => (σ i).derivation.toHasType

theorem assembly_pure {n : Nat} {β : BoundCtx Types n} {A : Types} (v : Assembly β A) :
    Pure false v.term := by
  induction v with
  | slot => exact .bv
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair iha ihb

theorem instantiate_assembly {n m : Nat}
    {source : BoundCtx Types n} {target : BoundCtx Types m} {A : Types}
    (σ : AssemblyEnv source target) (body : Term (n + 1)) (v : Assembly target A) :
    Tm.instantiate (body.bsubst (Tm.upSub σ.terms)) v.term = body.bsubst (extend σ v).terms := by
  rw [instantiate_bsubst_up]
  exact Tm.bsubst_congr (Fin.cases rfl (fun _ => rfl)) _

private theorem instantiate_pair_assembly {n m : Nat}
    {source : BoundCtx Types n} {target : BoundCtx Types m} {A B : Types}
    (σ : AssemblyEnv source target) (body : Term (n + 2)) (a : Assembly target A)
    (b : Assembly target B) :
    Tm.instantiate (Tm.instantiate (body.bsubst (Tm.upSub (Tm.upSub σ.terms))) b.term.lift)
        a.term = body.bsubst (extend (extend σ a) b).terms := by
  rw [instantiate_bsubst_up, Tm.instantiate, Tm.bsubst_comp]
  apply Tm.bsubst_congr
  intro i
  refine Fin.cases ?_ (Fin.cases rfl (fun j => ?_)) i
  · simp only [Fin.cases_zero, Tm.lift, Tm.bsubst_rename]
    exact Tm.bsubst_id _
  · simp only [Fin.cases_succ, Tm.upSub_succ, Tm.lift, Tm.bsubst_rename]
    exact Tm.bsubst_id _

/-- Destructuring an assembled pair substitutes both fields into any typed
body. The body may itself be effectful. -/
theorem replay_assembled_pair {n m : Nat} {source : BoundCtx Types n}
    {target : BoundCtx Types m} {A B C : Types} {body : Term (n + 2)}
    (σ : AssemblyEnv source target) (left : Assembly target A) (right : Assembly target B)
    (typed : HasType Request Γ₀ ((source.snoc A).snoc B) body C) :
    Equiv false Γ₀ target
      (.let₂ (.pair left.term right.term) (body.bsubst (Tm.upSub (Tm.upSub σ.terms))))
      (body.bsubst (extend (extend σ left) right).terms) C := by
  have bodyType := typed.bsubst (((terms_typed σ).up A).up B)
  have leftType := left.derivation.toHasType
  have rightType := right.derivation.toHasType
  have inner := Equiv.letBeta (assembly_pure right).lift rightType.lift bodyType
  have outer := Equiv.letBeta (assembly_pure left) leftType inner.hasType.2
  rw [instantiate_pair_assembly σ body left right] at outer
  exact (Equiv.pairBeta leftType rightType bodyType).trans
    ((Equiv.let₁ (.refl leftType) inner).trans outer)

/-- Normalize a native pure derivation with all its free bound-variable
occurrences supplied by assemblies. Replay substitutes a new assembly at
each pure binder, using the native equations on the actual substituted term. -/
theorem pure_normalize_proof {n m : Nat} {source : BoundCtx Types n} {target : BoundCtx Types m}
    {t : Term n} {A : Types} (d : Derivation Request Γ₀ source t A) (h : Pure false t)
    (σ : AssemblyEnv source target) :
    ∃ v : Assembly target A, Equiv false Γ₀ target (t.bsubst σ.terms) v.term A := by
  induction d with
  | @fv _ _ x _ _ => exact x.elim
  | bv => exact ⟨σ _, .refl (σ _).derivation.toHasType⟩
  | op arg _ =>
    have impossible : False := by
      cases h with
      | op pure _ => cases pure
    exact impossible.elim
  | unit => exact ⟨.unit, .unit⟩
  | pair a b iha ihb =>
    obtain ⟨ha, hb⟩ : Pure false _ ∧ Pure false _ := by cases h with | pair ha hb => exact ⟨ha, hb⟩
    obtain ⟨va, ea⟩ := iha ha σ
    obtain ⟨vb, eb⟩ := ihb hb σ
    exact ⟨.pair va vb, .pair ea eb⟩
  | @let₁ _ _ t body A B a b iha ihb =>
    obtain ⟨ha, hb⟩ : Pure false t ∧ Pure false body := by cases h with | let₁ ha hb => exact ⟨ha, hb⟩
    obtain ⟨v, ea⟩ := iha ha σ
    have bodyType := b.toHasType.bsubst ((terms_typed σ).up A)
    obtain ⟨out, replay⟩ := ihb hb (extend σ v)
    rw [← instantiate_assembly σ body v] at replay
    exact ⟨out, (Equiv.let₁ ea (.refl bodyType)).trans
      ((Equiv.letBeta (assembly_pure v) v.derivation.toHasType bodyType).trans replay)⟩
  | @let₂ _ _ t body A B C a b iha ihb =>
    obtain ⟨ha, hb⟩ : Pure false t ∧ Pure false body := by cases h with | let₂ ha hb => exact ⟨ha, hb⟩
    obtain ⟨packet, ea⟩ := iha ha σ
    cases packet with
    | pair left right =>
      have bodyType := b.toHasType.bsubst (((terms_typed σ).up A).up B)
      obtain ⟨out, replay⟩ := ihb hb (extend (extend σ left) right)
      exact ⟨out, (Equiv.let₂ ea (.refl bodyType)).trans
        ((replay_assembled_pair σ left right b.toHasType).trans replay)⟩

theorem assembly_normalize_proof {n : Nat} {β : BoundCtx Types n} {t : Term n} {A : Types}
    (p : PureAssembly β t A) : ∃ v : Assembly β A, Equiv false Γ₀ β t v.term A := by
  cases p with
  | assembled v => exact ⟨v, .refl v.derivation.toHasType⟩
  | substituted d h σ => exact pure_normalize_proof d h σ

private theorem cast_term {n : Nat} {β : BoundCtx Types n} {A B : Types}
    (h : A = B) (v : Assembly β A) :
    (cast (congrArg (Assembly β) h) v).term = v.term := by
  cases h
  rfl

def pureAssemblyOfAtomic {n : Nat} {β : BoundCtx Types n} {t : Term n} {A : Types}
    (d : Derivation Request Γ₀ β t A) (h : Pure false t)
    (slots : ∀ i, β.get i = Atom) : PureAssembly β t A := by
  let σ : AssemblyEnv β β := fun i => cast (congrArg (Assembly β) (slots i).symm) (.slot ⟨i, slots i⟩)
  have identity : t.bsubst σ.terms = t :=
    (Tm.bsubst_congr (fun i => cast_term (slots i).symm (.slot ⟨i, slots i⟩)) t).trans (Tm.bsubst_id t)
  exact identity ▸ PureAssembly.substituted d h σ

end Silmaril.Isotope.LetSeq.StraightLine
