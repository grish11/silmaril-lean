module

public import Silmaril.Raw.SSA.Isotope.Ctx.Bound
public import Silmaril.SSA.Isotope.Types.Defs

/-!
# Parallel extensions of the locally nameless let calculi

All tiers share one parallel constructor. Both branches see the same ambient
scope and return their results in an ordered binary product. Ordinary
`pair` evaluates its operands from left to right.
-/

@[expose] public section

namespace Silmaril.Isotope.Parallel

universe u v w

/-- Constructor availability in the let hierarchy. -/
inductive Tier where
  | seq | case | iter
  deriving DecidableEq

abbrev Tier.HasCase (tier : Tier) : Prop := tier ≠ .seq
abbrev Tier.HasIter (tier : Tier) : Prop := tier = .iter

/-- A tier inclusion preserves availability of both optional constructor families. -/
structure Tier.Inclusion (source target : Tier) : Prop where
  hasCase : source.HasCase → target.HasCase
  hasIter : source.HasIter → target.HasIter

theorem Tier.seqCase : Tier.Inclusion .seq .case :=
  ⟨(fun h => False.elim (h rfl)), (fun h => nomatch h)⟩

theorem Tier.caseIter : Tier.Inclusion .case .iter :=
  ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩

/-- Sums and the empty type are required only when the tier supports case analysis. -/
class CaseTypes (tier : Tier) (τ : Type u) where
  formers : tier.HasCase → CoproductTypeFormers τ

instance {τ : Type u} : CaseTypes .seq τ where
  formers h := False.elim (h rfl)

instance {τ : Type u} [CoproductTypeFormers τ] : CaseTypes .case τ where
  formers _ := inferInstance

instance {τ : Type u} [CoproductTypeFormers τ] : CaseTypes .iter τ where
  formers _ := inferInstance

def CaseTypes.sum {tier : Tier} {τ : Type u} [c : CaseTypes tier τ]
    (h : tier.HasCase) (A B : τ) : τ :=
  @Silmaril.coprod τ (c.formers h).toHasCoproduct A B

def CaseTypes.zero {tier : Tier} {τ : Type u} [c : CaseTypes tier τ]
    (h : tier.HasCase) : τ :=
  @Silmaril.empty τ (c.formers h).toHasEmpty

theorem Tier.iterHasCase {tier : Tier} (h : tier.HasIter) : tier.HasCase := by
  subst tier
  intro h
  cases h

/-- Terms with named free variables and a finite locally nameless bound scope. -/
inductive Tm (tier : Tier) (ν : Type v) (Φ : Type w) : Nat → Type (max v w) where
  | fv {n : Nat} (x : ν) : Tm tier ν Φ n
  | bv {n : Nat} (i : Fin n) : Tm tier ν Φ n
  | op {n : Nat} (f : Φ) (a : Tm tier ν Φ n) : Tm tier ν Φ n
  | let₁ {n : Nat} (a : Tm tier ν Φ n) (b : Tm tier ν Φ (n + 1)) : Tm tier ν Φ n
  | unit {n : Nat} : Tm tier ν Φ n
  | pair {n : Nat} (a b : Tm tier ν Φ n) : Tm tier ν Φ n
  | let₂ {n : Nat} (a : Tm tier ν Φ n) (b : Tm tier ν Φ (n + 2)) : Tm tier ν Φ n
  | inl {n : Nat} (h : tier.HasCase) (a : Tm tier ν Φ n) : Tm tier ν Φ n
  | inr {n : Nat} (h : tier.HasCase) (a : Tm tier ν Φ n) : Tm tier ν Φ n
  | case {n : Nat} (h : tier.HasCase) (e : Tm tier ν Φ n) (l r : Tm tier ν Φ (n + 1)) :
      Tm tier ν Φ n
  | abort {n : Nat} (h : tier.HasCase) (a : Tm tier ν Φ n) : Tm tier ν Φ n
  | iter {n : Nat} (h : tier.HasIter) (a : Tm tier ν Φ n) (b : Tm tier ν Φ (n + 1)) :
      Tm tier ν Φ n
  | par {n : Nat} (a b : Tm tier ν Φ n) : Tm tier ν Φ n

namespace Tm

variable {tier target : Tier} {ν : Type v} {Φ : Type w} {n m : Nat}

def up (ρ : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cases 0 (fun i => (ρ i).succ)

/-- Rename bound variables, using the same renaming in both parallel branches. -/
def rename {n m : Nat} (ρ : Fin n → Fin m) : Tm tier ν Φ n → Tm tier ν Φ m
  | .fv x => .fv x
  | .bv i => .bv (ρ i)
  | .op f a => .op f (rename ρ a)
  | .let₁ a b => .let₁ (rename ρ a) (rename (up ρ) b)
  | .unit => .unit
  | .pair a b => .pair (rename ρ a) (rename ρ b)
  | .let₂ a b => .let₂ (rename ρ a) (rename (up (up ρ)) b)
  | .inl h a => .inl h (rename ρ a)
  | .inr h a => .inr h (rename ρ a)
  | .case h e l r => .case h (rename ρ e) (rename (up ρ) l) (rename (up ρ) r)
  | .abort h a => .abort h (rename ρ a)
  | .iter h a b => .iter h (rename ρ a) (rename (up ρ) b)
  | .par a b => .par (rename ρ a) (rename ρ b)

def lift (t : Tm tier ν Φ n) : Tm tier ν Φ (n + 1) := rename Fin.succ t

/-- Insert a binder below the newest one. -/
def underBinder (t : Tm tier ν Φ (n + 1)) : Tm tier ν Φ (n + 2) :=
  rename (Fin.cases 0 (fun i => i.succ.succ)) t

/-- Insert a binder below the newest two. -/
def underTwoBinders (t : Tm tier ν Φ (n + 2)) : Tm tier ν Φ (n + 3) :=
  rename (Fin.cases 0 (Fin.cases 1 (fun i => i.succ.succ.succ))) t

def upSub (σ : Fin n → Tm tier ν Φ m) : Fin (n + 1) → Tm tier ν Φ (m + 1) :=
  Fin.cases (.bv 0) (fun i => (σ i).lift)

/-- Simultaneous capture-avoiding substitution for bound variables. -/
def bsubst {n m : Nat} (σ : Fin n → Tm tier ν Φ m) : Tm tier ν Φ n → Tm tier ν Φ m
  | .fv x => .fv x
  | .bv i => σ i
  | .op f a => .op f (bsubst σ a)
  | .let₁ a b => .let₁ (bsubst σ a) (bsubst (upSub σ) b)
  | .unit => .unit
  | .pair a b => .pair (bsubst σ a) (bsubst σ b)
  | .let₂ a b => .let₂ (bsubst σ a) (bsubst (upSub (upSub σ)) b)
  | .inl h a => .inl h (bsubst σ a)
  | .inr h a => .inr h (bsubst σ a)
  | .case h e l r => .case h (bsubst σ e) (bsubst (upSub σ) l) (bsubst (upSub σ) r)
  | .abort h a => .abort h (bsubst σ a)
  | .iter h a b => .iter h (bsubst σ a) (bsubst (upSub σ) b)
  | .par a b => .par (bsubst σ a) (bsubst σ b)

def instantiate (b : Tm tier ν Φ (n + 1)) (a : Tm tier ν Φ n) : Tm tier ν Φ n :=
  bsubst (Fin.cases a .bv) b

/-- Include a tier by preserving every visible term constructor. -/
def widen (h : Tier.Inclusion tier target) {n : Nat} : Tm tier ν Φ n → Tm target ν Φ n
  | .fv x => .fv x
  | .bv i => .bv i
  | .op f a => .op f (widen h a)
  | .let₁ a b => .let₁ (widen h a) (widen h b)
  | .unit => .unit
  | .pair a b => .pair (widen h a) (widen h b)
  | .let₂ a b => .let₂ (widen h a) (widen h b)
  | .inl p a => .inl (h.hasCase p) (widen h a)
  | .inr p a => .inr (h.hasCase p) (widen h a)
  | .case p e l r => .case (h.hasCase p) (widen h e) (widen h l) (widen h r)
  | .abort p a => .abort (h.hasCase p) (widen h a)
  | .iter p a b => .iter (h.hasIter p) (widen h a) (widen h b)
  | .par a b => .par (widen h a) (widen h b)

end Tm

set_option autoImplicit true in
/-- Exact, computational typing evidence. The two parallel premises use the very same context. -/
inductive Derivation {tier : Tier} {τ : Type u} [HasProduct τ] [HasUnit τ] [CaseTypes tier τ]
    {ν : Type v} [DecidableEq ν] (Φ : Type w) [HasTy Φ τ] (Γ : Ctx ν τ) :
    {n : Nat} → BoundCtx τ n → Tm tier ν Φ n → τ → Type (max u v w) where
  | fv (h : Γ.lookup x = some A) : Derivation Φ Γ β (.fv x) A
  | bv : Derivation Φ Γ β (.bv i) (β.get i)
  | op (ha : Derivation Φ Γ β a (instrSrc f)) : Derivation Φ Γ β (.op f a) (instrTrg f)
  | let₁ (ha : Derivation Φ Γ β a A) (hb : Derivation Φ Γ (.snoc β A) b B) :
      Derivation Φ Γ β (.let₁ a b) B
  | unit : Derivation Φ Γ β .unit Silmaril.unit
  | pair (ha : Derivation Φ Γ β a A) (hb : Derivation Φ Γ β b B) :
      Derivation Φ Γ β (.pair a b) (product A B)
  | let₂ (ha : Derivation Φ Γ β a (product A B))
      (hb : Derivation Φ Γ (.snoc (.snoc β A) B) b C) : Derivation Φ Γ β (.let₂ a b) C
  | inl (ha : Derivation Φ Γ β a A) :
      Derivation Φ Γ β (.inl h a) (CaseTypes.sum h A B)
  | inr (hb : Derivation Φ Γ β b B) :
      Derivation Φ Γ β (.inr h b) (CaseTypes.sum h A B)
  | case (he : Derivation Φ Γ β e (CaseTypes.sum h A B))
      (hl : Derivation Φ Γ (.snoc β A) l C) (hr : Derivation Φ Γ (.snoc β B) r C) :
      Derivation Φ Γ β (.case h e l r) C
  | abort (ha : Derivation Φ Γ β a (CaseTypes.zero h)) : Derivation Φ Γ β (.abort h a) C
  | iter (ha : Derivation Φ Γ β a A)
      (hb : Derivation Φ Γ (.snoc β A) b (CaseTypes.sum (Tier.iterHasCase h) B A)) :
      Derivation Φ Γ β (.iter h a b) B
  | par (ha : Derivation Φ Γ β a A) (hb : Derivation Φ Γ β b B) :
      Derivation Φ Γ β (.par a b) (product A B)

/-- Propositional exact typing over the given free and bound contexts. -/
abbrev HasType {tier : Tier} {τ : Type u} [HasProduct τ] [HasUnit τ] [CaseTypes tier τ]
    {ν : Type v} [DecidableEq ν] (Φ : Type w) [HasTy Φ τ] (Γ : Ctx ν τ)
    {n : Nat} (β : BoundCtx τ n) (t : Tm tier ν Φ n) (A : τ) : Prop :=
  Nonempty (Derivation Φ Γ β t A)

set_option autoImplicit true in
/-- Both parallel branches must be pure for their pairing to be pure. -/
inductive Pure {tier : Tier} {ν : Type v} {Φ : Type w} {ε : Type u} [HasEff Φ ε]
    (pureEff : ε) : {n : Nat} → Tm tier ν Φ n → Prop where
  | fv : Pure pureEff (.fv x)
  | bv : Pure pureEff (.bv i)
  | op (hf : IsPure pureEff f) : Pure pureEff a → Pure pureEff (.op f a)
  | let₁ : Pure pureEff a → Pure pureEff b → Pure pureEff (.let₁ a b)
  | unit : Pure pureEff .unit
  | pair : Pure pureEff a → Pure pureEff b → Pure pureEff (.pair a b)
  | let₂ : Pure pureEff a → Pure pureEff b → Pure pureEff (.let₂ a b)
  | inl : Pure pureEff a → Pure pureEff (.inl h a)
  | inr : Pure pureEff a → Pure pureEff (.inr h a)
  | case : Pure pureEff e → Pure pureEff l → Pure pureEff r → Pure pureEff (.case h e l r)
  | abort : Pure pureEff a → Pure pureEff (.abort h a)
  | par : Pure pureEff a → Pure pureEff b → Pure pureEff (.par a b)

end Silmaril.Isotope.Parallel

namespace Silmaril.Isotope.LetPar

/-- LetSeq with independent parallel pairing. -/
abbrev Tm := Parallel.Tm .seq

end Silmaril.Isotope.LetPar

namespace Silmaril.Isotope.LetParCase

/-- LetCase with independent parallel pairing. -/
abbrev Tm := Parallel.Tm .case

end Silmaril.Isotope.LetParCase
