module

public import Silmaril.SSA.Isotope.LetPar.Defs

/-! Typed congruence for the shared sequential and parallel equation schemes. -/

@[expose] public section

set_option autoImplicit true

namespace Silmaril.Isotope.Parallel

variable {tier : Tier} {ν : Type u} {Φ : Type v}

abbrev EqScheme (tier : Tier) (ν : Type u) (Φ : Type v) :=
  {n : Nat} → Tm tier ν Φ n → Tm tier ν Φ n → Prop

namespace Tm

/-- Bind the old left-hand result, accounting for the newly bound right-hand result. -/
def leftResult (f : Tm tier ν Φ (n + 1)) : Tm tier ν Φ (n + 2) :=
  f.rename (Fin.cases 1 (fun i => i.succ.succ))

/-- Swap a computed tuple while evaluating its operand once. -/
def swap (p : Tm tier ν Φ n) : Tm tier ν Φ n :=
  .let₂ p (.pair (.bv 0) (.bv 1))

/-- Reassociate a computed tuple from `((a,b),c)` to `(a,(b,c))`. -/
def assoc (p : Tm tier ν Φ n) : Tm tier ν Φ n :=
  .let₂ p (.let₂ (.bv 1) (.pair (.bv 1) (.pair (.bv 0) (.bv 2))))

/-- Drop the right unit component after evaluating the operand. -/
def dropRight (p : Tm tier ν Φ n) : Tm tier ν Φ n :=
  .let₂ p (.bv 1)

/-- Drop the left unit component after evaluating the operand. -/
def dropLeft (p : Tm tier ν Φ n) : Tm tier ν Φ n :=
  .let₂ p (.bv 0)

end Tm

variable {ε : Type w} [HasEff Φ ε]

/-- The native sequential schemes, allowed also on terms containing parallel subterms. -/
inductive SeqRule (pureEff : ε) : EqScheme tier ν Φ where
  | letBeta (hp : Pure pureEff a) : SeqRule pureEff (.let₁ a b) (b.instantiate a)
  | letEta (a : Tm tier ν Φ n) : SeqRule pureEff (.let₁ a (.bv 0)) a
  | unitEta (a : Tm tier ν Φ n) : SeqRule pureEff (.let₁ a .unit) a
  | pairBeta (a b : Tm tier ν Φ n) (c : Tm tier ν Φ (n + 2)) :
      SeqRule pureEff (.let₂ (.pair a b) c) (.let₁ a (.let₁ b.lift c))
  | pairEta (a : Tm tier ν Φ n) :
      SeqRule pureEff (.let₂ a (.pair (.bv 1) (.bv 0))) a
  | bindOp (a : Tm tier ν Φ n) (c : Tm tier ν Φ (n + 1)) :
      SeqRule pureEff (.let₁ (.op f a) c) (.let₁ a (.let₁ (.op f (.bv 0)) c.underBinder))
  | bindLet (a : Tm tier ν Φ n) (b c : Tm tier ν Φ (n + 1)) :
      SeqRule pureEff (.let₁ (.let₁ a b) c) (.let₁ a (.let₁ b c.underBinder))
  | bindLetPair (e : Tm tier ν Φ n) (c : Tm tier ν Φ (n + 2)) (d : Tm tier ν Φ (n + 1)) :
      SeqRule pureEff (.let₁ (.let₂ e c) d) (.let₂ e (.let₁ c d.underBinder.underBinder))
  | bindPair (a : Tm tier ν Φ n) (c : Tm tier ν Φ (n + 2)) :
      SeqRule pureEff (.let₂ a c) (.let₁ a (.let₂ (.bv 0) c.underTwoBinders))

/-- Parallel pairing respects tuple coherence and maps with pure continuations. -/
inductive ParRule (pureEff : ε) : EqScheme tier ν Φ where
  | swap (a b : Tm tier ν Φ n) :
      ParRule pureEff (Tm.swap (.par a b)) (.par b a)
  | assoc (a b c : Tm tier ν Φ n) :
      ParRule pureEff (Tm.assoc (.par (.par a b) c)) (.par a (.par b c))
  | purePair (ha : Pure pureEff a) (hb : Pure pureEff b) :
      ParRule pureEff (.par a b) (.pair a b)
  | unitLeft (a : Tm tier ν Φ n) : ParRule pureEff (Tm.dropLeft (.par .unit a)) a
  | unitRight (a : Tm tier ν Φ n) : ParRule pureEff (Tm.dropRight (.par a .unit)) a
  | map (hf : Pure pureEff f) (hg : Pure pureEff g) :
      ParRule pureEff (.par (.let₁ a f) (.let₁ b g))
        (.let₂ (.par a b) (.pair f.leftResult g.underBinder))

variable {τ : Type x} [HasProduct τ] [HasUnit τ] [CaseTypes tier τ]
  [DecidableEq ν] [HasTy Φ τ]

/-- The least typed congruence containing the sequential and parallel schemes and the
tier-specific `extra` schemes. A scheme instance requires exact typing at both endpoints. -/
inductive Equiv (pureEff : ε) (extra : EqScheme tier ν Φ) (Γ : Ctx ν τ) :
    {n : Nat} → BoundCtx τ n → Tm tier ν Φ n → Tm tier ν Φ n → τ → Prop where
  | refl (h : HasType Φ Γ β a A) : Equiv pureEff extra Γ β a a A
  | symm : Equiv pureEff extra Γ β a b A → Equiv pureEff extra Γ β b a A
  | trans : Equiv pureEff extra Γ β a b A → Equiv pureEff extra Γ β b c A →
      Equiv pureEff extra Γ β a c A
  | op : Equiv pureEff extra Γ β a a' (instrSrc f) →
      Equiv pureEff extra Γ β (.op f a) (.op f a') (instrTrg f)
  | let₁ : Equiv pureEff extra Γ β a a' A → Equiv pureEff extra Γ (.snoc β A) b b' B →
      Equiv pureEff extra Γ β (.let₁ a b) (.let₁ a' b') B
  | pair : Equiv pureEff extra Γ β a a' A → Equiv pureEff extra Γ β b b' B →
      Equiv pureEff extra Γ β (.pair a b) (.pair a' b') (product A B)
  | let₂ : Equiv pureEff extra Γ β a a' (product A B) →
      Equiv pureEff extra Γ (.snoc (.snoc β A) B) b b' C →
      Equiv pureEff extra Γ β (.let₂ a b) (.let₂ a' b') C
  | inl : Equiv pureEff extra Γ β a a' A →
      Equiv pureEff extra Γ β (.inl h a) (.inl h a') (CaseTypes.sum h A B)
  | inr : Equiv pureEff extra Γ β b b' B →
      Equiv pureEff extra Γ β (.inr h b) (.inr h b') (CaseTypes.sum h A B)
  | case : Equiv pureEff extra Γ β e e' (CaseTypes.sum h A B) →
      Equiv pureEff extra Γ (.snoc β A) l l' C → Equiv pureEff extra Γ (.snoc β B) r r' C →
      Equiv pureEff extra Γ β (.case h e l r) (.case h e' l' r') C
  | abort : Equiv pureEff extra Γ β a a' (CaseTypes.zero h) →
      Equiv pureEff extra Γ β (.abort h a) (.abort h a') C
  | iter : Equiv pureEff extra Γ β a a' A →
      Equiv pureEff extra Γ (.snoc β A) b b' (CaseTypes.sum (Tier.iterHasCase h) B A) →
      Equiv pureEff extra Γ β (.iter h a b) (.iter h a' b') B
  | par : Equiv pureEff extra Γ β a a' A → Equiv pureEff extra Γ β b b' B →
      Equiv pureEff extra Γ β (.par a b) (.par a' b') (product A B)
  | seqRule : SeqRule pureEff a b → HasType Φ Γ β a A → HasType Φ Γ β b A →
      Equiv pureEff extra Γ β a b A
  | parRule : ParRule pureEff a b → HasType Φ Γ β a A → HasType Φ Γ β b A →
      Equiv pureEff extra Γ β a b A
  | extraRule : extra a b → HasType Φ Γ β a A → HasType Φ Γ β b A →
      Equiv pureEff extra Γ β a b A

end Silmaril.Isotope.Parallel

namespace Silmaril.Isotope.LetPar

/-- The lower tier uses the common rules alone. -/
abbrev Equiv {ν : Type u} {Φ : Type v} {ε : Type w} [HasEff Φ ε] {τ : Type x}
    [HasProduct τ] [HasUnit τ] [DecidableEq ν] [HasTy Φ τ] (pureEff : ε) (Γ : Ctx ν τ)
    {n : Nat} (β : BoundCtx τ n) (a b : Tm ν Φ n) (A : τ) :=
  Parallel.Equiv pureEff (fun _ _ => False) Γ β a b A

end Silmaril.Isotope.LetPar
