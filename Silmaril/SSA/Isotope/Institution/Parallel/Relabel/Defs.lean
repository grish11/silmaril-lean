module

public import Silmaril.SSA.Isotope.Institution.LetCase.Thms
public import Silmaril.SSA.Isotope.LetParCase.Thms

/-! Opcode relabeling on the native scoped parallel syntax and its exact typing evidence. -/

@[expose] public section

namespace Silmaril.Isotope.Parallel

open Institution CategoryTheory

universe u v w

namespace Tm

variable {tier : Tier} {ν : Type v} {Φ Ψ : Type w}

/-- Change primitive names and retain the constructor tree, including both kinds of pairing. -/
def mapInstr (f : Φ → Ψ) : {n : Nat} → Tm tier ν Φ n → Tm tier ν Ψ n
  | _, .fv x => .fv x
  | _, .bv i => .bv i
  | _, .op p a => .op (f p) (mapInstr f a)
  | _, .let₁ a b => .let₁ (mapInstr f a) (mapInstr f b)
  | _, .unit => .unit
  | _, .pair a b => .pair (mapInstr f a) (mapInstr f b)
  | _, .let₂ a b => .let₂ (mapInstr f a) (mapInstr f b)
  | _, .inl h a => .inl h (mapInstr f a)
  | _, .inr h a => .inr h (mapInstr f a)
  | _, .case h e l r => .case h (mapInstr f e) (mapInstr f l) (mapInstr f r)
  | _, .abort h a => .abort h (mapInstr f a)
  | _, .iter h a b => .iter h (mapInstr f a) (mapInstr f b)
  | _, .par a b => .par (mapInstr f a) (mapInstr f b)

end Tm

variable {τ ε : Type u} {S S' : InstrSig τ ε} {tier : Tier} {ν : Type v}
  [HasProduct τ] [HasUnit τ] [CaseTypes tier τ] [DecidableEq ν] {Γ : Ctx ν τ}

/-- Transport the result type while retaining the same scoped term and contexts. -/
def Derivation.castResult {n : Nat} {β : BoundCtx τ n} {t : Tm tier ν S.Instr n}
    {A B : τ} (h : A = B) (d : Derivation S.Instr Γ β t A) : Derivation S.Instr Γ β t B :=
  h ▸ d

/-- Relabel exact typing evidence over fixed free and bound contexts and result type. -/
def Derivation.mapInstr (f : S ⟶ S') : {n : Nat} → {β : BoundCtx τ n} →
    {t : Tm tier ν S.Instr n} → {A : τ} →
    Derivation S.Instr Γ β t A → Derivation S'.Instr Γ β (t.mapInstr f.instr) A
  | _, _, _, _, .fv h => .fv h
  | _, _, _, _, .bv => .bv
  | _, _, .op p _, _, .op a =>
      Derivation.castResult (f.target p) (.op (Derivation.castResult (f.source p).symm (a.mapInstr f)))
  | _, _, _, _, .let₁ a b => .let₁ (a.mapInstr f) (b.mapInstr f)
  | _, _, _, _, .unit => .unit
  | _, _, _, _, .pair a b => .pair (a.mapInstr f) (b.mapInstr f)
  | _, _, _, _, .let₂ a b => .let₂ (a.mapInstr f) (b.mapInstr f)
  | _, _, _, _, .inl a => .inl (a.mapInstr f)
  | _, _, _, _, .inr a => .inr (a.mapInstr f)
  | _, _, _, _, .case e l r => .case (e.mapInstr f) (l.mapInstr f) (r.mapInstr f)
  | _, _, _, _, .abort a => .abort (a.mapInstr f)
  | _, _, _, _, .iter a b => .iter (a.mapInstr f) (b.mapInstr f)
  | _, _, _, _, .par a b => .par (a.mapInstr f) (b.mapInstr f)

end Silmaril.Isotope.Parallel
