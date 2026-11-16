module

public import Silmaril.Logic.Modal.Thms
public import Mathlib.Order.FixedPoints
public import Mathlib.CategoryTheory.Discrete.Basic

@[expose] public section

/-! Positive, scoped modal μ-calculus. Models have arbitrary pointed frames.
The institution deliberately uses a discrete model category: no invariance
under bounded morphisms is asserted by this interface. -/
namespace Silmaril.Logic.ModalMu
open CategoryTheory Silmaril.Logic.Institution

structure Signature : Type 1 where
  Atom : Type
  Action : Type

structure Renaming (S T : Signature) where
  atom : S.Atom → T.Atom
  action : S.Action → T.Action

instance : Category Signature where
  Hom := Renaming
  id _ := ⟨id, id⟩
  comp f g := ⟨g.atom ∘ f.atom, g.action ∘ f.action⟩

/-- Only atoms have negative literals; set variables occur positively by construction. -/
inductive Formula (S : Signature) : Nat → Type where
  | pos {n : Nat} : S.Atom → Formula S n
  | neg {n : Nat} : S.Atom → Formula S n
  | bot {n : Nat} : Formula S n
  | top {n : Nat} : Formula S n
  | var {n : Nat} : Fin n → Formula S n
  | conj {n : Nat} : Formula S n → Formula S n → Formula S n
  | disj {n : Nat} : Formula S n → Formula S n → Formula S n
  | box {n : Nat} : S.Action → Formula S n → Formula S n
  | diamond {n : Nat} : S.Action → Formula S n → Formula S n
  | mu {n : Nat} : Formula S (n + 1) → Formula S n
  | nu {n : Nat} : Formula S (n + 1) → Formula S n

variable {n : Nat} {S : Signature}

def Formula.map {S T : Signature} (f : S ⟶ T) : {n : Nat} → Formula S n → Formula T n
  | _, .pos a => .pos (f.atom a)
  | _, .neg a => .neg (f.atom a)
  | _, .bot => .bot
  | _, .top => .top
  | _, .var i => .var i
  | _, .conj p q => .conj (p.map f) (q.map f)
  | _, .disj p q => .disj (p.map f) (q.map f)
  | _, .box a p => .box (f.action a) (p.map f)
  | _, .diamond a p => .diamond (f.action a) (p.map f)
  | _, .mu p => .mu (p.map f)
  | _, .nu p => .nu (p.map f)

/-- Negation normal form dual; the environment is complemented at free variables. -/
def Formula.dual : {n : Nat} → Formula S n → Formula S n
  | _, .pos a => .neg a
  | _, .neg a => .pos a
  | _, .bot => .top
  | _, .top => .bot
  | _, .var i => .var i
  | _, .conj p q => .disj p.dual q.dual
  | _, .disj p q => .conj p.dual q.dual
  | _, .box a p => .diamond a p.dual
  | _, .diamond a p => .box a p.dual
  | _, .mu p => .nu p.dual
  | _, .nu p => .mu p.dual

structure Model (S : Signature) : Type 1 where
  World : Type
  step : S.Action → World → World → Prop
  valuation : S.Atom → Set World
  point : World

/-- Equality-only arrows, with small hom types to match the existing K institution. -/
instance (S : Signature) : Category (Model S) where
  Hom M N := PLift (M = N)
  id _ := ⟨rfl⟩
  comp f g := ⟨f.down.trans g.down⟩

abbrev Env (W : Type) (n : Nat) := Fin n → Set W

def extend {W : Type} (ρ : Env W n) (X : Set W) : Env W (n + 1) := Fin.cases X ρ

def insert {W : Type} (ρ : Env W n) : Set W →o Env W (n + 1) where
  toFun := extend ρ
  monotone' := by
    intro X Y h i
    refine Fin.cases h (fun _ => le_rfl) i

/-- Every formula is a monotone map of its free set-variable environment. -/
noncomputable def Formula.denote {S : Signature} (M : Model S) {n : Nat}
    (p : Formula S n) : Env M.World n →o Set M.World := by
  induction p with
  | pos a => exact ⟨fun _ => M.valuation a, fun _ _ _ => le_rfl⟩
  | neg a => exact ⟨fun _ => (M.valuation a)ᶜ, fun _ _ _ => le_rfl⟩
  | bot => exact ⟨fun _ => ∅, fun _ _ _ => le_rfl⟩
  | top => exact ⟨fun _ => Set.univ, fun _ _ _ => le_rfl⟩
  | var i => exact ⟨fun ρ => ρ i, fun _ _ h => h i⟩
  | conj p q dp dq =>
      exact ⟨fun ρ => dp ρ ∩ dq ρ,
        fun _ _ h => fun _ hw => ⟨dp.monotone h hw.1, dq.monotone h hw.2⟩⟩
  | disj p q dp dq =>
      exact ⟨fun ρ => dp ρ ∪ dq ρ,
        fun _ _ h => fun _ hw => hw.elim
          (fun hp => Or.inl (dp.monotone h hp))
          (fun hq => Or.inr (dq.monotone h hq))⟩
  | box a p dp =>
      exact ⟨fun ρ => {w | ∀ v, M.step a w v → v ∈ dp ρ},
        fun _ _ h => fun _ hw v hv => dp.monotone h (hw v hv)⟩
  | diamond a p dp =>
      exact ⟨fun ρ => {w | ∃ v, M.step a w v ∧ v ∈ dp ρ},
        fun _ _ h => fun _ ⟨v, hv, hp⟩ => ⟨v, hv, dp.monotone h hp⟩⟩
  | mu p dp =>
      exact ⟨fun ρ => (dp.comp (insert ρ)).lfp, by
        intro ρ σ h
        apply OrderHom.lfp.monotone
        intro X
        apply dp.monotone
        intro i
        exact Fin.cases le_rfl (fun j => h j) i⟩
  | nu p dp =>
      exact ⟨fun ρ => (dp.comp (insert ρ)).gfp, by
        intro ρ σ h
        apply OrderHom.gfp.monotone
        intro X
        apply dp.monotone
        intro i
        exact Fin.cases le_rfl (fun j => h j) i⟩

abbrev emptyEnv {W : Type} : Env W 0 := Fin.elim0

def Sat {S : Signature} (M : Model S) (p : Formula S 0) : Prop :=
  M.point ∈ p.denote M emptyEnv

/-- Both action relations and atom valuations are pulled back; worlds stay fixed. -/
def reduct {S T : Signature} (f : S ⟶ T) (M : Model T) : Model S :=
  ⟨M.World, fun a => M.step (f.action a), fun a => M.valuation (f.atom a), M.point⟩

end Silmaril.Logic.ModalMu
