module

public import Silmaril.Logic.Institution.Morphism
public import Mathlib.Data.Fin.VecNotation

/-! # Scoped hybrid/polyadic modal semantics

Arity-indexed actions denote actual (k+1)-ary world relations. State variables
use finite de Bruijn scopes, separate from signature nominals. Pointed carriers
are arbitrary and nonempty. Model arrows are injective bounded maps, preserving
nominal values; injectivity preserves state equality under `down`.
-/

@[expose] public section

namespace Silmaril.Logic.HybridPolyadic
open CategoryTheory Silmaril.Logic.Institution

structure Signature : Type 1 where
  Atom : Type
  Nominal : Type
  Action : ℕ → Type

structure Signature.Hom (S T : Signature) where
  atom : S.Atom → T.Atom
  nominal : S.Nominal → T.Nominal
  action : ∀ k, S.Action k → T.Action k

instance : Category Signature where
  Hom := Signature.Hom
  id _ := ⟨id, id, fun _ => id⟩
  comp f g := ⟨g.atom ∘ f.atom, g.nominal ∘ f.nominal, fun k => g.action k ∘ f.action k⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The finite index is the number of state variables currently in scope. -/
inductive Formula (S : Signature) : ℕ → Type
  | atom {n} : S.Atom → Formula S n
  | bot {n} : Formula S n
  | imp {n} : Formula S n → Formula S n → Formula S n
  | nominal {n} : S.Nominal → Formula S n
  | state {n} : Fin n → Formula S n
  | atNom {n} : S.Nominal → Formula S n → Formula S n
  | atState {n} : Fin n → Formula S n → Formula S n
  | dia {n k} : S.Action k → (Fin k → Formula S n) → Formula S n
  | down {n} : Formula S (n + 1) → Formula S n

def Formula.neg {S n} (p : Formula S n) : Formula S n := .imp p .bot
def Formula.conj {S n} (p q : Formula S n) : Formula S n := (Formula.imp p q.neg).neg
def Formula.top {S n} : Formula S n := .imp .bot .bot

/-- Signature maps preserve arities but may identify symbols, including nominals. -/
def Formula.map {S T : Signature} (f : S ⟶ T) : {n : ℕ} → Formula S n → Formula T n
  | _, .atom a => .atom (f.atom a)
  | _, .bot => .bot
  | _, .imp p q => .imp (p.map f) (q.map f)
  | _, .nominal a => .nominal (f.nominal a)
  | _, .state i => .state i
  | _, .atNom a p => .atNom (f.nominal a) (p.map f)
  | _, .atState i p => .atState i (p.map f)
  | _, .dia a ps => .dia (f.action _ a) (fun i => (ps i).map f)
  | _, .down p => .down (p.map f)

/-- Under a binder, the new variable stays zero and old variables shift together. -/
def liftRename {n m : ℕ} (ρ : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cons 0 (fun i => (ρ i).succ)

def Formula.rename {S : Signature} {n m : ℕ} (ρ : Fin n → Fin m) : Formula S n → Formula S m
  | .atom a => .atom a
  | .bot => .bot
  | .imp p q => .imp (p.rename ρ) (q.rename ρ)
  | .nominal a => .nominal a
  | .state i => .state (ρ i)
  | .atNom a p => .atNom a (p.rename ρ)
  | .atState i p => .atState (ρ i) (p.rename ρ)
  | .dia a ps => .dia a (fun i => (ps i).rename ρ)
  | .down p => .down (p.rename (liftRename ρ))

structure Model (S : Signature) : Type 1 where
  World : Type
  relation : ∀ k, S.Action k → World → (Fin k → World) → Prop
  valuation : S.Atom → World → Prop
  name : S.Nominal → World
  point : World

/-- Bounded tuple maps, with injectivity for the equality tests of hybrid binders.
No surjectivity onto unreachable worlds is required. -/
structure Model.Hom {S : Signature} (M N : Model S) where
  map : M.World → N.World
  injective : Function.Injective map
  point : map M.point = N.point
  atoms : ∀ a w, M.valuation a w ↔ N.valuation a (map w)
  names : ∀ a, map (M.name a) = N.name a
  forth : ∀ k a w vs, M.relation k a w vs → N.relation k a (map w) (map ∘ vs)
  back : ∀ k a w vs, N.relation k a (map w) vs →
    ∃ us, M.relation k a w us ∧ map ∘ us = vs

instance (S : Signature) : Category (Model S) where
  Hom := Model.Hom
  id M := ⟨id, Function.injective_id, rfl, fun _ _ => Iff.rfl, fun _ => rfl,
    fun _ _ _ _ h => h, fun _ _ _ vs h => ⟨vs, h, rfl⟩⟩
  comp f g :=
    { map := g.map ∘ f.map
      injective := g.injective.comp f.injective
      point := by change g.map (f.map _) = _; rw [f.point, g.point]
      atoms := fun a w => (f.atoms a w).trans (g.atoms a (f.map w))
      names := by intro a; change g.map (f.map _) = _; rw [f.names, g.names]
      forth := fun k a w vs h => g.forth k a _ _ (f.forth k a w vs h)
      back := by
        intro k a w vs h
        obtain ⟨us, hu, huv⟩ := g.back k a (f.map w) vs h
        obtain ⟨ts, ht, htu⟩ := f.back k a w us hu
        exact ⟨ts, ht, by change g.map ∘ (f.map ∘ ts) = vs; rw [htu, huv]⟩ }
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Signature reduct retains worlds, point and every actual relation tuple. -/
def reduct {S T : Signature} (f : S ⟶ T) : Model T ⥤ Model S where
  obj M := ⟨M.World, fun k a => M.relation k (f.action k a),
    fun a => M.valuation (f.atom a), fun a => M.name (f.nominal a), M.point⟩
  map h := ⟨h.map, h.injective, h.point, fun a w => h.atoms (f.atom a) w,
    fun a => h.names (f.nominal a), fun k a => h.forth k (f.action k a),
    fun k a => h.back k (f.action k a)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def Formula.Holds {S : Signature} (M : Model S) : {n : ℕ} →
    Formula S n → (Fin n → M.World) → M.World → Prop
  | _, .atom a, _, w => M.valuation a w
  | _, .bot, _, _ => False
  | _, .imp p q, env, w => p.Holds M env w → q.Holds M env w
  | _, .nominal a, _, w => w = M.name a
  | _, .state i, env, w => w = env i
  | _, .atNom a p, env, _ => p.Holds M env (M.name a)
  | _, .atState i p, env, _ => p.Holds M env (env i)
  | _, .dia a ps, env, w => ∃ vs, M.relation _ a w vs ∧ ∀ i, (ps i).Holds M env (vs i)
  | _, .down p, env, w => p.Holds M (Fin.cons w env) w

/-- Satisfaction is local at the distinguished point; sentences have no free state variables. -/
def Sat {S : Signature} (M : Model S) (p : Formula S 0) : Prop :=
  p.Holds M Fin.elim0 M.point

end Silmaril.Logic.HybridPolyadic
