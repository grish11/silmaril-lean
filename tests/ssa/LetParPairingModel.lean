module

import Silmaril.SSA.Isotope.LetParIter.Thms
import Silmaril.Semantics.ElgotMonads.Thms
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.FreeMonoid.Basic

open Silmaril.Elgot

namespace LetParPairingModel

section WriterPair

variable {W : Type} [Monoid W]
variable (merge : W → W → W)

local notation "M" => WriterT W Part

variable {A B : Type}

def pair (x : M A) (y : M B) : M (A × B) :=
  WriterT.mk <| x.run.bind fun a => y.run.map fun b => ((a.1, b.1), merge a.2 b.2)

omit [Monoid W] in
theorem mem_pair (x : M A) (y : M B) (c : (A × B) × W) :
    c ∈ (pair merge x y).run ↔
      ∃ a ∈ x.run, ∃ b ∈ y.run, ((a.1, b.1), merge a.2 b.2) = c := by
  simp only [pair, WriterT.run_mk, Part.mem_bind_iff, Part.mem_map_iff]

theorem mem_map {C : Type} (f : A → C) (x : M A) (c : C × W) :
    c ∈ (f <$> x).run ↔ ∃ a ∈ x.run, (f a.1, a.2) = c :=
  Part.mem_map_iff _

def writerPairing (merge_comm : ∀ x y, merge x y = merge y x)
    (merge_assoc : ∀ x y z, merge (merge x y) z = merge x (merge y z))
    (merge_one : ∀ x, merge x 1 = x) : ParallelPairing M where
  pair := pair merge
  natural f g x y := by
    apply WriterT.ext
    apply Part.ext
    intro c
    simp only [mem_pair, mem_map]
    constructor
    · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      exact ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
  swap x y := by
    apply WriterT.ext
    apply Part.ext
    intro c
    simp only [mem_pair, mem_map]
    constructor
    · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      exact ⟨b, hb, a, ha, by simp [Prod.swap, merge_comm]⟩
    · rintro ⟨b, hb, a, ha, rfl⟩
      exact ⟨_, ⟨a, ha, b, hb, rfl⟩, by simp [Prod.swap, merge_comm]⟩
  assoc x y z := by
    apply WriterT.ext
    apply Part.ext
    intro c
    simp only [mem_pair, mem_map]
    constructor
    · rintro ⟨_, ⟨_, ⟨a, ha, b, hb, rfl⟩, d, hd, rfl⟩, rfl⟩
      exact ⟨a, ha, _, ⟨b, hb, d, hd, rfl⟩, by rw [merge_assoc]⟩
    · rintro ⟨a, ha, _, ⟨b, hb, d, hd, rfl⟩, rfl⟩
      exact ⟨_, ⟨_, ⟨a, ha, b, hb, rfl⟩, d, hd, rfl⟩, by rw [merge_assoc]⟩
  rightUnit x := by
    apply WriterT.ext
    apply Part.ext
    intro c
    have h : (pure (PUnit.unit : PUnit) : M PUnit).run = Part.some (PUnit.unit, 1) := rfl
    simp only [mem_pair, mem_map, h, Part.mem_some_iff, exists_eq_left,
      merge_one]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ha
    · intro hc
      exact ⟨_, ⟨c, hc, rfl⟩, rfl⟩

end WriterPair

-- Sequential composition adds counts. Parallel pairing takes their maximum.
abbrev Log := Multiplicative Nat
abbrev M := WriterT Log Part

def merge (x y : Log) : Log := Multiplicative.ofAdd (max x.toAdd y.toAdd)

theorem merge_comm (x y : Log) : merge x y = merge y x := by
  exact congrArg Multiplicative.ofAdd (Nat.max_comm _ _)

theorem merge_assoc (x y z : Log) : merge (merge x y) z = merge x (merge y z) := by
  exact congrArg Multiplicative.ofAdd (Nat.max_assoc _ _ _)

theorem merge_one (x : Log) : merge x 1 = x := by
  exact congrArg Multiplicative.ofAdd (Nat.max_zero _)

def pairing : ParallelPairing M :=
  writerPairing merge merge_comm merge_assoc merge_one

example : LawfulElgotMonad M := inferInstance

def tick : M PUnit := MonadWriter.tell (Multiplicative.ofAdd 1)

theorem run_parallel : (pairing.pair tick tick).run =
    Part.some ((PUnit.unit, PUnit.unit), Multiplicative.ofAdd 1) := by
  simp [pairing, writerPairing, pair, tick, merge]

theorem run_sequential : (tick >>= fun a => tick >>= fun b => pure (a, b)).run =
    Part.some ((PUnit.unit, PUnit.unit), Multiplicative.ofAdd 2) := by
  simp only [tick, WriterT.run_bind, WriterT.run_tell, WriterT.run_pure, pure_bind, map_pure, mul_one]
  rfl

theorem parallel_ne_sequential :
    pairing.pair tick tick ≠ (tick >>= fun a => tick >>= fun b => pure (a, b)) := by
  intro h
  have hr := congrArg WriterT.run h
  rw [run_parallel, run_sequential] at hr
  have hlog := congrArg (fun p => (Prod.snd p : Log).toAdd) (Part.some_injective hr)
  contradiction

-- Both orders have the same result for two identical branches.
example : pairing.pair tick tick ≠ (tick >>= fun b => tick >>= fun a => pure (a, b)) := by
  refine fun h => parallel_ne_sequential (h.trans ?_)
  apply bind_congr
  intro a
  apply bind_congr
  intro b
  exact congrArg pure (Subsingleton.elim _ _)

theorem no_interchange :
    pairing.pair (tick >>= (pure : PUnit → M PUnit)) ((pure () : M PUnit) >>= fun _ => tick) ≠
      (pairing.pair tick (pure ()) >>= fun p => pairing.pair (pure p.1) tick) := by
  simpa only [bind_pure, pure_bind, ParallelPairing.pair_pure_right,
    ParallelPairing.pair_pure_left, ← bind_pure_comp, bind_assoc] using parallel_ne_sequential

end LetParPairingModel

namespace LetParIterWordSeparation

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics

abbrev Log := FreeMonoid Bool
abbrev M := WriterT Log Part

/-- Keep the single non-unit log when there is one. Two nonempty logs produce a
fixed nonempty marker. Sequential bind still concatenates the original words. -/
noncomputable def merge (x y : Log) : Log :=
  open Classical in
  if x = 1 then y else if y = 1 then x else FreeMonoid.of false

noncomputable def pairing : ParallelPairing M :=
  LetParPairingModel.writerPairing merge
    (by
      intro x y
      by_cases hx : x = 1 <;> by_cases hy : y = 1 <;> simp [merge, hx, hy])
    (by
      intro x y z
      by_cases hx : x = 1 <;> by_cases hy : y = 1 <;> by_cases hz : z = 1 <;>
        simp [merge, hx, hy, hz])
    (by intro x; by_cases hx : x = 1 <;> simp [merge, hx])

abbrev Obj := Ty Empty

def val : Obj → Type
  | .base e => e.elim
  | .unit => Unit
  | .empty => Empty
  | .product a b => val a × val b
  | .coprod a b => val a ⊕ val b

def coerce {a b : Obj} : Ty.Subty a b → val a → val b
  | .refl _ => id
  | .trans f g => coerce g ∘ coerce f
  | .product f g => Prod.map (coerce f) (coerce g)
  | .coprod f g => Sum.map (coerce f) (coerce g)
  | .empty _ => Empty.elim
  | .unit _ => fun _ => ()

local instance : TypeModel Obj where
  interp := val
  productEquiv _ _ := _root_.Equiv.refl _
  unitEquiv := _root_.Equiv.refl _
  coprodEquiv _ _ := _root_.Equiv.refl _
  emptyEquiv := _root_.Equiv.refl _
  coe := coerce

local instance : HasTy Bool Obj := ⟨fun _ => unit, fun _ => unit⟩
local instance : HasEff Bool (Bool × Bool) := ⟨fun _ => (true, false)⟩

local instance : InstructionModel Bool Obj (Bool × Bool) M where
  denote b _ := WriterT.mk (Part.some ((), FreeMonoid.of b))
  denotePure _ h := False.elim (Bool.noConfusion (congrArg Prod.fst h))
  denote_pure _ h _ := False.elim (Bool.noConfusion (congrArg Prod.fst h))

abbrev Γ : Ctx Empty Obj := .nil

/-- A canonical straight-line native program emits one instruction per letter. -/
def emit {n : Nat} : List Bool → LetIter.LocallyNameless.Tm Empty Bool n
  | [] => .unit
  | b :: bs => .let₁ (.op b .unit) (emit bs)

def typed {n : Nat} {β : BoundCtx Obj n} : (w : List Bool) →
    LetIter.LocallyNameless.Derivation Bool Γ β (emit w) unit
  | [] => .unit
  | _ :: bs => .let₁ (.op .unit) (typed bs)

set_option backward.isDefEq.respectTransparency false in
theorem run_emit {n : Nat} {β : BoundCtx Obj n} (w : List Bool) (ρ : BoundDen β) :
    (denote (m := M) (ε := Bool × Bool) (LetParIter.nativeTyping (typed w)) PUnit.unit ρ).run =
      Part.some ((), FreeMonoid.ofList w) := by
  induction w generalizing n with
  | nil => rfl
  | cons b bs ih =>
      simp only [typed, LetParIter.nativeTyping, denote, pure_bind]
      simp only [_root_.WriterT.run_bind]
      change (Part.some ((), FreeMonoid.of b)).bind
        (fun (a, l) =>
          (fun (u, k) => (u, l * k)) <$>
            (denote (m := M) (ε := Bool × Bool) (LetParIter.nativeTyping (typed (β := .snoc β unit) bs))
              PUnit.unit (ρ, a)).run) = _
      rw [Part.bind_some]
      exact congrArg (Functor.map (fun p : Unit × Log => (p.1, FreeMonoid.of b * p.2)))
        (ih (β := .snoc β unit) (ρ, ()))

/-- The extended equations separate any two distinct native instruction words.
The right-to-left implication uses the fixed native typing derivation. -/
theorem equiv_emit_iff (x y : List Bool) :
    LetParIter.Equiv (⊥ : Bool × Bool) Γ
      (LetParIter.derivation (β := .nil) (typed x))
      (LetParIter.derivation (β := .nil) (typed y)) ↔ x = y := by
  constructor
  · intro h
    have eq := LetParIter.native_denote_eq pairing h PUnit.unit PUnit.unit
    have runs := congrArg _root_.WriterT.run eq
    rw [run_emit (β := .nil) x PUnit.unit, run_emit (β := .nil) y PUnit.unit] at runs
    exact congrArg (fun p : Unit × Log => p.2.toList) (Part.some_injective runs)
  · rintro rfl
    exact .refl _

/-- On these canonical native programs, extended equivalence reflects to the
native proof-relevant equational judgment. -/
theorem reflects_emit (x y : List Bool)
    (h : LetParIter.Equiv (⊥ : Bool × Bool) Γ
      (LetParIter.derivation (β := .nil) (typed x))
      (LetParIter.derivation (β := .nil) (typed y))) :
    LetIter.ProofRelevant.LocallyNameless.TypedEquiv.Related (⊥ : Bool × Bool) Γ
      (LetParIter.nativeTyping (β := .nil) (typed x))
      (LetParIter.nativeTyping (β := .nil) (typed y)) := by
  obtain rfl := (equiv_emit_iff x y).mp h
  exact ⟨.refl _⟩

example : ¬ LetParIter.Equiv (⊥ : Bool × Bool) Γ
    (LetParIter.derivation (β := .nil) (typed [false, true]))
    (LetParIter.derivation (β := .nil) (typed [true, false])) :=
  fun h => Bool.noConfusion (List.cons.inj ((equiv_emit_iff _ _).mp h)).1

end LetParIterWordSeparation
