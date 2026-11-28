module

public import Silmaril.Semantics.ElgotMonads.Parallel.Defs
public import Silmaril.Semantics.Elgot.Parallel.Thms
import Silmaril.Proofs.Semantics.ElgotMonads.Parallel

/-! # Coherent tuple pairing and maps of reader models -/

@[expose] public section

namespace Silmaril.Elgot

open scoped Silmaril.Elgot.Nondet

universe u

namespace Part

theorem bindPair_comm {A B : Type u} (x : _root_.Part A) (y : _root_.Part B) :
    ParallelPairing.bindPair x y = (y >>= fun b => x >>= fun a => pure (a, b)) :=
  _root_.Part.ext fun p => (Proofs.Semantics.ElgotMonads.Parallel.part_mem_left x y p).trans
    (Proofs.Semantics.ElgotMonads.Parallel.part_mem_right x y p).symm

/-- The partial tuple exists exactly when both branches return. -/
def parallelPairing : ParallelPairing _root_.Part.{u} := .ofBind bindPair_comm

@[simp] theorem mem_pair {A B : Type u} (x : _root_.Part A) (y : _root_.Part B) (p : A × B) :
    p ∈ parallelPairing.pair x y ↔ p.1 ∈ x ∧ p.2 ∈ y :=
  Proofs.Semantics.ElgotMonads.Parallel.part_mem_left x y p

end Part

namespace Nondet

theorem bindPair_comm {A B : Type u} (x : SetM A) (y : SetM B) :
    ParallelPairing.bindPair x y = (y >>= fun b => x >>= fun a => pure (a, b)) :=
  Set.ext fun p => (Proofs.Semantics.ElgotMonads.Parallel.set_mem_left x y p).trans
    (Proofs.Semantics.ElgotMonads.Parallel.set_mem_right x y p).symm

/-- Independent nondeterministic choice forms the cartesian product of the outcomes. -/
def parallelPairing : ParallelPairing SetM.{u} := .ofBind bindPair_comm

@[simp] theorem mem_pair {A B : Type u} (x : SetM A) (y : SetM B) (p : A × B) :
    p ∈ₘ parallelPairing.pair x y ↔ p.1 ∈ₘ x ∧ p.2 ∈ₘ y :=
  Proofs.Semantics.ElgotMonads.Parallel.set_mem_left x y p

end Nondet

namespace ReaderT

open _root_.ReaderT (adapt)

variable {m : Type u → Type u} [Monad m] {ρ σ A B : Type u}

/-! Evaluation at any fixed environment preserves pure and bind by the core
`ReaderT.run_pure` and `ReaderT.run_bind` laws, iteration by `run_iter`, and
parallel pairing by `run_pair` below. -/

@[simp] theorem run_pair (P : ParallelPairing m) (x : _root_.ReaderT ρ m A)
    (y : _root_.ReaderT ρ m B) (r : ρ) :
    (P.reader.pair x y).run r = P.pair (x.run r) (y.run r) := rfl

@[simp] theorem adapt_pure (f : σ → ρ) (a : A) :
    adapt f (pure a : _root_.ReaderT ρ m A) = pure a := rfl

@[simp] theorem adapt_bind (f : σ → ρ) (x : _root_.ReaderT ρ m A)
    (k : A → _root_.ReaderT ρ m B) :
    adapt f (x >>= k) = adapt f x >>= fun a => adapt f (k a) := rfl

omit [Monad m] in
@[simp] theorem adapt_iter [Iterate m] (f : σ → ρ) (step : A → _root_.ReaderT ρ m (B ⊕ A))
    (a : A) : adapt f (iter step a) = iter (fun a => adapt f (step a)) a := rfl

@[simp] theorem adapt_pair (f : σ → ρ) (P : ParallelPairing m)
    (x : _root_.ReaderT ρ m A) (y : _root_.ReaderT ρ m B) :
    adapt f (P.reader.pair x y) = P.reader.pair (adapt f x) (adapt f y) := rfl

@[simp] theorem lift_pure (a : A) :
    (liftM (m := m) (pure a) : _root_.ReaderT ρ m A) = pure a := rfl

@[simp] theorem lift_bind (x : m A) (k : A → m B) :
    (liftM (x >>= k) : _root_.ReaderT ρ m B) = liftM x >>= fun a => liftM (k a) := rfl

omit [Monad m] in
@[simp] theorem lift_iter [Iterate m] (step : A → m (B ⊕ A)) (a : A) :
    (liftM (iter step a) : _root_.ReaderT ρ m B) = iter (fun a => liftM (step a)) a := rfl

@[simp] theorem lift_pair (P : ParallelPairing m) (x : m A) (y : m B) :
    (liftM (P.pair x y) : _root_.ReaderT ρ m (A × B)) = P.reader.pair (liftM x) (liftM y) := rfl

end ReaderT
end Silmaril.Elgot
