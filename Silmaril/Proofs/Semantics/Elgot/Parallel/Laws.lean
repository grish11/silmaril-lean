module

public import Silmaril.Semantics.Elgot.Parallel.Defs

public section

namespace Silmaril.Elgot.ParallelPairing.Proofs

universe u v

variable {m : Type u → Type v} [Monad m] [LawfulMonad m]
variable (P : ParallelPairing m) {A B : Type u}

theorem leftUnit (y : m B) :
    (Prod.snd <$> P.pair (pure (PUnit.unit : PUnit.{u + 1})) y) = y := by
  calc
    _ = (Prod.snd ∘ Prod.swap) <$> P.pair y (pure PUnit.unit) := by
      rw [comp_map, P.swap]
    _ = y := P.rightUnit y

theorem pair_pure_right (x : m A) (b : B) :
    P.pair x (pure b) = ((fun a => (a, b)) <$> x) := by
  calc
    _ = (Prod.map id (fun _ : PUnit.{u + 1} => b)) <$> P.pair x (pure PUnit.unit) := by
      simpa only [id_map, map_pure] using
        (P.natural id (fun _ : PUnit.{u + 1} => b) x (pure PUnit.unit)).symm
    _ = (fun a => (a, b)) <$> (Prod.fst <$> P.pair x (pure PUnit.unit)) :=
      comp_map Prod.fst (fun a => (a, b)) (P.pair x (pure PUnit.unit))
    _ = _ := congrArg (Functor.map (fun a => (a, b))) (P.rightUnit x)

theorem pair_pure_left (a : A) (y : m B) :
    P.pair (pure a) y = ((fun b => (a, b)) <$> y) := by
  calc
    _ = (Prod.map (fun _ : PUnit.{u + 1} => a) id) <$> P.pair (pure PUnit.unit) y := by
      simpa only [id_map, map_pure] using
        (P.natural (fun _ : PUnit.{u + 1} => a) id (pure PUnit.unit) y).symm
    _ = (fun b => (a, b)) <$> (Prod.snd <$> P.pair (pure PUnit.unit) y) :=
      comp_map Prod.snd (fun b => (a, b)) (P.pair (pure PUnit.unit) y)
    _ = _ := congrArg (Functor.map (fun b => (a, b))) (leftUnit P y)

end Silmaril.Elgot.ParallelPairing.Proofs
