module

public import Silmaril.Games.Abstract.StratOps.Defs
public import Silmaril.Games.Abstract.FullFun.Thms

/-!
# Premonoidal operations on observation triples: theorems

**The full parts are the `FullFun` operations** (`full_seqT`, `full_pureT`, `full_mapT`,
`full_comapT`, `full_whiskerRightT`, `full_whiskerLeftT`, `full_iterT`), by `rfl`. A triple is
determined by its full part and its pending calls (`ext_full`).
-/

public section

namespace Silmaril.Games.Abstract.StratOps

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs

universe u

variable {E : Sig.{u}} {S A B C D : Type u}

/-! ## Components -/

/-- A triple is its full part with its pending calls. -/
theorem ofFull_full (t : ObsTriple E S A B) : ofFull (full t) t.2.1 = t := rfl

/-- Triples with the same full part and pending calls are equal. -/
theorem ext_full {t t' : ObsTriple E S A B} (hf : full t = full t') (hp : t.2.1 = t'.2.1) :
    t = t' :=
  (ofFull_full t).symm.trans (hf ▸ hp ▸ ofFull_full t')

theorem full_seqT (t : ObsTriple E S A B) (u : ObsTriple E S B C) :
    full (seqT t u) = FullFun.seq (full t) (full u) := rfl

theorem full_pureT : full (pureT : ObsTriple E S A A) = FullFun.pure := rfl

theorem full_mapT (t : ObsTriple E S A B) (h : B → C) : full (mapT t h) = (full t).map h := rfl

theorem full_comapT {A' : Type u} (t : ObsTriple E S A B) (k : A' → A) :
    full (comapT t k) = (full t).comap k := rfl

theorem full_whiskerRightT (t : ObsTriple E S A B) (C : Type u) :
    full (whiskerRightT t C) = (full t).whiskerRight C := rfl

theorem full_whiskerLeftT (C : Type u) (t : ObsTriple E S A B) :
    full (whiskerLeftT C t) = (full t).whiskerLeft C := rfl

theorem full_iterT (t : ObsTriple E S A (B ⊕ A)) : full (iterT t) = FullFun.iter (full t) := rfl

end Silmaril.Games.Abstract.StratOps
