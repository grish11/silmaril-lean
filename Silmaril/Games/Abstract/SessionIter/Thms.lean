module

public import Silmaril.Games.Abstract.SessionIter.Defs
public import Silmaril.Games.Abstract.SessionCat.Thms
import Silmaril.Proofs.Games.Abstract.SessionIter.Laws
import Silmaril.Proofs.Games.Abstract.SessionIter.Det

/-!
# Session iteration with store-retaining traps: theorems

The laws hold for all store-retaining session triples `ObsTriple E S A (B ⊕ PUnit)`, with no
hypothesis: they are transported from the `StratOps.iterT` laws along the reassociation
`iterAssoc` (proofs in `Silmaril.Proofs.Games.Abstract.SessionIter.Laws`).

* `iterS_unfold` (**the fixpoint law**, session form): one body round, sequenced (`seqS`, so a
  continuing trap aborts the iteration keeping its store) with an exit (`retS`) or another
  iteration;
* `iterS_mapT` (**naturality** in the exit value), `iterS_dinat` (**dinaturality**, with `exitS`
  continuing a body into another one), `iterS_codiag` (**the codiagonal law**);
* `iterS_uniform_comap`, `iterS_uniform` (**uniformity** along a pure map of the loop argument,
  in pre-composition and session (Elgot) form; `seqS_mapT_pureT` relates them).

**Returns, plain traps and determinism** (proofs in `…SessionIter.Det`):

* `mem_iterS_ret`, `mem_seqS_ret`: the returns of `iterS t` and `seqS t u` are the one-round
  relations `IterRet t` and `SeqRet t u`;
* `noPlainTrap_iterS`, `noPlainTrap_seqS`: no plain traps are created;
* `retDet_iterS`, `retDet_seqS`: deterministic returns (`SessionCat.RetDet`) are preserved;
* `det_iterS`: determinism given answers (`AFun.Det`) is preserved by iteration, an infinite
  silent chain of a deterministic body being its only behaviour.
-/

public section

namespace Silmaril.Games.Abstract.SessionIter

open Silmaril.Games Silmaril.Games.Abstract.StratObs Silmaril.Games.Abstract.StratOps
  Silmaril.Games.Abstract.StratSession Silmaril.Games.Abstract.SessionCat

universe u

variable {E : Sig.{u}} {S A B C : Type u}

/-! ## Iteration laws -/

/-- **The fixpoint law**: one body round, then exit with the value or iterate again; a continuing
trap of the body aborts the iteration, keeping its store. -/
theorem iterS_unfold (t : ObsTriple E S A ((B ⊕ A) ⊕ PUnit.{u + 1})) :
    iterS t = seqS t (caseT retS (iterS t)) :=
  Silmaril.Proofs.Games.Abstract.SessionIter.iterS_unfold t

/-- **Naturality of session iteration** in the exit value. -/
theorem iterS_mapT (t : ObsTriple E S A ((B ⊕ A) ⊕ PUnit.{u + 1})) (h : B → C) :
    iterS (mapT t (Sum.map (Sum.map h id) id)) = mapT (iterS t) (Sum.map h id) :=
  Silmaril.Proofs.Games.Abstract.SessionIter.iterS_mapT t h

/-- **Dinaturality of session iteration**: `iterS (t ; [exit, u]) = t ; [ret, iterS (u ; [exit, t])]`
in session sequencing. -/
theorem iterS_dinat (t : ObsTriple E S A ((B ⊕ C) ⊕ PUnit.{u + 1}))
    (u : ObsTriple E S C ((B ⊕ A) ⊕ PUnit.{u + 1})) :
    iterS (seqS t (caseT exitS u)) = seqS t (caseT retS (iterS (seqS u (caseT exitS t)))) :=
  Silmaril.Proofs.Games.Abstract.SessionIter.iterS_dinat t u

/-- **The codiagonal law**: `iterS (iterS t) = iterS (t ; [id, inr] + id)`. -/
theorem iterS_codiag (t : ObsTriple E S A (((B ⊕ A) ⊕ A) ⊕ PUnit.{u + 1})) :
    iterS (iterS t) = iterS (mapT t (Sum.map (Sum.elim id Sum.inr) id)) :=
  Silmaril.Proofs.Games.Abstract.SessionIter.iterS_codiag t

/-- **Uniformity of session iteration** along a pure map `k` of the loop argument,
pre-composition form. -/
theorem iterS_uniform_comap {A' : Type u} {F : ObsTriple E S A ((B ⊕ A) ⊕ PUnit.{u + 1})}
    {G : ObsTriple E S A' ((B ⊕ A') ⊕ PUnit.{u + 1})} {k : A' → A}
    (hFG : comapT F k = mapT G (Sum.map (Sum.map id k) id)) :
    comapT (iterS F) k = iterS G :=
  Silmaril.Proofs.Games.Abstract.SessionIter.iterS_uniform_comap hFG

/-- Session sequencing after a pure value map is pre-composition. -/
theorem seqS_mapT_pureT (h : A → B) (X : ObsTriple E S B (C ⊕ PUnit.{u + 1})) :
    seqS (mapT pureT (Sum.inl ∘ h)) X = comapT X h :=
  Silmaril.Proofs.Games.Abstract.SessionIter.seqS_mapT_pureT h X

/-- **Uniformity of session iteration** (Elgot form) along a pure map `h`: if
`h ; F = G ; (id + h) + id` then `h ; iterS F = iterS G`, in session sequencing. -/
theorem iterS_uniform {A' : Type u} {F : ObsTriple E S A ((B ⊕ A) ⊕ PUnit.{u + 1})}
    {G : ObsTriple E S A' ((B ⊕ A') ⊕ PUnit.{u + 1})} (h : A' → A)
    (hFG : seqS (mapT pureT (Sum.inl ∘ h)) F = mapT G (Sum.map (Sum.map id h) id)) :
    seqS (mapT pureT (Sum.inl ∘ h)) (iterS F) = iterS G :=
  Silmaril.Proofs.Games.Abstract.SessionIter.iterS_uniform h hFG

/-! ## Returns, plain traps and determinism -/

/-- **The returns of a session iteration** are continuing body returns followed by an exit or a
continuing trap. -/
theorem mem_iterS_ret {t : ObsTriple E S A ((B ⊕ A) ⊕ PUnit.{u + 1})} {s s' : S} {a : A}
    {c : List (Call E)} {x : B ⊕ PUnit.{u + 1}} :
    (c, End.ret x s') ∈ (iterS t).1 s a ↔ IterRet t s a c x s' :=
  Silmaril.Proofs.Games.Abstract.SessionIter.mem_iterS_ret

/-- **The returns of a session sequence**: a continuing trap of the first part, or its value
continued by a return of the second. -/
theorem mem_seqS_ret {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
    {u : ObsTriple E S B (C ⊕ PUnit.{u + 1})} {s s' : S} {a : A} {c : List (Call E)}
    {x : C ⊕ PUnit.{u + 1}} :
    (c, End.ret x s') ∈ (seqS t u).1 s a ↔ SeqRet t u s a c x s' :=
  Silmaril.Proofs.Games.Abstract.SessionIter.mem_seqS_ret

/-- Session iteration creates no plain trap. -/
theorem noPlainTrap_iterS {t : ObsTriple E S A ((B ⊕ A) ⊕ PUnit.{u + 1})} (ht : NoPlainTrap t) :
    NoPlainTrap (iterS t) :=
  Silmaril.Proofs.Games.Abstract.SessionIter.noPlainTrap_iterS ht

/-- Session sequencing creates no plain trap. -/
theorem noPlainTrap_seqS {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
    {u : ObsTriple E S B (C ⊕ PUnit.{u + 1})} (ht : NoPlainTrap t) (hu : NoPlainTrap u) :
    NoPlainTrap (seqS t u) :=
  Silmaril.Proofs.Games.Abstract.SessionIter.noPlainTrap_seqS ht hu

/-- **Session iteration preserves deterministic returns.** -/
theorem retDet_iterS {t : ObsTriple E S A ((B ⊕ A) ⊕ PUnit.{u + 1})} (ht : RetDet t) :
    RetDet (iterS t) :=
  Silmaril.Proofs.Games.Abstract.SessionIter.retDet_iterS ht

/-- **Session sequencing preserves deterministic returns.** -/
theorem retDet_seqS {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
    {u : ObsTriple E S B (C ⊕ PUnit.{u + 1})} (ht : RetDet t) (hu : RetDet u) :
    RetDet (seqS t u) :=
  Silmaril.Proofs.Games.Abstract.SessionIter.retDet_seqS ht hu

/-- **Session iteration preserves determinism given answers.** -/
theorem det_iterS {t : ObsTriple E S A ((B ⊕ A) ⊕ PUnit.{u + 1})} (ht : AFun.Det t.1) :
    AFun.Det (iterS t).1 :=
  Silmaril.Proofs.Games.Abstract.SessionIter.det_iterS ht

end Silmaril.Games.Abstract.SessionIter
