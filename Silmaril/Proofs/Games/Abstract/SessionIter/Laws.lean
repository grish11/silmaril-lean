module

public import Silmaril.Games.Abstract.SessionIter.Defs
public import Silmaril.Games.Abstract.SessionCat.Thms

/-!
# Session iteration: the iteration laws (proofs)

`iterS t` is `iterT (mapT t iterAssoc)`. Each law is the `StratOps` law for the reassociated
body: pure maps are moved through `mapT_mapT`, `seqT_mapT`, `mapT_seqT`, and the session
continuations (`retS`, `trapS`, `exitS`) are compared pointwise on sums.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionIter

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratOps Silmaril.Games.Abstract.SessionCat
  Silmaril.Games.Abstract.SessionIter

universe u

variable {E : Sig.{u}} {S A B C D : Type u}

theorem mapT_pureT_fst (h : A → B) (s : S) (a : A) :
    (mapT (pureT : ObsTriple E S A A) h).1 s a = {([], End.ret (h a) s)} := by
  simp [mapT, pureT, ofFull, full, FullFun.map, FullFun.pure, FullFun.endMap]

theorem comapT_pureT (h : A → B) : comapT (pureT : ObsTriple E S B B) h = mapT pureT h := by
  rw [← pureT_mapT_seqT, seqT_pureT]

/-- The continuation of one iteration step, in session form. -/
theorem comapT_caseT_pureT_iterAssoc (X : ObsTriple E S A (B ⊕ PUnit.{u + 1})) :
    comapT (caseT pureT X) iterAssoc = caseT (caseT retS X) trapS := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> funext s x <;> rcases x with (b | a) | ⟨⟩
  all_goals first
    | rfl
    | (simp only [comapT, caseT, ofFull, full, FullFun.comap, FullFun.case, AFun.case, iterAssoc,
        retS, trapS, Sum.elim_inl, Sum.elim_inr, mapT_pureT_fst]; rfl)

theorem iterS_unfold (t : ObsTriple E S A ((B ⊕ A) ⊕ PUnit.{u + 1})) :
    iterS t = seqS t (caseT retS (iterS t)) := by
  conv_lhs => rw [iterS, iterT_unfold, seqT_mapT, ← iterS]
  rw [seqS, comapT_caseT_pureT_iterAssoc]

theorem iterS_mapT (t : ObsTriple E S A ((B ⊕ A) ⊕ PUnit.{u + 1})) (h : B → C) :
    iterS (mapT t (Sum.map (Sum.map h id) id)) = mapT (iterS t) (Sum.map h id) := by
  have : (iterAssoc ∘ Sum.map (Sum.map h id) id : (B ⊕ A) ⊕ PUnit.{u + 1} → _) =
      Sum.map (Sum.map h id) id ∘ iterAssoc := by
    funext x; rcases x with (b | a) | ⟨⟩ <;> rfl
  rw [iterS, iterS, mapT_mapT, this, ← mapT_mapT, iterT_mapT]

theorem iterS_codiag (t : ObsTriple E S A (((B ⊕ A) ⊕ A) ⊕ PUnit.{u + 1})) :
    iterS (iterS t) = iterS (mapT t (Sum.map (Sum.elim id Sum.inr) id)) := by
  have : (Sum.elim id Sum.inr ∘ Sum.map iterAssoc id ∘ iterAssoc :
      ((B ⊕ A) ⊕ A) ⊕ PUnit.{u + 1} → (B ⊕ PUnit.{u + 1}) ⊕ A) =
      iterAssoc ∘ Sum.map (Sum.elim id Sum.inr) id := by
    funext x; rcases x with ((b | a) | a) | ⟨⟩ <;> rfl
  rw [iterS, iterS, ← iterT_mapT, iterT_codiag, mapT_mapT, mapT_mapT, iterS, mapT_mapT,
    Function.comp_assoc, this]

theorem mapT_exitS_fst (h : (B ⊕ A) ⊕ PUnit.{u + 1} → D) (s : S) (b : B) :
    (mapT (exitS : ObsTriple E S B ((B ⊕ A) ⊕ PUnit.{u + 1})) h).1 s b =
      {([], End.ret (h (.inl (.inl b))) s)} := by
  rw [exitS, mapT_mapT, mapT_pureT_fst]
  rfl

theorem mapT_trapS_fst (h : B ⊕ PUnit.{u + 1} → D) (s : S) (x : PUnit.{u + 1}) :
    (mapT (trapS : ObsTriple E S PUnit.{u + 1} (B ⊕ PUnit.{u + 1})) h).1 s x =
      {([], End.ret (h (.inr PUnit.unit)) s)} := by
  rw [trapS, mapT_mapT, mapT_pureT_fst]
  rfl

/-- A session body followed by a loop step, read as an `iterT` body. -/
theorem mapT_seqS_caseT_exitS (t : ObsTriple E S A ((B ⊕ C) ⊕ PUnit.{u + 1}))
    (u : ObsTriple E S C ((B ⊕ A) ⊕ PUnit.{u + 1})) :
    mapT (seqS t (caseT exitS u)) iterAssoc =
      seqT (mapT t iterAssoc) (caseT (mapT pureT Sum.inl) (mapT u iterAssoc)) := by
  rw [seqS, mapT_seqT, seqT_mapT]
  congr 1
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> funext s x <;> rcases x with (b | c) | ⟨⟩
  all_goals try rfl
  · change (mapT (exitS : ObsTriple E S B ((B ⊕ A) ⊕ PUnit.{u + 1})) iterAssoc).1 s b =
      (mapT (pureT : ObsTriple E S (B ⊕ PUnit.{u + 1}) _) Sum.inl).1 s (Sum.inl b)
    rw [mapT_exitS_fst, mapT_pureT_fst]
    rfl
  · change (mapT (trapS : ObsTriple E S PUnit.{u + 1} ((B ⊕ A) ⊕ PUnit.{u + 1})) iterAssoc).1 s _ =
      (mapT (pureT : ObsTriple E S (B ⊕ PUnit.{u + 1}) _) Sum.inl).1 s (Sum.inr PUnit.unit)
    rw [mapT_trapS_fst, mapT_pureT_fst]
    rfl

theorem iterS_dinat (t : ObsTriple E S A ((B ⊕ C) ⊕ PUnit.{u + 1}))
    (u : ObsTriple E S C ((B ⊕ A) ⊕ PUnit.{u + 1})) :
    iterS (seqS t (caseT exitS u)) =
      seqS t (caseT retS (iterS (seqS u (caseT exitS t)))) := by
  rw [iterS, mapT_seqS_caseT_exitS, iterT_dinat, ← mapT_seqS_caseT_exitS, ← iterS, seqT_mapT,
    comapT_caseT_pureT_iterAssoc]
  rfl

theorem iterS_uniform_comap {A' : Type u} {F : ObsTriple E S A ((B ⊕ A) ⊕ PUnit.{u + 1})}
    {G : ObsTriple E S A' ((B ⊕ A') ⊕ PUnit.{u + 1})} {k : A' → A}
    (hFG : comapT F k = mapT G (Sum.map (Sum.map id k) id)) :
    comapT (iterS F) k = iterS G := by
  refine iterT_uniform_comap ?_
  have : (iterAssoc ∘ Sum.map (Sum.map id k) id : (B ⊕ A') ⊕ PUnit.{u + 1} → _) =
      Sum.map id k ∘ iterAssoc := by
    funext x; rcases x with (b | a) | ⟨⟩ <;> rfl
  rw [← mapT_comapT, hFG, mapT_mapT, mapT_mapT, this]

theorem seqS_mapT_pureT (h : A → B) (X : ObsTriple E S B (C ⊕ PUnit.{u + 1})) :
    seqS (mapT pureT (Sum.inl ∘ h)) X = comapT X h := by
  rw [seqS, pureT_mapT_seqT]
  rfl

theorem iterS_uniform {A' : Type u} {F : ObsTriple E S A ((B ⊕ A) ⊕ PUnit.{u + 1})}
    {G : ObsTriple E S A' ((B ⊕ A') ⊕ PUnit.{u + 1})} (h : A' → A)
    (hFG : seqS (mapT pureT (Sum.inl ∘ h)) F = mapT G (Sum.map (Sum.map id h) id)) :
    seqS (mapT pureT (Sum.inl ∘ h)) (iterS F) = iterS G := by
  rw [seqS_mapT_pureT] at hFG ⊢
  exact iterS_uniform_comap hFG

end Silmaril.Proofs.Games.Abstract.SessionIter
