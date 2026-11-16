module

public import Silmaril.Games.Abstract.SessionIter3.Defs
public import Silmaril.Games.Abstract.SessionIter2.Thms
public import Silmaril.Proofs.Games.Abstract.SessionIter3.Iter

/-!
# Call prefixes of a session iteration of a total body (proofs)

`iterS t` is `iterT (mapT t iterAssoc)`. The reassociation `iterAssoc` keeps the call prefixes
(`StratOps.sat_mapT`) and totality, and the continuing chains of `mapT t iterAssoc` are the
`ContS` chains of `t`, so the results of `…SessionIter3.Iter` for `iterT` transfer to `iterS`.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionIter3

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratOps Silmaril.Games.Abstract.SessionIter
  Silmaril.Games.Abstract.SessionIter2 Silmaril.Games.Abstract.SessionIter3

universe u

variable {E : Sig.{u}} {S A B : Type u}

theorem total_mapT {C : Type u} {X : ObsTriple E S A B} (hX : Total X) (h : B → C) :
    Total (mapT X h) := by
  intro s a
  rcases hX s a with ⟨x, hx⟩ | hp | hi
  · exact .inl ⟨_, x, hx, rfl⟩
  · exact .inr (.inl hp)
  · exact .inr (.inr hi)

section Iter

variable {t : ObsTriple E S A ((B ⊕ A) ⊕ PUnit.{u + 1})}

theorem mem_mapT_iterAssoc_inr {s s' : S} {a a' : A} {c : List (Call E)} :
    (c, End.ret (.inr a') s') ∈ (mapT t iterAssoc).1 s a ↔
      (c, End.ret (.inl (.inr a')) s') ∈ t.1 s a := by
  constructor
  · rintro ⟨⟨c₀, e⟩, h, hx⟩
    simp only [Prod.mk.injEq] at hx
    obtain ⟨rfl, hx⟩ := hx
    rcases e with ⟨(b | a₀) | ⟨⟩, s₀⟩ | _ | _ <;> simp [FullFun.endMap, iterAssoc] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact h
  · intro h
    exact ⟨_, h, rfl⟩

theorem contChain_iff {s s' : S} {a a' : A} {c : List (Call E)} :
    FullFun.ContChain (mapT t iterAssoc).1 s a c s' a' ↔ ContS t s a c s' a' := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | step h₁ _ ih => exact .step (mem_mapT_iterAssoc_inr.1 h₁) ih
  · intro h
    induction h with
    | refl => exact .refl
    | step h₁ _ ih => exact .step (mem_mapT_iterAssoc_inr.2 h₁) ih

theorem satP_mapT_iterAssoc : satP (mapT t iterAssoc) = satP t :=
  congrArg (fun y : ObsTriple E S A ((B ⊕ PUnit.{u + 1}) ⊕ A) => y.2.1) (sat_mapT t iterAssoc)

theorem total_iterS (ht : Total t) : Total (iterS t) :=
  total_iterT (total_mapT ht iterAssoc)

theorem mem_contSatP {s : S} {a : A} {c : List (Call E)} {m : E.Op} :
    (c, m) ∈ contSatP t s a ↔
      ∃ c₁ s' a' c₂, ContS t s a c₁ s' a' ∧ (c₂, m) ∈ satP t s' a' ∧ c = c₁ ++ c₂ :=
  Iff.rfl

theorem satP_iterS_subset {s : S} {a : A} : satP (iterS t) s a ⊆ contSatP t s a := by
  rintro ⟨c, m⟩ h
  obtain ⟨c₁, s', a', c₂, hch, hm, rfl⟩ := exists_contChain_of_satP_iterT h
  rw [satP_mapT_iterAssoc] at hm
  exact ⟨c₁, s', a', c₂, contChain_iff.1 hch, hm, rfl⟩

theorem mem_satP_iterS_of_total (ht : Total t) {s : S} {a : A} {c : List (Call E)}
    {m : E.Op} :
    (c, m) ∈ satP (iterS t) s a ↔
      ∃ c₁ s' a' c₂, ContS t s a c₁ s' a' ∧ (c₂, m) ∈ satP t s' a' ∧ c = c₁ ++ c₂ := by
  show (c, m) ∈ satP (iterT (mapT t iterAssoc)) s a ↔ _
  rw [mem_satP_iterT_of_total (total_mapT ht iterAssoc), satP_mapT_iterAssoc]
  simp only [contChain_iff]

theorem satP_iterS_of_total (ht : Total t) : satP (iterS t) = contSatP t := by
  funext s a
  ext ⟨c, m⟩
  exact (mem_satP_iterS_of_total ht).trans mem_contSatP.symm

end Iter

end Silmaril.Proofs.Games.Abstract.SessionIter3
