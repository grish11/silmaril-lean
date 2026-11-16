module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Terms.Defs
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.WTerms

@[expose] public section

/-!
# Checked bounds and set interpretation of the object templates

The bounds concern syntax. The coherence recursor's motive is `Uₙ`; typing
that motive by the universe rule uses `Uₙ₊₁`, so this particular construction's
direct derivation needs that next available level. No minimal-budget theorem
or impossibility result is asserted. Full derivability preservation remains
separate from these interpretation equations.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.Description

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
open Silmaril.Logic.TypeTheory.ExtensionalMLTT

universe u

theorem raw_universeBound (S : Description) : S.raw.universeBound ≤ S.universeBound :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.raw_bound S

theorem fibre_universeBound (S : Description) (n : ℕ) (i : Tm 0) :
    (S.fibre n i).universeBound ≤ max (max S.universeBound (n + 1)) i.universeBound :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.fibre_bound S n i

/-- Both projections from the tagged label fill the original position binders. -/
theorem positions_denoteIn (S : Description) (U : ℕ → ZFSet.{u})
    (ρ : String → ZFSet.{u}) (a : ZFSet.{u}) :
    S.positions.denoteIn U ρ (Fin.cons a Fin.elim0) =
      S.position.denoteIn U ρ
        (Fin.cons (SetSem.snd a) (Fin.cons (SetSem.fst a) Fin.elim0)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.positions_denoteIn S U ρ a

/-- The requested child index may depend on the result index, shape, and position. -/
theorem childIndexAt_denoteIn {k : ℕ} (S : Description) (U : ℕ → ZFSet.{u})
    (ρ : String → ZFSet.{u}) (β : Fin k → ZFSet.{u}) (label p : Tm k) :
    (S.childIndexAt label p).denoteIn U ρ β =
      S.next.denoteIn U ρ (Fin.cons (p.denoteIn U ρ β)
        (Fin.cons (SetSem.snd (label.denoteIn U ρ β))
          (Fin.cons (SetSem.fst (label.denoteIn U ρ β)) Fin.elim0))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.childIndexAt_denoteIn
    S U ρ β label p

theorem root_denoteIn {k : ℕ} (S : Description) (U : ℕ → ZFSet.{u})
    (ρ : String → ZFSet.{u}) (β : Fin k → ZFSet.{u}) (t : Tm k) :
    (S.root t).denoteIn U ρ β =
      WSet.wrec (S.totalShape.denoteIn U ρ Fin.elim0)
        (fun a => S.positions.denoteIn U ρ (Fin.cons a Fin.elim0))
        (S.rootStep.denoteIn U ρ Fin.elim0) (t.denoteIn U ρ β) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.root_denoteIn S U ρ β t

theorem coherence_denoteIn {k : ℕ} (S : Description) (n : ℕ) (U : ℕ → ZFSet.{u})
    (ρ : String → ZFSet.{u}) (β : Fin k → ZFSet.{u}) (t : Tm k) :
    (S.coherence n t).denoteIn U ρ β =
      WSet.wrec (S.totalShape.denoteIn U ρ Fin.elim0)
        (fun a => S.positions.denoteIn U ρ (Fin.cons a Fin.elim0))
        ((S.coherenceStep n).denoteIn U ρ Fin.elim0) (t.denoteIn U ρ β) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.coherence_denoteIn S n U ρ β t

/-- The object fibre has exactly the expected nested dependent-sum interpretation. -/
theorem fibre_denoteIn (S : Description) (n : ℕ) (U : ℕ → ZFSet.{u})
    (ρ : String → ZFSet.{u}) (i : Tm 0) :
    let labels := S.totalShape.denoteIn U ρ Fin.elim0
    let positions := fun a => S.positions.denoteIn U ρ (Fin.cons a Fin.elim0)
    let root := WSet.wrec labels positions (S.rootStep.denoteIn U ρ Fin.elim0)
    let coherent := WSet.wrec labels positions ((S.coherenceStep n).denoteIn U ρ Fin.elim0)
    (S.fibre n i).denoteIn U ρ Fin.elim0 =
      SetSem.sigma (S.raw.denoteIn U ρ Fin.elim0) (fun t =>
        SetSem.sigma (SetSem.truth (root t = i.denoteIn U ρ Fin.elim0))
          (fun _ => coherent t)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.fibre_denoteIn S n U ρ i

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.Description

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Tm

@[simp] theorem universeBound_castLE {n m : ℕ} (t : Tm n) (h : n ≤ m) :
    (t.castLE h).universeBound = t.universeBound :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.bound_castLE h t

@[simp] theorem universeBound_wkn {k : ℕ} (t : Tm k) (j : ℕ) :
    (t.wkn j).universeBound = t.universeBound :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.bound_wkn j t

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Tm
