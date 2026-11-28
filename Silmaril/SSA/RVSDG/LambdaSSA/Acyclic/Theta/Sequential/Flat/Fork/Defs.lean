module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Defs

/-! # Disjoint typed CFG arms with a common pair of exits -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat

open LinearChain (Site localSite externalSite)
open TwoBlock.TwoExit (Carrier)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A M Y E D X : τ}
variable (p : Fragment Φ M E D) (q : Fragment Φ Y E D)

def forkTypes : Fin (p.count + q.count) → τ := Fin.addCases p.localTypes q.localTypes

abbrev ForkLabels := List.ofFn (forkTypes p q) ++ [E,D]

@[simp] theorem forkLeft_type (i : Fin p.count) :
    forkTypes p q (i.castAdd q.count) = p.localTypes i := Fin.addCases_left i

@[simp] theorem forkRight_type (i : Fin q.count) :
    forkTypes p q (i.natAdd p.count) = q.localTypes i := Fin.addCases_right i

def forkLeft (site : Site p.Labels X) : Site (ForkLabels p q) X :=
  redirect (R := p.localTypes)
    (fun i => forkLeft_type p q i ▸ localSite (forkTypes p q) [E,D] (i.castAdd q.count))
    (externalSite (forkTypes p q) [E,D]) site

def forkRight (site : Site q.Labels X) : Site (ForkLabels p q) X :=
  redirect (R := q.localTypes)
    (fun i => forkRight_type p q i ▸ localSite (forkTypes p q) [E,D] (i.natAdd p.count))
    (externalSite (forkTypes p q) [E,D]) site

/-- The two arm block tables are relocated independently of dispatch. -/
def forkWith (entry : Block Φ (ForkLabels p q) A) : Fragment Φ A E D where
  extra := p.count + q.extra
  localTypes := forkTypes p q
  entry := entry
  blocks := Fin.addCases (motive := fun i => Block Φ (ForkLabels p q) (forkTypes p q i))
    (fun i => (forkLeft_type p q i).symm ▸ (p.blocks i).rename (forkLeft p q))
    (fun i => (forkRight_type p q i).symm ▸ (q.blocks i).rename (forkRight p q))

/-- Dispatch a binary choice directly to the relocated selected arm. -/
def forkCase (gate : TwoBlock.Instruction Φ A (Silmaril.coprod M Y)) : Fragment Φ A E D :=
  forkWith p q (.choose gate (p.entry.rename (forkLeft p q)) (q.entry.rename (forkRight p q)))

/-- The left alternatives of the carrier have the same type. Both select the
left arm, with their original value as its entry payload. -/
def fork (gate : TwoBlock.Instruction Φ A (Carrier Y M M)) : Fragment Φ A E D :=
  forkWith p q (.choose gate (.split (p.entry.rename (forkLeft p q)) (p.entry.rename (forkLeft p q)))
    (q.entry.rename (forkRight p q)))

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat
