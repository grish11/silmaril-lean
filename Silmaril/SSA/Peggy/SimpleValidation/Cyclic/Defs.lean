module

public import Silmaril.SSA.Peggy.Optimizer.Cyclic.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Automatic.Defs

/-! # Checked cyclic PEG optimization through SIMPLE reversion

Use the self-feedback matcher and replay with the eval/pass demand rank
from the single-loop region reverter. The target must also pass that
reverter's boundary and schedule checks.
-/

@[expose] public section

namespace Silmaril.SSA.Peggy.SimpleValidation.Cyclic

open PEG
open PEG.Simple.Revert.While
open Optimizer.Cyclic (Match matchAt)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params : List (Ty Data)} {result : Ty Data} {n : Nat}

inductive Rejection where
  | sourceRank
  | noCheckedRewrite
  | reversion
  deriving DecidableEq, Repr

structure Rewrite (g : Graph P params [result] (n + 1) 1) where
  site : Fin (n + 1)
  matched : Match g site
  targetRank : DemandRank n 1
  replay : matched.Replay targetRank

def tryRewrite (g : Graph P params [result] (n + 1) 1) (site : Fin (n + 1)) :
    Option (Rewrite g) := do
  let matched ← matchAt g site
  let rank := Region.Automatic.inferDemandRank matched.extract
  let replay ← matched.replay rank
  return ⟨site, matched, rank, replay⟩

def findRewrite (g : Graph P params [result] (n + 1) 1) : Option (Rewrite g) :=
  (List.finRange (n + 1)).findSome? (tryRewrite g)

structure Accepted (g : Graph P params [result] (n + 1) 1) (allowInvariant : Bool := false) where
  sourceRank : DemandRank (n + 1) 1
  sourceRanked : sourceRank.check g = true
  rewrite : Rewrite g
  reversion : Region.Certificate rewrite.matched.extract allowInvariant

variable {g : Graph P params [result] (n + 1) 1}

def Accepted.output {allowInvariant : Bool} (accepted : Accepted g allowInvariant) :
    PEG.Simple.Program P true params result :=
  accepted.reversion.revert

/-- Discover the first candidate with successful replay, then infer and
check the target's complete SIMPLE region schedule. -/
def optimize [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P params [result] (n + 1) 1) : Except Rejection (Accepted g) := do
  let rank := Region.Automatic.inferDemandRank g
  if ranked : rank.check g = true then
    let some rewrite := findRewrite g
      | .error .noCheckedRewrite
    let some reversion := Region.Automatic.extract rewrite.matched.extract
      | .error .reversion
    return ⟨rank, ranked, rewrite, reversion⟩
  else .error .sourceRank

end Silmaril.SSA.Peggy.SimpleValidation.Cyclic
