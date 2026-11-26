module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Branch.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Case.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Nested.Defs

/-! # Forward scripts for the five structural entry equations -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.ScriptReplay

open WithEntryLet (Site)

/-- One oriented generator at an address in the current region. -/
inductive Move where
  | bindBranch (site : Site)
  | unaryEntry (site : Site)
  | binaryEntry (site : Site)
  | caseEntry (site : Site)
  | nestedEntry (site : Site)

def Move.apply {Φ : Type v} (move : Move) (r : Region Φ) : Option (Region Φ) :=
  match move with
  | .bindBranch site => BranchReplay.bindAt site r
  | .unaryEntry site => site.move r
  | .binaryEntry site => move₂ site r
  | .caseEntry site => CaseReplay.hoistAt site r
  | .nestedEntry site => NestedReplay.hoistAt site r

/-- Run forward actions in order. Each address is interpreted in the result
of the preceding action. A missing redex or address stops the script. -/
def run {Φ : Type v} : List Move → Region Φ → Option (Region Φ)
  | [], r => some r
  | move :: rest, r => move.apply r >>= run rest

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- A successful script with exact input and exit types at every region
in the chain. The step premise is a literal forward action at its address.
The address permits surrounding region binders, case arms, and CFG entries
and rows. Symmetry of the resulting equality supplies no inverse action.
Label-substitution congruence, term rewrites, and intervening Paper
equations need separate replay. -/
inductive Trace (Γ : VCtx τ) (L : LCtx τ) : List Move → Region Φ → Region Φ → Prop where
  | nil {r : Region Φ} (typed : HasType Γ r L) : Trace Γ L [] r r
  | cons {move : Move} {rest : List Move} {r next s : Region Φ}
      (typed : HasType Γ r L) (step : move.apply r = some next) (tail : Trace Γ L rest next s) :
      Trace Γ L (move :: rest) r s

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.ScriptReplay
