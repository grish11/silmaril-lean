module

public import Silmaril.Logic.FirstOrder.Variables.Thms

@[expose] public section
namespace Silmaril.Logic.Reachability.Derivation.FirstOrder
open Silmaril.Logic.Institution.Examples

/-- Source patterns are actual FOL formulas with a distinguished cfg coordinate0. -/
abbrev Pattern (Sg : FOL.Signature) (cfg : Sg.S) {k : Nat} (Γ : Fin k → Sg.S) :=
  FOL.Formula Sg (Fin.cases cfg Γ)

structure Claim (Sg : FOL.Signature) (cfg : Sg.S) {k : Nat} (Γ : Fin k → Sg.S) where
  pre : Pattern Sg cfg Γ
  post : Pattern Sg cfg Γ

end Silmaril.Logic.Reachability.Derivation.FirstOrder
