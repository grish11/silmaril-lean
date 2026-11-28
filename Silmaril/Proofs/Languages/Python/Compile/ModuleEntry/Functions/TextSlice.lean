module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Defs

public section
namespace Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions

open Silmaril.Languages.Python.Compile
open Silmaril.Languages.Python.Compile.ModuleEntry
open Silmaril.Languages.Python.Compile.ModuleEntry.Functions
open Silmaril.Languages.Python.Source (Scope)

theorem ordinaryIf_textSliceGuard_none {scope : Scope} {condition yes no actions}
    (checked : ModuleEntry.Translation scope [.if_ condition yes no] actions) :
    textSliceGuard? scope (.if_ condition yes no) = none := by
  cases textSliceGuard? scope (.if_ condition yes no) with
  | none => rfl
  | some candidate =>
    obtain ⟨guard, translated⟩ := candidate
    cases translated
    cases checked with
    | assign binding _ _ => cases binding
    | literalIf arms _ _ _ _ => simp [literalArmStatement, binding?] at arms

end Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions
