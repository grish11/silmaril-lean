module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Aliases.Syntax.Defs
public import Silmaril.Logic.Matching.GeneralFixedPoint.SetObjects.Thms
public import Silmaril.Logic.Kore.FixedPoint.Checking.Defs
public import Silmaril.Logic.Kore.Modules.Checking.Defs
public import Silmaril.Logic.Matching.GeneralFixedPoint.Institution

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Aliases

namespace Checking
open Modules.Checking

def elaborate (scope : Modules.Scope) (aliases : List Declaration) : Nat → (sets objects : Names) →
    (s : String) → RawPattern → Option (Pattern scope sets objects s)
  | 0, _, _, _, _ => none
  | _ + 1, _, _, _, .domainValue _ _ => none
  | _ + 1, _, objects, s, .evar name actual => do
      if actual ≠ s || !namedSort scope s then none else do
      let i ← lookup objects name
      if h : context objects i = s then some (h ▸ .base (.var i)) else none
  | _ + 1, sets, _, s, .svar name actual => do
      if actual ≠ s || !namedSort scope s then none else do
      let i ← lookup sets name
      if h : context sets i = s then some (h ▸ .setvar i) else none
  | _ + 1, _, _, s, .top actual =>
      if actual = s && namedSort scope s then some (.base Matching.FirstOrder.Pattern.top) else none
  | _ + 1, _, _, s, .bottom actual =>
      if actual = s && namedSort scope s then some (.base Matching.FirstOrder.Pattern.bottom) else none
  | n + 1, sets, objects, s, .neg actual p => do
      if actual ≠ s then none else
      return .neg (← elaborate scope aliases n sets objects s p)
  | n + 1, sets, objects, s, .conj actual p q => do
      if actual ≠ s then none else
      return .conj (← elaborate scope aliases n sets objects s p) (← elaborate scope aliases n sets objects s q)
  | n + 1, sets, objects, s, .disj actual p q => do
      if actual ≠ s then none else
      return .disj (← elaborate scope aliases n sets objects s p) (← elaborate scope aliases n sets objects s q)
  | n + 1, sets, objects, s, .ex actual name b p => do
      if actual ≠ s || !namedSort scope b then none else
      return .ex b (← elaborate scope aliases n sets ((name, b) :: objects) s p)
  | n + 1, sets, objects, s, .all actual name b p => do
      if actual ≠ s || !namedSort scope b then none else
      return Matching.GeneralFixedPoint.Pattern.all (b := b) (← elaborate scope aliases n sets ((name, b) :: objects) s p)
  | n + 1, sets, objects, s, .mu name actual p => do
      if actual ≠ s || !namedSort scope s then none else
      return .mu (← elaborate scope aliases n ((name, s) :: sets) objects s p)
  | n + 1, sets, objects, s, .nu name actual p => do
      if actual ≠ s || !namedSort scope s then none else
      return .nu (← elaborate scope aliases n ((name, s) :: sets) objects s p)
  | n + 1, sets, objects, s, .app name args => do
      match scope.symbols.attach.find? (fun d => d.val.declaration.name == name) with
      | some d => do
          if h : d.val.declaration.result = s then
            if len : args.length = d.val.declaration.arguments.length then do
              let ps ← collect (fun i : Fin d.val.declaration.arguments.length =>
                elaborate scope aliases n sets objects (d.val.declaration.arguments.get i)
                  (args.get ⟨i.val, by omega⟩))
              return .app ⟨d.val, d.property, by simp, h⟩ ps
            else none
          else none
      | none => do
          let d ← aliases.find? (fun d => d.symbol.name == name)
          if d.valid scope && d.symbol.result == s && args.length == d.parameters.length then do
            let body ← elaborate scope aliases n (d.names true) (d.names false) s d.body
            let σ ← collect (fun i : Fin (d.names false).length => do
              let arg ← d.argument args false ((d.names false).get i).1
              elaborate scope aliases n sets objects (context (d.names false) i) arg)
            let τ ← collect (fun i : Fin (d.names true).length => do
              let arg ← d.argument args true ((d.names true).get i).1
              elaborate scope aliases n sets objects (context (d.names true) i) arg)
            return body.substitute τ σ
          else none

/-- Free variables require explicit sorted contexts; closed input uses two empty
contexts. This reader checks actual text and returns a native fixed-point AST. -/
def read (scope : Modules.Scope) (aliases : List Declaration) (fuel : Nat) (sets objects : Names) (s text : String) :
    Option (Pattern scope sets objects s) := do
  elaborate scope aliases fuel sets objects s (← GeneralFixedPoint.Syntax.parse text)
end Checking
end Silmaril.Logic.Kore.GeneralFixedPoint.Aliases
