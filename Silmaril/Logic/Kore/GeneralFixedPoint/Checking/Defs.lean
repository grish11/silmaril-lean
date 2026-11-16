module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Syntax.Defs
public import Silmaril.Logic.Kore.FixedPoint.Checking.Defs
public import Silmaril.Logic.Kore.Modules.Checking.Defs
public import Silmaril.Logic.Matching.GeneralFixedPoint.Institution

@[expose] public section
namespace Silmaril.Logic.Kore.GeneralFixedPoint

abbrev Names := FixedPoint.Names
abbrev context := FixedPoint.context
abbrev lookup := FixedPoint.lookup

abbrev Pattern (scope : Modules.Scope) (sets objects : Names) (s : String) :=
  Matching.GeneralFixedPoint.Pattern scope.signature (context sets) (context objects) s

namespace Checking
open Modules.Checking

def elaborate (scope : Modules.Scope) : Nat → (sets objects : Names) →
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
      return .neg (← elaborate scope n sets objects s p)
  | n + 1, sets, objects, s, .conj actual p q => do
      if actual ≠ s then none else
      return .conj (← elaborate scope n sets objects s p) (← elaborate scope n sets objects s q)
  | n + 1, sets, objects, s, .disj actual p q => do
      if actual ≠ s then none else
      return .disj (← elaborate scope n sets objects s p) (← elaborate scope n sets objects s q)
  | n + 1, sets, objects, s, .ex actual name b p => do
      if actual ≠ s || !namedSort scope b then none else
      return .ex b (← elaborate scope n sets ((name, b) :: objects) s p)
  | n + 1, sets, objects, s, .all actual name b p => do
      if actual ≠ s || !namedSort scope b then none else
      return Matching.GeneralFixedPoint.Pattern.all (b := b) (← elaborate scope n sets ((name, b) :: objects) s p)
  | n + 1, sets, objects, s, .mu name actual p => do
      if actual ≠ s || !namedSort scope s then none else
      return .mu (← elaborate scope n ((name, s) :: sets) objects s p)
  | n + 1, sets, objects, s, .nu name actual p => do
      if actual ≠ s || !namedSort scope s then none else
      return .nu (← elaborate scope n ((name, s) :: sets) objects s p)
  | n + 1, sets, objects, s, .app name args => do
      let d ← scope.symbols.attach.find? (fun d => d.val.declaration.name == name)
      if h : d.val.declaration.result = s then
        if len : args.length = d.val.declaration.arguments.length then do
          let ps ← collect (fun i : Fin d.val.declaration.arguments.length =>
            elaborate scope n sets objects (d.val.declaration.arguments.get i)
              (args.get ⟨i.val, by omega⟩))
          return .app ⟨d.val, d.property, by simp, h⟩ ps
        else none
      else none

/-- Free variables require explicit sorted contexts; closed input uses two empty
contexts. This reader checks actual text and returns a native fixed-point AST. -/
def read (scope : Modules.Scope) (fuel : Nat) (sets objects : Names) (s text : String) :
    Option (Pattern scope sets objects s) := do
  elaborate scope fuel sets objects s (← Syntax.parse text)
end Checking
end Silmaril.Logic.Kore.GeneralFixedPoint
