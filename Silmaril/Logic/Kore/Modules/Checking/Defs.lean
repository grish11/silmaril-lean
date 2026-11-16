module

public import Silmaril.Logic.Kore.Modules.Syntax.Defs
public import Silmaril.Logic.Kore.FirstOrder.Institution

/-! Checked monomorphic declaration scopes and capture-avoiding elaboration.
Symbols retain their originating declaration; diamond imports do not rename or
copy symbols. Aliases are checked macros, never arbitrary model operations. -/
@[expose] public section
namespace Silmaril.Logic.Kore.Modules
open Algebraic.ManySorted (Signature)

/-- Origin identity is preserved through every import path. -/
structure Origin where
  moduleName : String
  declarationIndex : Nat
  deriving DecidableEq, Repr

structure NamedSymbol where
  origin : Origin
  declaration : SymbolDeclaration
  deriving DecidableEq, Repr

structure NamedAlias where
  origin : Origin
  declaration : AliasDeclaration
  deriving Repr

structure Scope where
  sorts : List (Origin × String)
  symbols : List NamedSymbol
  aliases : List NamedAlias
  deriving Repr

/-- Only symbols at their actual declared profile inhabit this signature. -/
def Scope.signature (scope : Scope) : Signature String where
  operations _n inputs output := {symbol : NamedSymbol // symbol ∈ scope.symbols ∧
    symbol.declaration.arguments = List.ofFn inputs ∧ symbol.declaration.result = output}

namespace Checking

/-- Sorted variable renaming, including binder lifting. -/
def rename {A : Signature String} {k l : Nat} {Γ : Fin k → String} {Δ : Fin l → String}
    (f : (i : Fin k) → {j : Fin l // Δ j = Γ i}) {s : String} :
    FirstOrder.Pattern A Γ s → FirstOrder.Pattern A Δ s
  | .evar i => (f i).property ▸ .evar (f i).val
  | .app sym args => .app sym (fun i => rename f (args i))
  | .top => .top
  | .bottom => .bottom
  | .not p => .not (rename f p)
  | .and p q => .and (rename f p) (rename f q)
  | .or p q => .or (rename f p) (rename f q)
  | .implies p q => .implies (rename f p) (rename f q)
  | .iff p q => .iff (rename f p) (rename f q)
  | .exists b p => .exists b (rename (Fin.cases ⟨0, rfl⟩
      (fun i => ⟨(f i).val.succ, (f i).property⟩)) p)
  | .forall b p => .forall b (rename (Fin.cases ⟨0, rfl⟩
      (fun i => ⟨(f i).val.succ, (f i).property⟩)) p)

abbrev Binding (A : Signature String) {k : Nat} (Γ : Fin k → String) :=
  String × (s : String) × FirstOrder.Pattern A Γ s

def weakenBinding {A : Signature String} {k : Nat} {Γ : Fin k → String}
    (b : String) (v : Binding A Γ) : Binding A (Fin.cases b Γ) :=
  ⟨v.1, v.2.1, rename (Γ := Γ) (Δ := Fin.cases b Γ) (fun i => ⟨i.succ, rfl⟩) v.2.2⟩

def bind {A : Signature String} {k : Nat} {Γ : Fin k → String}
    (name b : String) (vs : List (Binding A Γ)) : List (Binding A (Fin.cases b Γ)) :=
  ⟨name, b, .evar 0⟩ :: vs.map (weakenBinding b)

def lookupVariable {A : Signature String} {k : Nat} {Γ : Fin k → String}
    (vs : List (Binding A Γ)) (name s : String) : Option (FirstOrder.Pattern A Γ s) := do
  let v ← vs.find? (fun v => v.1 == name)
  if h : v.2.1 = s then some (h ▸ v.2.2) else none

/-- Collect a dependent finite family without assuming choice or a success proof. -/
def collect {n : Nat} {α : Fin n → Type} (xs : (i : Fin n) → Option (α i)) :
    Option ((i : Fin n) → α i) :=
  match n with
  | 0 => some (fun i => Fin.elim0 i)
  | _ + 1 => do
      let x ← xs 0
      let tail ← collect (fun i => xs i.succ)
      return Fin.cases x tail

def namedSort (scope : Scope) (s : String) : Bool :=
  scope.sorts.any (fun d => d.2 == s)

/-- Elaborate to an expected intrinsic sort. Alias arguments are first elaborated
in the caller environment, then installed as typed bindings in a fresh alias
parameter environment. A binder weakens these arguments, preventing capture.
Fuel rejects cyclic aliases; fuel exhaustion never supplies a partial pattern. -/
def elaborate (scope : Scope) : Nat → {k : Nat} → {Γ : Fin k → String} →
    List (Binding scope.signature Γ) → (s : String) → RawPattern →
    Option (FirstOrder.Pattern scope.signature Γ s)
  | 0, _, _, _, _, _ => none
  | _ + 1, _, _, vs, s, .variable name actual =>
      if actual = s && namedSort scope s then lookupVariable vs name s else none
  | _ + 1, _, _, _, s, .top actual =>
      if actual = s && namedSort scope s then some .top else none
  | _ + 1, _, _, _, s, .bottom actual =>
      if actual = s && namedSort scope s then some .bottom else none
  | n + 1, _, _, vs, s, .not actual p => do
      if actual ≠ s then none else return .not (← elaborate scope n vs s p)
  | n + 1, _, _, vs, s, .and actual p q => do
      if actual ≠ s then none else
        return .and (← elaborate scope n vs s p) (← elaborate scope n vs s q)
  | n + 1, _, _, vs, s, .or actual p q => do
      if actual ≠ s then none else
        return .or (← elaborate scope n vs s p) (← elaborate scope n vs s q)
  | n + 1, _, _, vs, s, .implies actual p q => do
      if actual ≠ s then none else
        return .implies (← elaborate scope n vs s p) (← elaborate scope n vs s q)
  | n + 1, _, _, vs, s, .iff actual p q => do
      if actual ≠ s then none else
        return .iff (← elaborate scope n vs s p) (← elaborate scope n vs s q)
  | n + 1, _, _, vs, s, .exists actual name b p => do
      if actual ≠ s || !namedSort scope b then none else
        return .exists b (← elaborate scope n (bind name b vs) s p)
  | n + 1, _, _, vs, s, .forall actual name b p => do
      if actual ≠ s || !namedSort scope b then none else
        return .forall b (← elaborate scope n (bind name b vs) s p)
  | n + 1, _, Γ, vs, s, .app name args => do
      match scope.symbols.attach.find? (fun d => d.val.declaration.name == name) with
      | some d =>
          if h : d.val.declaration.result = s then
            if len : args.length = d.val.declaration.arguments.length then do
              let ps ← collect (fun i : Fin d.val.declaration.arguments.length =>
                elaborate scope n vs (d.val.declaration.arguments.get i)
                  (args.get ⟨i.val, by omega⟩))
              return .app ⟨d.val, d.property, by simp, h⟩ ps
            else none
          else none
      | none => do
          let a ← scope.aliases.find? (fun a => a.declaration.symbol.name == name)
          let d := a.declaration
          if d.symbol.result ≠ s || args.length ≠ d.parameters.length then none else do
            let ps ← (d.parameters.zip args).mapM (fun (formal, arg) => do
              let p ← elaborate scope n vs formal.2 arg
              pure ⟨formal.1, formal.2, p⟩)
            elaborate scope n ps s d.body

/-- The explicit sort annotation/result profile of a source pattern. -/
def resultSort (scope : Scope) : RawPattern → Option String
  | .variable _ s | .top s | .bottom s | .not s _ | .and s _ _ | .or s _ _
    | .implies s _ _ | .iff s _ _ | .exists s _ _ _ | .forall s _ _ _ => some s
  | .app name _ =>
      match scope.symbols.find? (fun d => d.declaration.name == name) with
      | some d => some d.declaration.result
      | none => (scope.aliases.find? (fun d => d.declaration.symbol.name == name)).map
          (fun d => d.declaration.symbol.result)

/-- Build the complete free-variable context, respecting bound-name shadowing. -/
def freeVariables (bound : List String) : Nat → RawPattern → Option (List (String × String))
  | 0, _ => none
  | _ + 1, .variable n s => some (if n ∈ bound then [] else [(n, s)])
  | n + 1, .app _ args => (args.mapM (freeVariables bound n)).map List.flatten
  | _ + 1, .top _ | _ + 1, .bottom _ => some []
  | n + 1, .not _ p => freeVariables bound n p
  | n + 1, .and _ p q | n + 1, .or _ p q | n + 1, .implies _ p q | n + 1, .iff _ p q => do
      return (← freeVariables bound n p) ++ (← freeVariables bound n q)
  | n + 1, .exists _ name _ p | n + 1, .forall _ name _ p => freeVariables (name :: bound) n p

/-- Universally close free element variables, as the existing FO institution does.
Conflicting occurrences of one free name at distinct sorts are rejected. -/
def sentence (scope : Scope) (fuel : Nat) (p : RawPattern) :
    Option (FirstOrder.Sentence scope.signature) := do
  let vars ← freeVariables [] fuel p
  let vars := vars.eraseDups
  if !(vars.map Prod.fst).Nodup then none else do
    let s ← resultSort scope p
    let Γ := fun i : Fin vars.length => (vars.get i).2
    let vs : List (Binding scope.signature Γ) :=
      (List.finRange vars.length).map (fun i => ⟨(vars.get i).1, Γ i, .evar i⟩)
    let body ← elaborate scope fuel vs s p
    return ⟨vars.length, Γ, s, body⟩
end Checking
end Silmaril.Logic.Kore.Modules
