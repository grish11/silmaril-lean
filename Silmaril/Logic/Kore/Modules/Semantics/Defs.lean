module

public import Silmaril.Logic.Kore.Modules.Checking.Thms

/-! Independent set semantics of the accepted named monomorphic raw language.
This interpretation never calls the elaborator or typed pattern denotation.
Fuel bounds recursive alias unfolding as well as source syntax traversal. -/
@[expose] public section
namespace Silmaril.Logic.Kore.Modules.Semantics
variable {scope : Scope} (M : Matching.FirstOrder.Model scope.signature)

abbrev Binding := String × (s : String) × Set (M.carrier s)
abbrev Environment := List (Binding M)

def lookup (ρ : Environment M) (name s : String) : Set (M.carrier s) :=
  match ρ.find? (fun entry => entry.1 == name) with
  | none => ∅
  | some entry => if h : entry.2.1 = s then h ▸ entry.2.2 else ∅

/-- Direct set interpretation: logical operations and quantifiers act on sets;
symbols use the actual model operation graph. Alias actuals are evaluated in the
caller environment and installed simultaneously in a fresh formal environment.
Invalid lookups/profiles and exhausted fuel denote the empty set. -/
def denote : Nat → Environment M → (s : String) → RawPattern → Set (M.carrier s)
  | 0, _, _, _ => ∅
  | _ + 1, ρ, s, .variable name actual =>
      if actual = s && Checking.namedSort scope s then lookup M ρ name s else ∅
  | _ + 1, _, s, .top actual =>
      if actual = s && Checking.namedSort scope s then Set.univ else ∅
  | _ + 1, _, s, .bottom actual =>
      if actual = s && Checking.namedSort scope s then ∅ else ∅
  | n + 1, ρ, s, .not actual p =>
      if actual ≠ s then ∅ else (denote n ρ s p)ᶜ
  | n + 1, ρ, s, .and actual p q =>
      if actual ≠ s then ∅ else denote n ρ s p ∩ denote n ρ s q
  | n + 1, ρ, s, .or actual p q =>
      if actual ≠ s then ∅ else denote n ρ s p ∪ denote n ρ s q
  | n + 1, ρ, s, .implies actual p q =>
      if actual ≠ s then ∅ else {result | result ∈ denote n ρ s p → result ∈ denote n ρ s q}
  | n + 1, ρ, s, .iff actual p q =>
      if actual ≠ s then ∅ else {result | result ∈ denote n ρ s p ↔ result ∈ denote n ρ s q}
  | n + 1, ρ, s, .exists actual name b p =>
      if actual ≠ s || !Checking.namedSort scope b then ∅ else
        {result | ∃ x : M.carrier b, result ∈ denote n (⟨name, b, {x}⟩ :: ρ) s p}
  | n + 1, ρ, s, .forall actual name b p =>
      if actual ≠ s || !Checking.namedSort scope b then ∅ else
        {result | ∀ x : M.carrier b, result ∈ denote n (⟨name, b, {x}⟩ :: ρ) s p}
  | n + 1, ρ, s, .app name args =>
      match scope.symbols.attach.find? (fun d => d.val.declaration.name == name) with
      | some d =>
          if h : d.val.declaration.result = s then
            if len : args.length = d.val.declaration.arguments.length then
              {result | ∃ values : (i : Fin d.val.declaration.arguments.length) →
                  M.carrier (d.val.declaration.arguments.get i),
                (∀ i, values i ∈ denote n ρ (d.val.declaration.arguments.get i)
                  (args.get ⟨i.val, by omega⟩)) ∧
                result ∈ M.operation ⟨d.val, d.property, by simp, h⟩ values}
            else ∅
          else ∅
      | none =>
          match scope.aliases.find? (fun a => a.declaration.symbol.name == name) with
          | none => ∅
          | some a =>
              let d := a.declaration
              if d.symbol.result ≠ s || args.length ≠ d.parameters.length then ∅ else
                let formals := (d.parameters.zip args).map (fun (formal, arg) =>
                  (⟨formal.1, formal.2, denote n ρ formal.2 arg⟩ : Binding M))
                denote n formals s d.body

/-- Relate typed environments to direct named environments. The raw interpreter
above neither uses this bridge nor refers to any typed pattern. -/
def interpret {k : Nat} {Γ : Fin k → String}
    (vs : List (Checking.Binding scope.signature Γ))
    (v : (i : Fin k) → M.carrier (Γ i)) : Environment M :=
  vs.map (fun entry => ⟨entry.1, entry.2.1, FirstOrder.denote scope.signature M v entry.2.2⟩)
/-- A direct valuation assigns a carrier element to each named free-variable
occurrence in the canonical deduplicated source context. -/
abbrev Valuation (names : List (String × String)) :=
  (i : Fin names.length) → M.carrier (names.get i).2

def initial (names : List (String × String)) (v : Valuation M names) : Environment M :=
  (List.finRange names.length).map
    (fun i => ⟨(names.get i).1, (names.get i).2, {v i}⟩)

/-- Independent raw global validity: require source context/sort metadata to
exist, then quantify over all source valuations and all result elements.
Acceptance is not part of this definition and no typed pattern is inspected. -/
def Satisfies (fuel : Nat) (raw : RawPattern) : Prop :=
  ∃ names s, Checking.freeVariables [] fuel raw = some names ∧
    Checking.resultSort scope raw = some s ∧
    ∀ v : Valuation M names.eraseDups, ∀ result : M.carrier s,
      result ∈ denote M fuel (initial M names.eraseDups v) s raw

end Silmaril.Logic.Kore.Modules.Semantics
