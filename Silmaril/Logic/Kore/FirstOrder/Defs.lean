module

public import Silmaril.Logic.Matching.FirstOrder.Thms

/-! A sorted, elaborated first-order fragment of the KORE pattern grammar.
Sort parameters have already been instantiated, and named element variables have
been resolved to sorted de Bruijn indices. Conjunction and disjunction cover the
binary instances of the backend's variadic grammar. See the pinned source record
`papers/works/kore-first-order-fragment/`; this is not the whole K language. -/
@[expose] public section
namespace Silmaril.Logic.Kore.FirstOrder
open CategoryTheory
open Algebraic.ManySorted (Signature)
variable {S : Type} (A : Signature S)

/-- A separate source AST, including KORE connectives absent from the target core. -/
inductive Pattern : {k : Nat} → (Fin k → S) → S → Type where
  | evar {k : Nat} {Γ : Fin k → S} (i : Fin k) : Pattern Γ (Γ i)
  | app {k : Nat} {Γ : Fin k → S} {n : Nat} {inputs : Fin n → S} {output : S}
      (symbol : A.operations n inputs output)
      (args : (i : Fin n) → Pattern Γ (inputs i)) : Pattern Γ output
  | top {k : Nat} {Γ : Fin k → S} {s : S} : Pattern Γ s
  | bottom {k : Nat} {Γ : Fin k → S} {s : S} : Pattern Γ s
  | not {k : Nat} {Γ : Fin k → S} {s : S} (p : Pattern Γ s) : Pattern Γ s
  | and {k : Nat} {Γ : Fin k → S} {s : S} (p q : Pattern Γ s) : Pattern Γ s
  | or {k : Nat} {Γ : Fin k → S} {s : S} (p q : Pattern Γ s) : Pattern Γ s
  | implies {k : Nat} {Γ : Fin k → S} {s : S} (p q : Pattern Γ s) : Pattern Γ s
  | iff {k : Nat} {Γ : Fin k → S} {s : S} (p q : Pattern Γ s) : Pattern Γ s
  | exists {k : Nat} {Γ : Fin k → S} {s : S} (bound : S)
      (body : Pattern (Fin.cases bound Γ) s) : Pattern Γ s
  | forall {k : Nat} {Γ : Fin k → S} {s : S} (bound : S)
      (body : Pattern (Fin.cases bound Γ) s) : Pattern Γ s

/-- Independent set interpretation over the existing arbitrary-set-valued models.
In particular, universal binding is interpreted directly, without calling lowering. -/
def denote (M : Matching.FirstOrder.Model A) {k : Nat} {Γ : Fin k → S} {s : S}
    (v : (i : Fin k) → M.carrier (Γ i)) : Pattern A Γ s → Set (M.carrier s)
  | .evar i => {v i}
  | .app symbol args => {result | ∃ values,
      (∀ i, values i ∈ denote M v (args i)) ∧ result ∈ M.operation symbol values}
  | .top => Set.univ
  | .bottom => ∅
  | .not p => (denote M v p)ᶜ
  | .and p q => denote M v p ∩ denote M v q
  | .or p q => denote M v p ∪ denote M v q
  | .implies p q => {result | result ∈ denote M v p → result ∈ denote M v q}
  | .iff p q => {result | result ∈ denote M v p ↔ result ∈ denote M v q}
  | .exists bound body => {result | ∃ value : M.carrier bound,
      result ∈ denote M (Fin.cases value v) body}
  | .forall bound body => {result | ∀ value : M.carrier bound,
      result ∈ denote M (Fin.cases value v) body}

namespace Pattern
variable {A} {B : Signature S}
/-- Explicit expansion into the 2017 first-order matching primitives. -/
def lower {k : Nat} {Γ : Fin k → S} {s : S} :
    Pattern A Γ s → Matching.FirstOrder.Pattern A Γ s
  | .evar i => .var i
  | .app symbol args => .app symbol (fun i => lower (args i))
  | .top => Matching.FirstOrder.Pattern.top
  | .bottom => Matching.FirstOrder.Pattern.bottom
  | .not p => .neg (lower p)
  | .and p q => .conj (lower p) (lower q)
  | .or p q => .neg (.conj (.neg (lower p)) (.neg (lower q)))
  | .implies p q => .neg (.conj (lower p) (.neg (lower q)))
  | .iff p q => .conj (.neg (.conj (lower p) (.neg (lower q))))
      (.neg (.conj (lower q) (.neg (lower p))))
  | .exists bound body => .ex bound (lower body)
  | .forall bound body => .neg (.ex bound (.neg (lower body)))

/-- Rename symbols while keeping the fixed sort set and element context. -/
def map (f : A ⟶ B) {k : Nat} {Γ : Fin k → S} {s : S} : Pattern A Γ s → Pattern B Γ s
  | .evar i => .evar i
  | .app symbol args => .app (f.operations symbol) (fun i => map f (args i))
  | .top => .top
  | .bottom => .bottom
  | .not p => .not (map f p)
  | .and p q => .and (map f p) (map f q)
  | .or p q => .or (map f p) (map f q)
  | .implies p q => .implies (map f p) (map f q)
  | .iff p q => .iff (map f p) (map f q)
  | .exists bound body => .exists bound (map f body)
  | .forall bound body => .forall bound (map f body)
end Pattern

/-- A finite-context pattern, universally closed for validity as in matching logic.
This does not represent KORE module declarations or the axiom/claim distinction. -/
structure Sentence where
  variableCount : Nat
  context : Fin variableCount → S
  sort : S
  pattern : Pattern A context sort

namespace Sentence
variable {A} {B : Signature S}
def lower (p : Sentence A) : Matching.FirstOrder.Sentence A :=
  ⟨p.variableCount, p.context, p.sort, p.pattern.lower⟩
def map (f : A ⟶ B) (p : Sentence A) : Sentence B :=
  ⟨p.variableCount, p.context, p.sort, p.pattern.map f⟩
def Satisfies (M : Matching.FirstOrder.Model A) (p : Sentence A) : Prop :=
  ∀ v : (i : Fin p.variableCount) → M.carrier (p.context i),
    ∀ result : M.carrier p.sort, result ∈ denote A M v p.pattern
end Sentence
end Silmaril.Logic.Kore.FirstOrder
