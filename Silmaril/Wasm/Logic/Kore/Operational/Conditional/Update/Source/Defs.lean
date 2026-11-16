module

public import Silmaril.Wasm.Logic.Kore.Operational.Conditional.Update.Thms

/-! Independent named-variable semantics for the selected raw KORE constructors.
Undefined syntax is none; a defined empty pattern is some ∅. Rewriting is an
outer declaration relation, distinct from pattern equality and next. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source

abbrev Environment := (s : KSort) → String → Carrier s

def sortName : KSort → String
  | .state => "SortState"
  | .item => "SortKItem"
  | .code => "SortK"
  | .kcell => "SortKCell"
  | .integer => "SortInt"
  | .boolean => "SortBool"
  | .valcell => "SortValCell"
  | .tcell => "SortTCell"
  | .counter => "SortGeneratedCounterCell"
  | .config => "SortGeneratedTopCell"

def image₂ {A B C : Type} (f : A → B → C) (a : Set A) (b : Set B) : Set C :=
  {z | ∃ x ∈ a, ∃ y ∈ b, z = f x y}

/-- Sort-checked structural interpretation, independent of Rule and elaborate.
Both children must be defined before conjunction or equality has a meaning. -/
def denote (ρ : Environment) : Raw → (s : KSort) → Option (Set (Carrier s))
  | .variable name tag, s =>
      if tag = sortName s then some {ρ s name} else none
  | .domainValue tag text, s => match s, tag with
      | .state, "SortState" => some {text}
      | .integer, "SortInt" => text.toInt?.map (fun n => {n})
      | .boolean, "SortBool" =>
          if text = "true" then some {true}
          else if text = "false" then some {false} else none
      | _, _ => none
  | .top tag, s => if tag = sortName s then some Set.univ else none
  | .and tag a b, s => do
      if tag ≠ sortName s then none else do
        let x ← denote ρ a s
        let y ← denote ρ b s
        return x ∩ y
  | .app1 name sorts a, s => match s, name, sorts with
      | .item, "inj", ["SortState", "SortKItem"] => denote ρ a .state
      | .kcell, "Lbl'-LT-'k'-GT-'", [] => denote ρ a .code
      | .valcell, "Lbl'-LT-'val'-GT-'", [] => denote ρ a .integer
      | .counter, "Lbl'-LT-'generatedCounter'-GT-'", [] => denote ρ a .integer
      | .boolean, "LblnotBool'Unds'", [] =>
          (denote ρ a .boolean).map (Set.image (fun x => !x))
      | _, _, _ => none
  | .app2 name sorts a b, s => match s, name, sorts with
      | .code, "kseq", [] => do
          let x ← denote ρ a .item
          let y ← denote ρ b .code
          return image₂ List.cons x y
      | .tcell, "Lbl'-LT-'T'-GT-'", [] => do
          let x ← denote ρ a .kcell
          let y ← denote ρ b .valcell
          return image₂ Prod.mk x y
      | .config, "Lbl'-LT-'generatedTop'-GT-'", [] => do
          let x ← denote ρ a .tcell
          let y ← denote ρ b .counter
          return image₂ (fun t n => (⟨t.1, t.2, n⟩ : Config)) x y
      | .boolean, "Lbl'UndsEqlsEqls'Int'Unds'", [] => do
          let x ← denote ρ a .integer
          let y ← denote ρ b .integer
          return image₂ intEqual x y
      | _, _, _ => none
  | .equals "SortBool" "SortGeneratedTopCell" a b, .config => do
      let x ← denote ρ a .boolean
      let y ← denote ρ b .boolean
      return { _c | x = y }
  | _, _ => none

/-- A real source transition witnesses a single named-variable assignment shared
by the original left and right trees. Claims never supply transitions. -/
def RawStep (ds : List Declaration) (c d : Config) : Prop :=
  ∃ decl ∈ ds, decl.kind = .ruleAxiom ∧
    ∃ (ρ : Environment) (lhs rhs : Raw) (left right : Set Config),
      decl.body = .rewrites "SortGeneratedTopCell" lhs rhs ∧
      denote ρ lhs .config = some left ∧ denote ρ rhs .config = some right ∧
      c ∈ left ∧ d ∈ right

def decode (Γ : Context) (ρ : Environment) : Valuation :=
  ⟨ρ .code Γ.tail, ρ .integer Γ.x, ρ .valcell Γ.capturedVal, ρ .counter Γ.counter⟩

/-- Extend the four actual captures to a total sorted named assignment. -/
def encode (Γ : Context) (v : Valuation) : Environment := fun s name =>
  match s with
  | .code => if name = Γ.tail then v.tail else []
  | .integer => if name = Γ.x then v.x else 0
  | .valcell => if name = Γ.capturedVal then v.capturedVal else 0
  | .counter => if name = Γ.counter then v.counter else 0
  | .state | .item => ""
  | .kcell => []
  | .boolean => false
  | .tcell => ([], 0)
  | .config => ⟨[], 0, 0⟩

/-- Successful parsing of the literal is a lexical property of the checked raw
AST, derived below from the actual elaborator, rather than a semantic premise. -/
def LiteralReads (r : Rule) : Prop := (toString r.literal).toInt? = some r.literal

def leftTree (Γ : Context) (r : Rule) : Raw :=
  .and "SortGeneratedTopCell" (configTree Γ r.before true) (guardTree Γ r.guard)

def rightTree (Γ : Context) (r : Rule) : Raw :=
  .and "SortGeneratedTopCell" (r.rhsTree Γ) (.top "SortGeneratedTopCell")


end Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source
