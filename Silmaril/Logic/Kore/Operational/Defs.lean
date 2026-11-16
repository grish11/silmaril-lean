module

public import Silmaril.Logic.Reachability.Thms

/-! A constructor/operational slice of the pinned emitted KORE TEST.CD rule.
Input is a parsed tree, not KORE text. Claims are never used as transition axioms.
Only the explicitly checked configuration profile is accepted. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.Operational

/-- Untrusted parsed syntax. Unknown forms are retained and rejected. -/
inductive Raw where
  | app0 (name : String) (sortArguments : List String)
  | app1 (name : String) (sortArguments : List String) (argument : Raw)
  | app2 (name : String) (sortArguments : List String) (first second : Raw)
  | variable (name sort : String)
  | stringLiteral (value : String)
  | domainValue (sort value : String)
  | top (sort : String)
  | and (sort : String) (left right : Raw)
  | rewrites (sort : String) (left right : Raw)
  | equals (operandSort resultSort : String) (left right : Raw)
  | next (sort : String) (body : Raw)
  | unsupported (name : String)
  deriving DecidableEq, Repr

def commaJoin : List (List Char) → List Char
  | [] => []
  | [s] => s
  | s :: ss => s ++ [','] ++ commaJoin ss

def quoted (value : String) : List Char :=
  ['"'] ++ value.toList.flatMap (fun c =>
    if c = '"' then ['\\', '"'] else
    if c = '\\' then ['\\', '\\'] else
    if c = '\n' then ['\\', 'n'] else
    if c = '\r' then ['\\', 'r'] else
    if c = '\t' then ['\\', 't'] else [c]) ++ ['"']

/-- Concrete KORE spelling as characters, avoiding opaque runtime formatters.
Sort names are instantiated zero-argument sorts. This is serialization, not parsing. -/
def Raw.render : Raw → List Char
  | .app0 name sorts => name.toList ++ ['{'] ++ commaJoin (sorts.map (fun s => s.toList ++ "{}".toList)) ++ "}()".toList
  | .app1 name sorts arg => name.toList ++ ['{'] ++ commaJoin (sorts.map (fun s => s.toList ++ "{}".toList)) ++ "}(".toList ++ arg.render ++ [')']
  | .app2 name sorts a b => name.toList ++ ['{'] ++ commaJoin (sorts.map (fun s => s.toList ++ "{}".toList)) ++ "}(".toList ++ a.render ++ [','] ++ b.render ++ [')']
  | .variable name sort => name.toList ++ [':'] ++ sort.toList ++ "{}".toList
  | .stringLiteral value => quoted value
  | .domainValue sort value => "\\dv{".toList ++ sort.toList ++ "{}}(".toList ++ quoted value ++ [')']
  | .top sort => "\\top{".toList ++ sort.toList ++ "{}}()".toList
  | .and sort a b => "\\and{".toList ++ sort.toList ++ "{}}(".toList ++ a.render ++ [','] ++ b.render ++ [')']
  | .rewrites sort a b => "\\rewrites{".toList ++ sort.toList ++ "{}}(".toList ++ a.render ++ [','] ++ b.render ++ [')']
  | .equals operand result a b => "\\equals{".toList ++ operand.toList ++ "{},".toList ++ result.toList ++ "{}}(".toList ++ a.render ++ [','] ++ b.render ++ [')']
  | .next sort body => "\\next{".toList ++ sort.toList ++ "{}}(".toList ++ body.render ++ [')']
  | .unsupported name => "#unsupported:".toList ++ name.toList

inductive DeclarationKind | ruleAxiom | claim deriving DecidableEq, Repr

structure Declaration where
  kind : DeclarationKind
  sortVariables : List String
  body : Raw
  /-- Every attribute must pass the explicit nonsemantic metadata whitelist. -/
  attributes : List Raw := []
  deriving DecidableEq, Repr

def Declaration.render (d : Declaration) : List Char :=
  (match d.kind with | .ruleAxiom => "axiom".toList | .claim => "claim".toList) ++
    ['{'] ++ commaJoin (d.sortVariables.map String.toList) ++ ['}'] ++ d.body.render ++
    ['['] ++ commaJoin (d.attributes.map Raw.render) ++ [']']

/-- Intrinsic source profile: a state token in the K cell with two sorted
captured variables. Both occurrences use this same context. -/
structure Context where
  tail : String
  counter : String
  deriving DecidableEq, Repr

structure ConfigPattern where
  state : String
  deriving DecidableEq, Repr

structure Rule where
  before : ConfigPattern
  after : ConfigPattern
  deriving DecidableEq, Repr

/-- The actual configuration data, independent of matching interpretation. -/
structure Config where
  code : List String
  counter : Nat
  deriving DecidableEq, Repr

structure Valuation where
  tail : List String
  counter : Nat
  deriving DecidableEq, Repr

def ConfigPattern.eval (p : ConfigPattern) (v : Valuation) : Config :=
  ⟨p.state :: v.tail, v.counter⟩

/-- Constructor names and sort instantiations are checked, including the
explicit State-to-KItem injection. This is not alias or hook evaluation. -/
def configTree (Γ : Context) (p : ConfigPattern) : Raw :=
  .and "SortGeneratedTopCell" (.top "SortGeneratedTopCell")
    (.app2 "Lbl'-LT-'generatedTop'-GT-'" []
      (.app1 "Lbl'-LT-'k'-GT-'" []
        (.app2 "kseq" []
          (.app1 "inj" ["SortState", "SortKItem"] (.domainValue "SortState" p.state))
          (.variable Γ.tail "SortK")))
      (.variable Γ.counter "SortGeneratedCounterCell"))

/-- Checked recognition of the one supported sorted constructor profile. -/
def elaborateConfig (Γ : Context) : Raw → Option ConfigPattern
  | .and "SortGeneratedTopCell" (.top "SortGeneratedTopCell")
      (.app2 "Lbl'-LT-'generatedTop'-GT-'" []
        (.app1 "Lbl'-LT-'k'-GT-'" [] (.app2 "kseq" []
          (.app1 "inj" ["SortState", "SortKItem"] (.domainValue "SortState" state))
          (.variable tail "SortK")))
        (.variable counter "SortGeneratedCounterCell")) =>
      if tail = Γ.tail ∧ counter = Γ.counter then some ⟨state⟩ else none
  | _ => none

/-- A single already-parsed alias definition; no recursive alias expansion. -/
structure Alias where
  name : String
  body : Raw
  deriving DecidableEq, Repr

def aliasApplication (Γ : Context) (a : Alias) : Raw :=
  .app2 a.name [] (.variable Γ.counter "SortGeneratedCounterCell") (.variable Γ.tail "SortK")

def Alias.render (Γ : Context) (a : Alias) : List Char :=
  "alias".toList ++ a.name.toList ++ "{}(SortGeneratedCounterCell{},SortK{}):SortGeneratedTopCell{}where".toList ++
    (aliasApplication Γ a).render ++ ":=".toList ++ a.body.render ++ "[]".toList

/-- Exact arity, instantiated sorts and argument order; expansion only after
checking the supplied alias body against the accepted constructor grammar. -/
def elaborateLeft (Γ : Context) (a : Alias) (p : Raw) : Option ConfigPattern :=
  if p = aliasApplication Γ a then elaborateConfig Γ a.body else elaborateConfig Γ p

/-- Only the five string-valued source-location/identity metadata forms in
this pinned specimen are accepted; hooks, priorities and other attributes fail. -/
def metadataOnly : Raw → Bool
  | .app1 name [] (.stringLiteral _) =>
      ["label", "org'Stop'kframework'Stop'attributes'Stop'Source",
       "org'Stop'kframework'Stop'definition'Stop'Production",
       "org'Stop'kframework'Stop'attributes'Stop'Location", "UNIQUE'Unds'ID"].contains name
  | _ => false

def elaborateRule (Γ : Context) (a : Alias) (d : Declaration) : Option Rule := do
  if d.sortVariables != [] || !d.attributes.all metadataOnly then none else
  match d.body with
  | .rewrites "SortGeneratedTopCell" lhs rhs =>
      return ⟨← elaborateLeft Γ a lhs, ← elaborateConfig Γ rhs⟩
  | _ => none

/-- Only validated axioms generate operational transitions. A claim with the
same syntactic body remains a goal and contributes no edge. -/
def transitionRule (Γ : Context) (a : Alias) (d : Declaration) : Option Rule :=
  match d.kind with
  | .ruleAxiom => elaborateRule Γ a d
  | .claim => none

structure CheckedInput where
  axioms : List Rule
  claims : List Rule
  deriving DecidableEq, Repr

/-- Fail the complete input on an unsupported declaration; never silently skip
it. Keep claims separate from the rules that generate execution. -/
def checkInput (Γ : Context) (a : Alias) : List Declaration → Option CheckedInput
  | [] => some ⟨[], []⟩
  | d :: ds => do
      let r ← elaborateRule Γ a d
      let checked ← checkInput Γ a ds
      match d.kind with
      | .ruleAxiom => return ⟨r :: checked.axioms, checked.claims⟩
      | .claim => return ⟨checked.axioms, r :: checked.claims⟩

inductive Step (rules : List Rule) : Config → Config → Prop where
  | rule (r : Rule) (member : r ∈ rules) (v : Valuation) :
      Step rules (r.before.eval v) (r.after.eval v)

/-- Independent one-path-next denotation, with predecessor orientation. -/
def nextDenote (R : Config → Config → Prop) (Q : Set Config) : Set Config :=
  {c | ∃ d, R c d ∧ d ∈ Q}

def Rule.Holds (R : Config → Config → Prop) (r : Rule) : Prop :=
  ∀ v, r.before.eval v ∈ nextDenote R {r.after.eval v}

/-- Actual six-sort native signature; constructor interpretations are not
opaque truth labels. -/
inductive KSort | state | item | code | cell | counter | config deriving DecidableEq

inductive Operation : (n : Nat) → (Fin n → KSort) → KSort → Type
  | token (value : String) : Operation 0 Fin.elim0 .state
  | injection : Operation 1 (fun _ => .state) .item
  | sequence : Operation 2 (fun i => if i = 0 then .item else .code) .code
  | kcell : Operation 1 (fun _ => .code) .cell
  | topcell : Operation 2 (fun i => if i = 0 then .cell else .counter) .config
  | step : Operation 1 (fun _ => .config) .config

def signature : Reachability.Signature KSort.config := ⟨⟨Operation⟩, .step⟩

def Carrier : KSort → Type
  | .state | .item => String
  | .code | .cell => List String
  | .counter => Nat
  | .config => Config

def model (R : Config → Config → Prop) : Reachability.Model KSort.config signature where
  carrier := Carrier
  nonempty := fun s => by
    cases s
    · exact ⟨""⟩
    · exact ⟨""⟩
    · exact ⟨[]⟩
    · exact ⟨[]⟩
    · exact ⟨(0 : Nat)⟩
    · exact ⟨⟨[], 0⟩⟩
  operation := fun op => match op with
    | .token s => fun _ => {s}
    | .injection => fun v => {v 0}
    | .sequence => fun v => {v 0 :: v 1}
    | .kcell => fun v => {v 0}
    | .topcell => fun v => {⟨v 0, v 1⟩}
    | .step => fun v => {c | R c (v 0)}

def context : Fin 2 → KSort := fun i => if i = 0 then .code else .counter

def valuation (v : Valuation) : (i : Fin 2) → Carrier (context i) :=
  fun i => if h : i = 0 then by subst i; exact v.tail else by
    have hi : i = 1 := by omega
    subst i
    exact v.counter

def tokenPattern (s : String) : Matching.FirstOrder.Pattern signature.algebra context .state :=
  .app (.token s) (fun i => i.elim0)

def itemPattern (s : String) : Matching.FirstOrder.Pattern signature.algebra context .item :=
  .app .injection (fun _ => tokenPattern s)

def codePattern (s : String) : Matching.FirstOrder.Pattern signature.algebra context .code :=
  .app .sequence (fun i => if h : i = 0 then by
    subst i; exact itemPattern s
  else by
    have hi : i = 1 := by omega
    subst i; exact .var 0)

def cellPattern (s : String) : Matching.FirstOrder.Pattern signature.algebra context .cell :=
  .app .kcell (fun _ => codePattern s)

/-- Structural constructor compilation; the captured variables remain native
matching variables, including the unchanged counter and arbitrary K tail. -/
def ConfigPattern.compile (p : ConfigPattern) :
    Matching.FirstOrder.Pattern signature.algebra context .config :=
  .app .topcell (fun i => if h : i = 0 then by
    subst i; exact cellPattern p.state
  else by
    have hi : i = 1 := by omega
    subst i; exact .var 1)

/-- One-step source rewrite represented by actual predecessor application. -/
def Rule.nextPattern (r : Rule) :
    Matching.FirstOrder.Pattern signature.algebra context .config :=
  .neg (.conj r.before.compile (.neg (.app .step (fun _ => r.after.compile))))

def Rule.nextSentence (r : Rule) : Matching.FirstOrder.Sentence signature.algebra :=
  ⟨2, context, .config, r.nextPattern⟩

def Rule.compile (r : Rule) : Reachability.Sentence KSort.config signature :=
  ⟨2, context, .finite, r.before.compile, r.after.compile⟩

end Silmaril.Logic.Kore.Operational
