module

public import Silmaril.Logic.Kore.Operational.Text.Defs

/-! The actual conditional TEST.AB/AC emitted profile, separate from CD.
Integer hooks have explicit total singleton interpretations. Source as-pattern
bindings remain distinct and their equality is an operational premise. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.Operational.Conditional

inductive Guard | zero | nonzero deriving DecidableEq, Repr

/-- Total interpretation selected for the pinned INT.eq hooked symbol. -/
def intEqual (x y : Int) : Bool := decide (x = y)

def Guard.eval : Guard → Int → Bool
  | .zero, x => intEqual x 0
  | .nonzero, x => !(intEqual x 0)

/-- Explicit semantics of the emitted Boolean equality-to-true guard. -/
def Guard.Holds (g : Guard) (x : Int) : Prop := g.eval x = true

structure Rule where
  before : String
  after : String
  guard : Guard
  deriving DecidableEq, Repr

/-- The generated counter is an Int cell, independent of the val cell. -/
structure Config where
  code : List String
  val : Int
  counter : Int
  deriving DecidableEq, Repr

structure Valuation where
  tail : List String
  x : Int
  capturedVal : Int
  counter : Int
  deriving DecidableEq, Repr

def Rule.beforeConfig (r : Rule) (v : Valuation) : Config :=
  ⟨r.before :: v.tail, v.x, v.counter⟩

def Rule.afterConfig (r : Rule) (v : Valuation) : Config :=
  ⟨r.after :: v.tail, v.capturedVal, v.counter⟩

/-- Independent guarded operational relation; no matching-satisfaction premise. -/
inductive Step (rules : List Rule) : Config → Config → Prop where
  | rule (r : Rule) (member : r ∈ rules) (v : Valuation)
      (coherent : v.x = v.capturedVal) (enabled : r.guard.Holds v.x) :
      Step rules (r.beforeConfig v) (r.afterConfig v)

/-- All four actual source captures, with distinct names checked by elaboration. -/
structure Context where
  tail : String
  x : String
  capturedVal : String
  counter : String
  deriving DecidableEq, Repr

def Context.distinct (Γ : Context) : Bool :=
  Γ.tail != Γ.x && Γ.tail != Γ.capturedVal && Γ.tail != Γ.counter &&
  Γ.x != Γ.capturedVal && Γ.x != Γ.counter && Γ.capturedVal != Γ.counter

def intEquality (Γ : Context) : Raw :=
  .app2 "Lbl'UndsEqlsEqls'Int'Unds'" [] (.variable Γ.x "SortInt") (.domainValue "SortInt" "0")

def guardTree (Γ : Context) (g : Guard) : Raw :=
  .equals "SortBool" "SortGeneratedTopCell"
    (match g with
     | .zero => intEquality Γ
     | .nonzero => .app1 "LblnotBool'Unds'" [] (intEquality Γ))
    (.domainValue "SortBool" "true")

def valueTree (Γ : Context) (lhs : Bool) : Raw :=
  if lhs then .and "SortValCell"
    (.app1 "Lbl'-LT-'val'-GT-'" [] (.variable Γ.x "SortInt"))
    (.variable Γ.capturedVal "SortValCell")
  else .variable Γ.capturedVal "SortValCell"

def configTree (Γ : Context) (state : String) (lhs : Bool) : Raw :=
  .app2 "Lbl'-LT-'generatedTop'-GT-'" []
    (.app2 "Lbl'-LT-'T'-GT-'" []
      (.app1 "Lbl'-LT-'k'-GT-'" []
        (.app2 "kseq" []
          (.app1 "inj" ["SortState", "SortKItem"] (.domainValue "SortState" state))
          (.variable Γ.tail "SortK")))
      (valueTree Γ lhs))
    (.variable Γ.counter "SortGeneratedCounterCell")

def Rule.tree (r : Rule) (Γ : Context) : Raw :=
  .rewrites "SortGeneratedTopCell"
    (.and "SortGeneratedTopCell" (configTree Γ r.before true) (guardTree Γ r.guard))
    (.and "SortGeneratedTopCell" (configTree Γ r.after false) (.top "SortGeneratedTopCell"))

/-- Recover names and endpoints, then check the entire exact profile tree.
No unsupported sort, capture, hook, attribute or extra subtree is skipped. -/
def elaborate (d : Declaration) : Option (Context × Rule) := do
  if d.sortVariables != [] || !d.attributes.all metadataOnly then none else
  match d.body with
  | .rewrites "SortGeneratedTopCell"
      (.and "SortGeneratedTopCell"
        (.app2 _ _ (.app2 _ _
          (.app1 _ _ (.app2 _ _ (.app1 _ _ (.domainValue _ before)) (.variable tail _)))
          (.and _ (.app1 _ _ (.variable x _)) (.variable captured _))) (.variable counter _)) guard)
      (.and _ (.app2 _ _ (.app2 _ _
        (.app1 _ _ (.app2 _ _ (.app1 _ _ (.domainValue _ after)) _)) _) _) _) =>
      let Γ : Context := ⟨tail, x, captured, counter⟩
      if !Γ.distinct then none else
      let g ← if guard = guardTree Γ .zero then some Guard.zero
        else if guard = guardTree Γ .nonzero then some Guard.nonzero else none
      let r : Rule := ⟨before, after, g⟩
      if d.body = r.tree Γ then some (Γ, r) else none
  | _ => none

structure CheckedProgram where
  declarations : List Declaration
  checked : List (Context × Rule)
  deriving DecidableEq, Repr

def CheckedProgram.axioms (p : CheckedProgram) : List Rule :=
  p.declarations.filterMap fun d =>
    if d.kind = .ruleAxiom then (elaborate d).map Prod.snd else none

/-- Complete declaration-only text profile: these emitted rules have no alias. -/
def check (input : String) : Option CheckedProgram := do
  let tokens ← Text.tokenize input
  let ds ← Text.declarations (tokens.length + 1) tokens
  let checked ← ds.mapM elaborate
  return ⟨ds, checked⟩

inductive KSort | state | item | code | kcell | integer | boolean | valcell | tcell | counter | config
  deriving DecidableEq

inductive Operation : (n : Nat) → (Fin n → KSort) → KSort → Type
  | token (s : String) : Operation 0 Fin.elim0 .state
  | intValue (x : Int) : Operation 0 Fin.elim0 .integer
  | boolValue (b : Bool) : Operation 0 Fin.elim0 .boolean
  | injection : Operation 1 (fun _ => .state) .item
  | sequence : Operation 2 (Fin.cases .item (fun _ => .code)) .code
  | kcell : Operation 1 (fun _ => .code) .kcell
  | valcell : Operation 1 (fun _ => .integer) .valcell
  | tcell : Operation 2 (Fin.cases .kcell (fun _ => .valcell)) .tcell
  | topcell : Operation 2 (Fin.cases .tcell (fun _ => .counter)) .config
  | intEq : Operation 2 (Fin.cases .integer (fun _ => .integer)) .boolean
  | boolNot : Operation 1 (fun _ => .boolean) .boolean
  /-- Universal definedness, not a stored truth assertion. -/
  | ceil : Operation 1 (fun _ => .boolean) .config
  | step : Operation 1 (fun _ => .config) .config

abbrev signature : Reachability.Signature KSort.config := ⟨⟨Operation⟩, .step⟩

abbrev Carrier : KSort → Type
  | .state | .item => String
  | .code | .kcell => List String
  | .integer | .valcell | .counter => Int
  | .boolean => Bool
  | .tcell => List String × Int
  | .config => Config

abbrev model (R : Config → Config → Prop) : Reachability.Model KSort.config signature where
  carrier := Carrier
  nonempty := fun s => by
    cases s
    · exact ⟨""⟩
    · exact ⟨""⟩
    · exact ⟨[]⟩
    · exact ⟨[]⟩
    · exact ⟨(0 : Int)⟩
    · exact ⟨false⟩
    · exact ⟨(0 : Int)⟩
    · exact ⟨([], 0)⟩
    · exact ⟨(0 : Int)⟩
    · exact ⟨⟨[], 0, 0⟩⟩
  operation := fun op => match op with
    | .token s => fun _ => {s}
    | .intValue x => fun _ => {x}
    | .boolValue b => fun _ => {b}
    | .injection => fun v => {v 0}
    | .sequence => fun v => {v 0 :: v 1}
    | .kcell => fun v => {v 0}
    | .valcell => fun v => {v 0}
    | .tcell => fun v => {(v 0, v 1)}
    | .topcell => fun v => {⟨(v 0).1, (v 0).2, v 1⟩}
    | .intEq => fun v => {intEqual (v 0) (v 1)}
    | .boolNot => fun v => {!v 0}
    | .ceil => fun _ => Set.univ
    | .step => fun v => {c | R c (v 0)}

abbrev context (i : Fin 4) : KSort :=
  match i.val with
  | 0 => .code
  | 1 => .integer
  | 2 => .valcell
  | _ => .counter

abbrev Pattern (s : KSort) := Matching.FirstOrder.Pattern signature.algebra context s

def unary {a b : KSort} (op : Operation 1 (fun _ => a) b) (p : Pattern a) : Pattern b :=
  .app op (fun _ => p)

def binary {a b c : KSort} (op : Operation 2 (Fin.cases a (fun _ => b)) c)
    (p : Pattern a) (q : Pattern b) : Pattern c :=
  .app op (Fin.cases p (fun _ => q))

def constant {s : KSort} (op : Operation 0 Fin.elim0 s) : Pattern s :=
  .app op (fun i => i.elim0)

def statePattern (s : String) : Pattern .code :=
  binary .sequence (unary .injection (constant (.token s))) (.var 0)

def valuePattern (lhs : Bool) : Pattern .valcell :=
  match lhs with
  | true => .conj (unary .valcell (.var 1)) (.var 2)
  | false => .var 2

def configPattern (s : String) (lhs : Bool) : Pattern .config :=
  binary .topcell (binary .tcell (unary .kcell (statePattern s)) (valuePattern lhs)) (.var 3)

/-- Direct native interpretation of the source INT.eq and BOOL.not hooks. -/
def Guard.boolPattern (g : Guard) : Pattern .boolean :=
  let eq : Pattern .boolean := binary .intEq (.var 1) (constant (.intValue 0))
  match g with
  | .zero => eq
  | .nonzero => unary .boolNot eq

/-- For singleton Boolean guard results, source equals-to-true is definedness
of the intersection with true. This is not an encoding of arbitrary set equality. -/
def Guard.compile (g : Guard) : Pattern .config :=
  unary .ceil (.conj g.boolPattern (constant (.boolValue true)))

def Rule.pre (r : Rule) : Pattern .config := .conj (configPattern r.before true) r.guard.compile

def Rule.post (r : Rule) : Pattern .config := configPattern r.after false

def Rule.nextSentence (r : Rule) : Matching.FirstOrder.Sentence signature.algebra :=
  ⟨4, context, .config, .neg (.conj r.pre (.neg (unary .step r.post)))⟩

def Rule.compile (r : Rule) : Reachability.Sentence KSort.config signature :=
  ⟨4, context, .finite, r.pre, r.post⟩

def environment (v : (i : Fin 4) → Carrier (context i)) : Valuation :=
  ⟨v 0, v 1, v 2, v 3⟩

def valuation (v : Valuation) : (i : Fin 4) → Carrier (context i) :=
  fun i => if h0 : i = 0 then by subst i; exact v.tail
    else if h1 : i = 1 then by subst i; exact v.x
    else if h2 : i = 2 then by subst i; exact v.capturedVal
    else by
      have h3 : i = 3 := by omega
      subst i
      exact v.counter

end Silmaril.Logic.Kore.Operational.Conditional
