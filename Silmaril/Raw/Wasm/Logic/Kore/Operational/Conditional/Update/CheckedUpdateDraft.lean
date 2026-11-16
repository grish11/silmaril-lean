module

public import Silmaril.Wasm.Logic.Kore.Operational.Conditional.WasmBranch.Thms
public import Mathlib.Tactic.FinCases
import Batteries.Data.List.Lemmas

-- Expose core string definitions used by the kernel-checked literal fixtures.
import all Init.Data.String.Search
import all Init.Data.String.Slice.Numeric
import all Init.Data.String.Slice.Pattern
import all Init.Data.String.Basic
import all Init.Data.Int.Repr
import all Init.Data.Repr

/- Literal assignment execution and finite simulation support.
All-path and native control obligations remain explicit Task definitions below. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.BodyDraft
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Logic.Kore.Operational.Conditional.WasmBranch

def assignBody (target : LocalIdx) (value : BitVec 32) : List Instr :=
  [.intConst .i32 value, .localSet target]

/-- Execute the body, including the real frame mutation and block exit.
There is no assumed execution premise for this body. -/
theorem block_assign_steps {H : Type} (P : Profile) (host : HostSemantics H)
    (s : Store H) (f : Frame) (bt : BlockType)
    (target : LocalIdx) (value : BitVec 32)
    (blockType : f.module.blockType? bt = some ([], []))
    (bound : target.toNat < f.locals.length) :
    Steps P host
      ⟨s, f, [.plain (.block bt (assignBody target value))]⟩
      ⟨s, f.setLocal target (Val.i32 value), []⟩ := by
  have enter : Steps P host
      ⟨s, f, [.plain (.block bt (assignBody target value))]⟩
      ⟨s, f, [.label 0 [] (expression (assignBody target value))]⟩ := by
    simpa only [vals, List.map_nil, List.nil_append, List.length_nil] using
      (Core.Step.steps (Core.Step.block (P := P) (host := host)
        (s := s) (f := f) (body := assignBody target value)
        (vs := []) blockType rfl))
  have write : Steps P host
      ⟨s, f, expression (assignBody target value)⟩
      ⟨s, f.setLocal target (Val.i32 value), []⟩ := by
    change Steps P host
      ⟨s, f, [(Val.i32 value).toAdmin, .plain (.localSet target)]⟩
      ⟨s, f.setLocal target (Val.i32 value), []⟩
    exact Core.Step.steps (Core.Step.variable (Core.VariableStep.localSet bound))
  have leave : Steps P host
      ⟨s, f.setLocal target (Val.i32 value), [.label 0 [] []]⟩
      ⟨s, f.setLocal target (Val.i32 value), []⟩ := by
    simpa only [vals, List.map_nil] using
      (Core.Step.steps (Core.Step.labelVals (P := P) (host := host)
        (s := s) (f := f.setLocal target (Val.i32 value))
        (n := 0) (cont := []) (vs := [])))
  exact enter.trans ((Core.Steps.label write).trans leave)

/-- Selection followed by execution of the chosen literal-assignment body.
The original source relation is NOT claimed to observe the changed counter. -/
theorem entry_assigns {H : Type} (L : Layout) (P : Profile) (host : HostSemantics H)
    (s : Store H) (f : Frame) (older : List Val) (tail : List String)
    (rest : List Admin) (valueLocal target : LocalIdx)
    (q zeroValue nonzeroValue : BitVec 32)
    (readValue : Silmaril.Wasm.Logic.Core.localVal? f valueLocal = some (Val.i32 q))
    (zeroBody : L.zeroBody = assignBody target zeroValue)
    (nonzeroBody : L.nonzeroBody = assignBody target nonzeroValue)
    (blockType : f.module.blockType? L.blockType = some ([], []))
    (bound : target.toNat < f.locals.length) :
    Steps P host (native L .entry s f older tail rest valueLocal)
      ⟨s, f.setLocal target (Val.i32 (if q = 0 then zeroValue else nonzeroValue)),
        vals older ++ L.tailCode tail ++ rest⟩ := by
  have selectedRun : Steps P host
      (native L (selected q) s f older tail rest valueLocal)
      ⟨s, f.setLocal target (Val.i32 (if q = 0 then zeroValue else nonzeroValue)),
        vals older ++ L.tailCode tail ++ rest⟩ := by
    by_cases hz : q = 0
    · simpa only [selected, ite_eq_left hz, native, zeroBody, List.append_assoc,
        List.append_nil, List.nil_append] using
        (Core.Steps.ctxtInstrs (vs := older) (rest := L.tailCode tail ++ rest)
          (block_assign_steps P host s f L.blockType target zeroValue blockType bound))
    · simpa only [selected, ite_eq_right hz, native, nonzeroBody, List.append_assoc,
        List.append_nil, List.nil_append] using
        (Core.Steps.ctxtInstrs (vs := older) (rest := L.tailCode tail ++ rest)
          (block_assign_steps P host s f L.blockType target nonzeroValue blockType bound))
  exact (native_steps L P host s f older tail rest valueLocal q readValue).trans selectedRun

/-- Finite reachability in the existing actual native-step matching model. -/
theorem entry_assigns_matching {H : Type} (L : Layout) (P : Profile)
    (host : HostSemantics H) (s : Store H) (f : Frame)
    (older : List Val) (tail : List String) (rest : List Admin)
    (valueLocal target : LocalIdx) (q zeroValue nonzeroValue : BitVec 32)
    (readValue : Silmaril.Wasm.Logic.Core.localVal? f valueLocal = some (Val.i32 q))
    (zeroBody : L.zeroBody = assignBody target zeroValue)
    (nonzeroBody : L.nonzeroBody = assignBody target nonzeroValue)
    (blockType : f.module.blockType? L.blockType = some ([], []))
    (bound : target.toNat < f.locals.length) :
    Silmaril.Logic.Matching.FixedPoint.Sentence.Satisfies
      (Silmaril.Logic.Reachability.WasmExpr.predicateModel P host
        (native L .entry s f older tail rest valueLocal)
        (fun w => w =
          ⟨s, f.setLocal target (Val.i32 (if q = 0 then zeroValue else nonzeroValue)),
            vals older ++ L.tailCode tail ++ rest⟩))
      (Silmaril.Logic.Reachability.encode ()
        (Silmaril.Logic.Reachability.atomRule .finite false true)) := by
  apply (Silmaril.Logic.Reachability.WasmExpr.compiled_iff_steps P host _ _).mpr
  exact ⟨_, entry_assigns L P host s f older tail rest valueLocal target q
    zeroValue nonzeroValue readValue zeroBody nonzeroBody blockType bound, rfl⟩

end Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.BodyDraft

/- Narrow authored update profile with counter-cell interpretation and finite simulation.
The existing Raw parser is reused. These rules are manually authored updates
using archived declarations; they are not emitted upstream TEST.AB/AC rules.
The narrow added counterCell operation interprets the actual archived
Lbl'-LT-'generatedCounter'-GT-' constructor as singleton identity on Int. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft

inductive Guard | zero | nonzero deriving DecidableEq, Repr

/-- Total interpretation selected for the pinned INT.eq hooked symbol. -/
def intEqual (x y : Int) : Bool := decide (x = y)

def Guard.eval : Guard → Int → Bool
  | .zero, x => intEqual x 0
  | .nonzero, x => !(intEqual x 0)

/-- Explicit semantics of the emitted Boolean equality-to-true guard. -/
def Guard.Holds (g : Guard) (x : Int) : Prop := g.eval x = true

inductive Target | val | counter deriving DecidableEq, Repr

/-- The checked text profile admits only canonical signed-i32 RHS literals. -/
def signedI32 (x : Int) : Bool := decide (-(2^31) ≤ x ∧ x < 2^31)

structure Rule where
  before : String
  after : String
  guard : Guard
  target : Target
  literal : Int
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
  match r.target with
  | .val => ⟨r.after :: v.tail, r.literal, v.counter⟩
  | .counter => ⟨r.after :: v.tail, v.capturedVal, r.literal⟩

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

def Rule.rhsTree (r : Rule) (Γ : Context) : Raw :=
  .app2 "Lbl'-LT-'generatedTop'-GT-'" []
    (.app2 "Lbl'-LT-'T'-GT-'" []
      (.app1 "Lbl'-LT-'k'-GT-'" []
        (.app2 "kseq" []
          (.app1 "inj" ["SortState", "SortKItem"] (.domainValue "SortState" r.after))
          (.variable Γ.tail "SortK")))
      (match r.target with
       | .val => .app1 "Lbl'-LT-'val'-GT-'" [] (.domainValue "SortInt" (toString r.literal))
       | .counter => .variable Γ.capturedVal "SortValCell"))
    (match r.target with
     | .val => .variable Γ.counter "SortGeneratedCounterCell"
     | .counter => .app1 "Lbl'-LT-'generatedCounter'-GT-'" []
         (.domainValue "SortInt" (toString r.literal)))

def Rule.tree (r : Rule) (Γ : Context) : Raw :=
  .rewrites "SortGeneratedTopCell"
    (.and "SortGeneratedTopCell" (configTree Γ r.before true) (guardTree Γ r.guard))
    (.and "SortGeneratedTopCell" (r.rhsTree Γ) (.top "SortGeneratedTopCell"))

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
        (.app1 _ _ (.app2 _ _ (.app1 _ _ (.domainValue _ after)) _)) rhsVal) rhsCounter) _) =>
      let Γ : Context := ⟨tail, x, captured, counter⟩
      if !Γ.distinct then none else
      let g ← if guard = guardTree Γ .zero then some Guard.zero
        else if guard = guardTree Γ .nonzero then some Guard.nonzero else none
      let (target, text) ← match rhsVal, rhsCounter with
        | .app1 "Lbl'-LT-'val'-GT-'" [] (.domainValue "SortInt" text), .variable _ _ =>
            some (Target.val, text)
        | .variable _ _, .app1 "Lbl'-LT-'generatedCounter'-GT-'" [] (.domainValue "SortInt" text) =>
            some (Target.counter, text)
        | _, _ => none
      let literal ← text.toInt?
      if !signedI32 literal then none else
      let r : Rule := ⟨before, after, g, target, literal⟩
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
  | counterCell : Operation 1 (fun _ => .integer) .counter
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
    | .counterCell => fun v => {v 0}
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

def Rule.post (r : Rule) : Pattern .config :=
  binary .topcell
    (binary .tcell (unary .kcell (statePattern r.after))
      (match r.target with
       | .val => unary .valcell (constant (.intValue r.literal))
       | .counter => .var 2))
    (match r.target with
     | .val => .var 3
     | .counter => unary .counterCell (constant (.intValue r.literal)))

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

private theorem unary_mem (M : Matching.FirstOrder.Model signature.algebra) {a b : KSort}
    (op : Operation 1 (fun _ => a) b) (p : Pattern a)
    (v : (i : Fin 4) → M.carrier (context i)) (result : M.carrier b) :
    result ∈ M.denote v (unary op p) ↔
      ∃ x, x ∈ M.denote v p ∧ result ∈ M.operation op (fun _ => x) := by
  constructor
  · rintro ⟨xs, hx, hr⟩
    refine ⟨xs 0, hx 0, ?_⟩
    have he : xs = fun _ => xs 0 := by funext i; fin_cases i; rfl
    simpa only [← he] using hr
  · rintro ⟨x, hx, hr⟩
    exact ⟨fun _ => x, fun _ => hx, hr⟩

private theorem binary_mem (M : Matching.FirstOrder.Model signature.algebra) {a b c : KSort}
    (op : Operation 2 (Fin.cases a (fun _ => b)) c) (p : Pattern a) (q : Pattern b)
    (v : (i : Fin 4) → M.carrier (context i)) (result : M.carrier c) :
    result ∈ M.denote v (binary op p q) ↔
      ∃ x, x ∈ M.denote v p ∧ ∃ y, y ∈ M.denote v q ∧
        result ∈ M.operation op (Fin.cases x (fun _ => y)) := by
  constructor
  · rintro ⟨xs, hx, hr⟩
    refine ⟨xs 0, hx 0, xs 1, hx 1, ?_⟩
    have he : xs = Fin.cases (xs 0) (fun _ => xs 1) := by
      funext i; fin_cases i <;> rfl
    simpa only [← he] using hr
  · rintro ⟨x, hx, y, hy, hr⟩
    refine ⟨Fin.cases x (fun _ => y), ?_, hr⟩
    intro i
    fin_cases i
    · exact hx
    · exact hy

private theorem constant_mem (M : Matching.FirstOrder.Model signature.algebra) {s : KSort}
    (op : Operation 0 Fin.elim0 s) (v : (i : Fin 4) → M.carrier (context i))
    (result : M.carrier s) :
    result ∈ M.denote v (constant op) ↔
      result ∈ M.operation op (fun i => i.elim0) := by
  constructor
  · rintro ⟨xs, _, hr⟩
    have he : xs = fun i => i.elim0 := by funext i; exact i.elim0
    simpa only [he] using hr
  · intro hr
    exact ⟨(fun i => i.elim0), (fun i => i.elim0), hr⟩

private theorem state_denote (R : Config → Config → Prop)
    (v : (i : Fin 4) → Carrier (context i)) (s : String) :
    (model R).denote v (statePattern s) = {s :: v 0} := by
  ext c
  change c ∈ (model R).denote v (binary .sequence
    (unary .injection (constant (.token s))) (.var 0)) ↔ c = s :: v 0
  rw [binary_mem (model R) .sequence _ _ v c]
  simp only [unary_mem (model R), constant_mem (model R), Matching.FirstOrder.Model.denote, Set.mem_singleton_iff]
  simp [Fin.cases, Fin.induction, Fin.induction.go]
  rfl

/-- Both hooked Boolean operations really return exactly one Boolean. -/
theorem guard_bool_denote (R : Config → Config → Prop)
    (v : (i : Fin 4) → Carrier (context i)) (g : Guard) :
    (model R).denote v g.boolPattern = {g.eval (v 1)} := by
  cases g <;> ext b <;>
    simp only [Guard.boolPattern, binary_mem (model R), unary_mem (model R), constant_mem (model R),
      Matching.FirstOrder.Model.denote, Set.mem_singleton_iff] <;>
    simp [Fin.cases, Fin.induction, Fin.induction.go, Guard.eval] <;> rfl

/-- Source Boolean equality compares the two singleton result sets. -/
theorem source_equals_true_iff (R : Config → Config → Prop)
    (v : (i : Fin 4) → Carrier (context i)) (g : Guard) :
    (model R).denote v g.boolPattern = {true} ↔ g.Holds (v 1) := by
  rw [guard_bool_denote R]
  constructor
  · intro h
    have ht : g.eval (v 1) ∈ ({true} : Set Bool) := h ▸ (Set.mem_singleton _)
    exact ht
  · intro h
    exact congrArg (fun b : Bool => ({b} : Set Bool)) h

/-- Ceil of the intersection is valid here because the source Boolean result
is singleton; no general set equality is identified with nonempty intersection. -/
theorem guard_compile_mem (R : Config → Config → Prop)
    (v : (i : Fin 4) → Carrier (context i)) (g : Guard) (c : Config) :
    c ∈ (model R).denote v g.compile ↔ g.Holds (v 1) := by
  simp only [Guard.compile, unary_mem (model R), Matching.FirstOrder.Model.denote,
    guard_bool_denote R, constant_mem (model R), Set.mem_inter_iff, Set.mem_singleton_iff]
  simp [Guard.Holds]

/-- The native intersection preserves the actual as-pattern binding. -/
theorem value_mem (R : Config → Config → Prop)
    (v : (i : Fin 4) → Carrier (context i)) (x : Int) :
    x ∈ (model R).denote v (valuePattern true) ↔ x = v 1 ∧ x = v 2 := by
  simp [valuePattern, Matching.FirstOrder.Model.denote, unary_mem (model R)]

/-- All original constructor fields and the as-pattern coherence are retained. -/
theorem before_mem (R : Config → Config → Prop)
    (v : (i : Fin 4) → Carrier (context i)) (s : String) (c : Config) :
    c ∈ (model R).denote v (configPattern s true) ↔
      v 1 = v 2 ∧ c = ⟨s :: v 0, v 1, v 3⟩ := by
  simp only [configPattern, binary_mem (model R), unary_mem (model R), state_denote R, value_mem R,
    Matching.FirstOrder.Model.denote, Set.mem_singleton_iff]
  simp [Fin.cases, Fin.induction, Fin.induction.go]
  intro _
  rfl

/-- Shared preserved-cell configuration helper; the update post is separate. -/
theorem after_denote (R : Config → Config → Prop)
    (v : (i : Fin 4) → Carrier (context i)) (s : String) :
    (model R).denote v (configPattern s false) = {⟨s :: v 0, v 2, v 3⟩} := by
  ext c
  simp only [configPattern, binary_mem (model R), unary_mem (model R), state_denote R, valuePattern,
    Matching.FirstOrder.Model.denote, Set.mem_singleton_iff]
  simp [Fin.cases, Fin.induction, Fin.induction.go]
  rfl

theorem pre_mem (R : Config → Config → Prop)
    (v : (i : Fin 4) → Carrier (context i)) (r : Rule) (c : Config) :
    c ∈ (model R).denote v r.pre ↔
      v 1 = v 2 ∧ r.guard.Holds (v 1) ∧ c = r.beforeConfig (environment v) := by
  simp only [Rule.pre, Matching.FirstOrder.Model.denote, Set.mem_inter_iff,
    before_mem R, guard_compile_mem R]
  simp only [Rule.beforeConfig, environment]
  tauto

theorem post_denote (R : Config → Config → Prop)
    (v : (i : Fin 4) → Carrier (context i)) (r : Rule) :
    (model R).denote v r.post = {r.afterConfig (environment v)} := by
  cases ht : r.target <;> ext c <;>
    simp only [Rule.post, ht, binary_mem (model R), unary_mem (model R),
      constant_mem (model R), state_denote R, Matching.FirstOrder.Model.denote,
      Set.mem_singleton_iff, Rule.afterConfig, environment] <;>
    simp [Fin.cases, Fin.induction, Fin.induction.go] <;> rfl

theorem next_mem (R : Config → Config → Prop)
    (v : (i : Fin 4) → Carrier (context i)) (r : Rule) (c : Config) :
    c ∈ (model R).denote v (unary .step r.post) ↔
      R c (r.afterConfig (environment v)) := by
  simp [unary_mem (model R), post_denote R]

/-- Successful traversal retains exactly the successfully elaborated declarations. -/
theorem mapM_members {ds : List Silmaril.Logic.Kore.Operational.Declaration} {checked : List (Context × Rule)}
    (h : ds.mapM elaborate = some checked) (pair : Context × Rule) :
    pair ∈ checked ↔ ∃ d ∈ ds, elaborate d = some pair := by
  have aligned : List.Forall₂ (fun d p => elaborate d = some p) ds checked :=
    List.mapM_eq_some_iff_forall₂.mp h
  have filtered : ds.filterMap elaborate = checked := by
    clear h
    induction aligned with
    | nil => rfl
    | @cons d p ds checked hd _ ih =>
      show (d :: ds).filterMap elaborate = p :: checked
      simp only [List.filterMap_cons, hd, ih]
  rw [← filtered, List.mem_filterMap]

@[simp] theorem environment_valuation (v : Valuation) : environment (valuation v) = v := by
  cases v
  rfl

/-- Exact inversion of the independent guarded relation, retaining every capture. -/
theorem step_iff (rules : List Rule) (c d : Config) :
    Step rules c d ↔ ∃ r ∈ rules, ∃ v : Valuation,
      v.x = v.capturedVal ∧ r.guard.Holds v.x ∧
      c = r.beforeConfig v ∧ d = r.afterConfig v := by
  constructor
  · intro h
    cases h with
    | rule r hr v hc hg => exact ⟨r, hr, v, hc, hg, rfl, rfl⟩
  · rintro ⟨r, hr, v, hc, hg, rfl, rfl⟩
    exact .rule r hr v hc hg

/-- Exact guarded next meaning, including independent as-pattern coherence. -/
theorem nextSentence_satisfies_iff (R : Config → Config → Prop) (r : Rule) :
    r.nextSentence.Satisfies (model R) ↔
      ∀ v, v.x = v.capturedVal → r.guard.Holds v.x →
        R (r.beforeConfig v) (r.afterConfig v) := by
  have hmem (v : (i : Fin 4) → Carrier (context i)) (c : Config) :
      c ∈ (model R).denote v (.neg (.conj r.pre (.neg (unary .step r.post)))) ↔
        (v 1 = v 2 → r.guard.Holds (v 1) →
          c = r.beforeConfig (environment v) → R c (r.afterConfig (environment v))) := by
    simp only [Matching.FirstOrder.Model.denote, Set.mem_compl_iff, Set.mem_inter_iff]
    rw [pre_mem, next_mem]
    tauto
  change (∀ v c, c ∈ (model R).denote v (.neg (.conj r.pre (.neg (unary .step r.post))))) ↔ _
  simp_rw [hmem]
  constructor
  · intro h v hc hg
    simpa only [environment_valuation] using h (valuation v) (r.beforeConfig v) hc hg (by simp)
  · intro h v c hc hg he
    subst c
    exact h (environment v) hc hg

/-- The independent guarded operational relation satisfies every installed rule. -/
theorem next_sound (rules : List Rule) (r : Rule) (hr : r ∈ rules) :
    r.nextSentence.Satisfies (model (Step rules)) :=
  (nextSentence_satisfies_iff _ _).2 (fun v hc hg => .rule r hr v hc hg)

/-- Exact finite reachability iff, not only a generated-model soundness result. -/
theorem compile_satisfies_iff (R : Config → Config → Prop) (r : Rule) :
    r.compile.Satisfies KSort.config (model R) ↔
      ∀ v, v.x = v.capturedVal → r.guard.Holds v.x →
        Reachability.Reaches R (fun c => c = r.afterConfig v) (r.beforeConfig v) := by
  change (∀ v c, c ∈ (model R).denote v r.pre →
    Reachability.Reaches R (fun d => d ∈ (model R).denote v r.post) c) ↔ _
  simp_rw [pre_mem R, post_denote R, Set.mem_singleton_iff]
  constructor
  · intro h v hc hg
    simpa only [environment_valuation] using
      h (valuation v) (r.beforeConfig v) ⟨hc, hg, by simp⟩
  · intro h v c ⟨hc, hg, he⟩
    subst c
    exact h (environment v) hc hg

theorem compile_sound (rules : List Rule) (r : Rule) (hr : r ∈ rules) :
    r.compile.Satisfies KSort.config (model (Step rules)) :=
  (compile_satisfies_iff _ _).2 fun v hc hg =>
    .next trivial (.rule r hr v hc hg) (.now rfl)

/-- Existing reachability-to-native-μ translation applied to guarded rules. -/
theorem compiled_matching_sound (rules : List Rule) (r : Rule) (hr : r ∈ rules) :
    Matching.FixedPoint.Sentence.Satisfies (model (Step rules))
      (Reachability.encode KSort.config r.compile) :=
  (Reachability.encode_correct _ _).2 (compile_sound rules r hr)

/-- A successful complete check recovers the original parsed declarations and
successful elaboration of every declaration, including claims. -/
theorem check_source {input : String} {p : CheckedProgram} (h : check input = some p) :
    ∃ tokens, Text.tokenize input = some tokens ∧
      Text.declarations (tokens.length + 1) tokens = some p.declarations ∧
      p.declarations.mapM elaborate = some p.checked := by
  cases ht : Text.tokenize input with
  | none => simp [check, ht] at h
  | some tokens =>
    cases hd : Text.declarations (tokens.length + 1) tokens with
    | none => simp [check, ht, hd] at h
    | some ds =>
      cases he : ds.mapM elaborate with
      | none => simp [check, ht, hd, he] at h
      | some checked =>
        simp [check, ht, hd, he] at h
        subst p
        exact ⟨tokens, rfl, hd, he⟩

/-- Successful checking aligns every checked pair with a real source declaration. -/
theorem checked_iff {input : String} {p : CheckedProgram}
    (h : check input = some p) (pair : Context × Rule) :
    pair ∈ p.checked ↔ ∃ d ∈ p.declarations, elaborate d = some pair := by
  obtain ⟨_, _, _, he⟩ := check_source h
  exact mapM_members he pair

/-- Every installed axiom comes from an actual declaration; claims contribute none. -/
theorem axioms_iff {input : String} {p : CheckedProgram}
    (_h : check input = some p) (r : Rule) :
    r ∈ p.axioms ↔ ∃ d ∈ p.declarations, d.kind = .ruleAxiom ∧
      ∃ Γ, elaborate d = some (Γ, r) ∧ (Γ, r) ∈ p.checked := by
  simp only [CheckedProgram.axioms, List.mem_filterMap]
  constructor
  · rintro ⟨d, hd, he⟩
    split at he
    next hk =>
      cases hel : elaborate d with
      | none => simp [hel] at he
      | some pair =>
        rcases pair with ⟨Γ, r'⟩
        simp only [hel, Option.map_some, Option.some.injEq] at he
        subst r'
        exact ⟨d, hd, hk, Γ, hel, (checked_iff _h (Γ, r)).2 ⟨d, hd, hel⟩⟩
    next => simp at he
  · rintro ⟨d, hd, hk, Γ, he, _⟩
    exact ⟨d, hd, by simp [hk, he]⟩

/-- Matching soundness tied to an actual accepted source axiom. -/
theorem declaration_matching_sound {input : String} {p : CheckedProgram}
    (_h : check input = some p) (d : Declaration) (hd : d ∈ p.declarations)
    (hk : d.kind = .ruleAxiom) (Γ : Context) (r : Rule)
    (hr : elaborate d = some (Γ, r)) :
    Matching.FixedPoint.Sentence.Satisfies (model (Step p.axioms))
      (Reachability.encode KSort.config r.compile) :=
  compiled_matching_sound _ r ((axioms_iff _h r).2 ⟨d, hd, hk, Γ, hr, (checked_iff _h (Γ, r)).2 ⟨d, hd, hr⟩⟩)

end Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft

namespace Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft
def authoredZeroBytes : String := "  axiom{} \\rewrites{SortGeneratedTopCell{}} (\n      \\and{SortGeneratedTopCell{}} (\n        Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortState{}, SortKItem{}}(\\dv{SortState{}}(\"a\")),Var'Unds'DotVar2:SortK{})),\\and{SortValCell{}}(Lbl'-LT-'val'-GT-'{}(VarX:SortInt{}),Var'Unds'Gen5:SortValCell{})),Var'Unds'DotVar0:SortGeneratedCounterCell{}),\n        \\equals{SortBool{},SortGeneratedTopCell{}}(\n        Lbl'UndsEqlsEqls'Int'Unds'{}(VarX:SortInt{},\\dv{SortInt{}}(\"0\")),\n        \\dv{SortBool{}}(\"true\"))),\n      \\and{SortGeneratedTopCell{}} (\n      Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortState{}, SortKItem{}}(\\dv{SortState{}}(\"b\")),Var'Unds'DotVar2:SortK{})),Var'Unds'Gen5:SortValCell{}),Lbl'-LT-'generatedCounter'-GT-'{}(\\dv{SortInt{}}(\"11\"))), \\top{SortGeneratedTopCell{}}()))\n  []\n"
def authoredNonzeroBytes : String := "  axiom{} \\rewrites{SortGeneratedTopCell{}} (\n      \\and{SortGeneratedTopCell{}} (\n        Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortState{}, SortKItem{}}(\\dv{SortState{}}(\"a\")),Var'Unds'DotVar2:SortK{})),\\and{SortValCell{}}(Lbl'-LT-'val'-GT-'{}(VarX:SortInt{}),Var'Unds'Gen5:SortValCell{})),Var'Unds'DotVar0:SortGeneratedCounterCell{}),\n        \\equals{SortBool{},SortGeneratedTopCell{}}(\n        LblnotBool'Unds'{}(Lbl'UndsEqlsEqls'Int'Unds'{}(VarX:SortInt{},\\dv{SortInt{}}(\"0\"))),\n        \\dv{SortBool{}}(\"true\"))),\n      \\and{SortGeneratedTopCell{}} (\n      Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortState{}, SortKItem{}}(\\dv{SortState{}}(\"c\")),Var'Unds'DotVar2:SortK{})),Var'Unds'Gen5:SortValCell{}),Lbl'-LT-'generatedCounter'-GT-'{}(\\dv{SortInt{}}(\"13\"))), \\top{SortGeneratedTopCell{}}()))\n  []\n"
def malformedWholeTreeBytes : String := "  axiom{} \\rewrites{SortGeneratedTopCell{}} (\n      \\and{SortGeneratedTopCell{}} (\n        Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortState{}, SortKItem{}}(\\dv{SortState{}}(\"a\")),WrongTail:SortK{})),\\and{SortValCell{}}(Lbl'-LT-'val'-GT-'{}(VarX:SortInt{}),Var'Unds'Gen5:SortValCell{})),Var'Unds'DotVar0:SortGeneratedCounterCell{}),\n        \\equals{SortBool{},SortGeneratedTopCell{}}(\n        Lbl'UndsEqlsEqls'Int'Unds'{}(VarX:SortInt{},\\dv{SortInt{}}(\"0\")),\n        \\dv{SortBool{}}(\"true\"))),\n      \\and{SortGeneratedTopCell{}} (\n      Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortState{}, SortKItem{}}(\\dv{SortState{}}(\"b\")),Var'Unds'DotVar2:SortK{})),Var'Unds'Gen5:SortValCell{}),Lbl'-LT-'generatedCounter'-GT-'{}(\\dv{SortInt{}}(\"11\"))), \\top{SortGeneratedTopCell{}}()))\n  []\n"
def outOfRangeBytes : String := "  axiom{} \\rewrites{SortGeneratedTopCell{}} (\n      \\and{SortGeneratedTopCell{}} (\n        Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortState{}, SortKItem{}}(\\dv{SortState{}}(\"a\")),Var'Unds'DotVar2:SortK{})),\\and{SortValCell{}}(Lbl'-LT-'val'-GT-'{}(VarX:SortInt{}),Var'Unds'Gen5:SortValCell{})),Var'Unds'DotVar0:SortGeneratedCounterCell{}),\n        \\equals{SortBool{},SortGeneratedTopCell{}}(\n        Lbl'UndsEqlsEqls'Int'Unds'{}(VarX:SortInt{},\\dv{SortInt{}}(\"0\")),\n        \\dv{SortBool{}}(\"true\"))),\n      \\and{SortGeneratedTopCell{}} (\n      Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortState{}, SortKItem{}}(\\dv{SortState{}}(\"b\")),Var'Unds'DotVar2:SortK{})),Var'Unds'Gen5:SortValCell{}),Lbl'-LT-'generatedCounter'-GT-'{}(\\dv{SortInt{}}(\"2147483648\"))), \\top{SortGeneratedTopCell{}}()))\n  []\n"

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem authored_zero_checked :
    (check authoredZeroBytes).map (fun p => p.axioms) =
      some [⟨"a", "b", .zero, .counter, 11⟩] := by
  let Γ : Context := ⟨"Var'Unds'DotVar2", "VarX", "Var'Unds'Gen5", "Var'Unds'DotVar0"⟩
  let r : Rule := ⟨"a", "b", .zero, .counter, 11⟩
  let d : Declaration := ⟨.ruleAxiom, [], r.tree Γ, []⟩
  have parsed : ((Text.tokenize authoredZeroBytes).bind fun tokens =>
      Text.declarations (tokens.length + 1) tokens) = some [d] := by
    decide +kernel
  have elaborated : elaborate d = some (Γ, r) := by
    cbv
  have checked : check authoredZeroBytes = some ⟨[d], [(Γ, r)]⟩ := by
    change ((Text.tokenize authoredZeroBytes).bind fun tokens =>
      (Text.declarations (tokens.length + 1) tokens).bind fun ds =>
        (ds.mapM elaborate).bind fun pairs => some (⟨ds, pairs⟩ : CheckedProgram)) = _
    rw [← Option.bind_assoc, parsed]
    simp [List.mapM_cons, elaborated]
  rw [checked]
  change some ([d].filterMap fun entry =>
    if entry.kind = .ruleAxiom then (elaborate entry).map Prod.snd else none) = some [r]
  simp [List.filterMap, show d.kind = .ruleAxiom from rfl, elaborated]

/-- info: 'Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.authored_zero_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms authored_zero_checked

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem authored_nonzero_checked :
    (check authoredNonzeroBytes).map (fun p => p.axioms) =
      some [⟨"a", "c", .nonzero, .counter, 13⟩] := by
  let Γ : Context := ⟨"Var'Unds'DotVar2", "VarX", "Var'Unds'Gen5", "Var'Unds'DotVar0"⟩
  let r : Rule := ⟨"a", "c", .nonzero, .counter, 13⟩
  let d : Declaration := ⟨.ruleAxiom, [], r.tree Γ, []⟩
  have parsed : ((Text.tokenize authoredNonzeroBytes).bind fun tokens =>
      Text.declarations (tokens.length + 1) tokens) = some [d] := by
    decide +kernel
  have elaborated : elaborate d = some (Γ, r) := by
    cbv
  have checked : check authoredNonzeroBytes = some ⟨[d], [(Γ, r)]⟩ := by
    change ((Text.tokenize authoredNonzeroBytes).bind fun tokens =>
      (Text.declarations (tokens.length + 1) tokens).bind fun ds =>
        (ds.mapM elaborate).bind fun pairs => some (⟨ds, pairs⟩ : CheckedProgram)) = _
    rw [← Option.bind_assoc, parsed]
    simp [List.mapM_cons, elaborated]
  rw [checked]
  change some ([d].filterMap fun entry =>
    if entry.kind = .ruleAxiom then (elaborate entry).map Prod.snd else none) = some [r]
  simp [List.filterMap, show d.kind = .ruleAxiom from rfl, elaborated]

/-- info: 'Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.authored_nonzero_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms authored_nonzero_checked

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem malformed_whole_tree_rejected : check malformedWholeTreeBytes = none := by cbv

/-- info: 'Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.malformed_whole_tree_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms malformed_whole_tree_rejected

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem out_of_range_rejected : check outOfRangeBytes = none := by cbv

/-- info: 'Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.out_of_range_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms out_of_range_rejected

theorem authored_zero_old7_new11 (tail : List String) :
    Step [⟨"a", "b", .zero, .counter, 11⟩]
      ⟨"a" :: tail, 0, 7⟩ ⟨"b" :: tail, 0, 11⟩ := by
  exact Step.rule ⟨"a", "b", .zero, .counter, 11⟩ (by simp) ⟨tail, 0, 0, 7⟩ rfl
    (by simp [Guard.Holds, Guard.eval, intEqual])

theorem authored_nonzero_old7_new13 (tail : List String) (x : Int) (hx : x ≠ 0) :
    Step [⟨"a", "c", .nonzero, .counter, 13⟩]
      ⟨"a" :: tail, x, 7⟩ ⟨"c" :: tail, x, 13⟩ := by
  exact Step.rule ⟨"a", "c", .nonzero, .counter, 13⟩ (by simp) ⟨tail, x, x, 7⟩ rfl
    (by simp [Guard.Holds, Guard.eval, intEqual, hx])
end Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft

namespace Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Native
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Logic

def rules (L : Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.Layout) (z n : Int) : List Rule :=
  [⟨L.entry, L.zero, .zero, .counter, z⟩,
   ⟨L.entry, L.nonzero, .nonzero, .counter, n⟩]

def entrySource (L : Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.Layout) (tail : List String) (q k : BitVec 32) : Config :=
  ⟨L.entry :: tail, q.toInt, k.toInt⟩

def afterSource (L : Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.Layout) (tail : List String) (q : BitVec 32) (z n : Int) : Config :=
  ⟨L.name (Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.selected q) :: tail, q.toInt, if q = 0 then z else n⟩

/-- Exact successor characterization for the independent update relation. -/
theorem source_step_iff (L : Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.Layout) (tail : List String) (q k : BitVec 32)
    (z n : Int) (d : Config) :
    Step (rules L z n) (entrySource L tail q k) d ↔
      d = afterSource L tail q z n := by
  constructor
  · intro h
    obtain ⟨r, hr, v, hc, hg, he, hd⟩ := (step_iff _ _ _).mp h
    have hr' : r = ⟨L.entry, L.zero, .zero, .counter, z⟩ ∨
        r = ⟨L.entry, L.nonzero, .nonzero, .counter, n⟩ := by
      simpa only [rules, List.mem_cons, List.not_mem_nil, or_false] using hr
    have hv : q.toInt = v.x := congrArg Config.val he
    have ht : tail = v.tail := (List.cons.inj (congrArg Config.code he)).2
    rcases hr' with rfl | rfl
    · have hz : q = 0 := (Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.signed_zero_iff q).mp (hv.trans (by
        simpa only [Guard.Holds, Guard.eval, intEqual, decide_eq_true_eq] using hg))
      simpa only [afterSource, Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.selected, ite_eq_left hz, Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.Layout.name,
        Rule.afterConfig, ← ht, ← hc, ← hv] using hd
    · have hz : q ≠ 0 := by
        intro hq
        have hv0 : v.x = 0 := hv.symm.trans ((Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.signed_zero_iff q).mpr hq)
        simp [Guard.Holds, Guard.eval, intEqual, hv0] at hg
      simpa only [afterSource, Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.selected, ite_eq_right hz, Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.Layout.name,
        Rule.afterConfig, ← ht, ← hc, ← hv] using hd
  · rintro rfl
    by_cases hz : q = 0
    · have hv : q.toInt = 0 := (Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.signed_zero_iff q).mpr hz
      simpa only [entrySource, afterSource, Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.selected, ite_eq_left hz,
        Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.Layout.name, Rule.beforeConfig, Rule.afterConfig] using
        (Step.rule (rules := rules L z n) ⟨L.entry, L.zero, .zero, .counter, z⟩
          (by simp [rules]) ⟨tail, q.toInt, q.toInt, k.toInt⟩ rfl
          (by simp [Guard.Holds, Guard.eval, intEqual, hv]))
    · have hv : q.toInt ≠ 0 := fun h => hz ((Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.signed_zero_iff q).mp h)
      simpa only [entrySource, afterSource, Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.selected, ite_eq_right hz,
        Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.Layout.name, Rule.beforeConfig, Rule.afterConfig] using
        (Step.rule (rules := rules L z n) ⟨L.entry, L.nonzero, .nonzero, .counter, n⟩
          (by simp [rules]) ⟨tail, q.toInt, q.toInt, k.toInt⟩ rfl
          (by simp [Guard.Holds, Guard.eval, intEqual, hv]))

/-- The write changes the observed counter and preserves the distinct val local.
The premise concerns the initial frame only, never a pre-assumed post-relation. -/
theorem write_agrees (f : Frame) (valueLocal counterLocal : LocalIdx)
    (q k updated : BitVec 32)
    (distinct : valueLocal.toNat ≠ counterLocal.toNat)
    (bound : counterLocal.toNat < f.locals.length)
    (agree : Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.LocalsAgree f valueLocal counterLocal q k) :
    Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.LocalsAgree (f.setLocal counterLocal (Val.i32 updated))
      valueLocal counterLocal q updated := by
  constructor
  · simpa [Silmaril.Wasm.Logic.Core.localVal?, Frame.local?, Frame.setLocal,
      List.getElem?_set, distinct, Ne.symm distinct] using agree.1
  · simp [Silmaril.Wasm.Logic.Core.localVal?, Frame.local?, Frame.setLocal, bound]

/-- The after relation includes the actual changed source Config, frame write,
both observed locals and signed (non-wrapping) counter interpretation. -/
def postRelated {H : Type} (L : Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.Layout) (s : Store H) (f : Frame)
    (older : List Val) (tail : List String) (rest : List Admin)
    (valueLocal counterLocal : LocalIdx) (q : BitVec 32) (z n : Int)
    (d : Config) (w : Core.Config H) : Prop :=
  let updated := if q = 0 then z else n
  d = afterSource L tail q z n ∧
  w = ⟨s, f.setLocal counterLocal (Val.i32 (BitVec.ofInt 32 updated)),
      vals older ++ L.tailCode tail ++ rest⟩ ∧
  Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.LocalsAgree (f.setLocal counterLocal (Val.i32 (BitVec.ofInt 32 updated)))
      valueLocal counterLocal q (BitVec.ofInt 32 updated) ∧
  (BitVec.ofInt 32 updated).toInt = updated

/-- Finite native body-changing simulation, derived from a source update step
and actual checked literal bodies. No arbitrary-body execution assumption. -/
theorem finite_simulation {H : Type} (L : Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.Layout) (P : Profile)
    (host : HostSemantics H) (s : Store H) (f : Frame)
    (older : List Val) (tail : List String) (rest : List Admin)
    (valueLocal counterLocal : LocalIdx) (q k : BitVec 32) (z n : Int)
    (distinct : valueLocal.toNat ≠ counterLocal.toNat)
    (bound : counterLocal.toNat < f.locals.length)
    (agree : Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.LocalsAgree f valueLocal counterLocal q k)
    (zeroBody : L.zeroBody = Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.BodyDraft.assignBody counterLocal (BitVec.ofInt 32 z))
    (nonzeroBody : L.nonzeroBody = Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.BodyDraft.assignBody counterLocal (BitVec.ofInt 32 n))
    (blockType : f.module.blockType? L.blockType = some ([], []))
    (zlo : -(2^31) ≤ z) (zhi : z < 2^31)
    (nlo : -(2^31) ≤ n) (nhi : n < 2^31)
    (d : Config) (step : Step (rules L z n) (entrySource L tail q k) d) :
    ∃ w', Steps P host (Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.native L .entry s f older tail rest valueLocal) w' ∧
      postRelated L s f older tail rest valueLocal counterLocal q z n d w' := by
  have hd := (source_step_iff L tail q k z n d).mp step
  have run := Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.BodyDraft.entry_assigns L P host s f older tail rest valueLocal counterLocal
    q (BitVec.ofInt 32 z) (BitVec.ofInt 32 n) agree.1 zeroBody nonzeroBody blockType bound
  have signed : (BitVec.ofInt 32 (if q = 0 then z else n)).toInt =
      (if q = 0 then z else n) := by
    split
    · exact Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.signed_representation z zlo zhi
    · exact Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.signed_representation n nlo nhi
  refine ⟨_, run, ?_⟩
  refine ⟨hd, ?_, write_agrees f valueLocal counterLocal q k _ distinct bound agree, signed⟩
  rw [apply_ite (BitVec.ofInt 32)]

/-- Finite matching statement for the actual native step relation and new
after relation. Source parsing/matching soundness is supplied above. -/
theorem checked_finite_matching {H : Type} (L : Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.Layout) (P : Profile)
    (host : HostSemantics H) (s : Store H) (f : Frame)
    (older : List Val) (tail : List String) (rest : List Admin)
    (valueLocal counterLocal : LocalIdx) (q k : BitVec 32) (z n : Int)
    (distinct : valueLocal.toNat ≠ counterLocal.toNat)
    (bound : counterLocal.toNat < f.locals.length)
    (agree : Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.LocalsAgree f valueLocal counterLocal q k)
    (zeroBody : L.zeroBody = Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.BodyDraft.assignBody counterLocal (BitVec.ofInt 32 z))
    (nonzeroBody : L.nonzeroBody = Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.BodyDraft.assignBody counterLocal (BitVec.ofInt 32 n))
    (blockType : f.module.blockType? L.blockType = some ([], []))
    (zlo : -(2^31) ≤ z) (zhi : z < 2^31)
    (nlo : -(2^31) ≤ n) (nhi : n < 2^31)
    (input : String) (program : CheckedProgram)
    (_checked : check input = some program)
    (installed : program.axioms = rules L z n)
    (d : Config) (step : Step program.axioms (entrySource L tail q k) d) :
    Matching.FixedPoint.Sentence.Satisfies
      (Reachability.WasmExpr.predicateModel P host
        (Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.native L .entry s f older tail rest valueLocal)
        (postRelated L s f older tail rest valueLocal counterLocal q z n d))
      (Reachability.encode () (Reachability.atomRule .finite false true)) :=
  (Reachability.WasmExpr.compiled_iff_steps P host _ _).mpr
    (finite_simulation L P host s f older tail rest valueLocal counterLocal q k z n
      distinct bound agree zeroBody nonzeroBody blockType zlo zhi nlo nhi d (by simpa only [installed] using step))

namespace Task
/-- OPEN: all finite complete native paths must hit the actual post relation.
This is not proved by finite_simulation. It needs native prefix inversion and
progress through localGet, if, block, localSet and label exit. Arbitrary later
continuation is allowed because AllPartial requires an intermediate hit. -/
def allPath {H : Type} (L : Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.Layout) (P : Profile) (host : HostSemantics H)
    (s : Store H) (f : Frame) (older : List Val) (tail : List String)
    (rest : List Admin) (valueLocal counterLocal : LocalIdx)
    (q : BitVec 32) (z n : Int) : Prop :=
  Reachability.AllPartial (Core.Step P host)
    (postRelated L s f older tail rest valueLocal counterLocal q z n
      (afterSource L tail q z n))
    (Silmaril.Logic.Kore.Operational.Conditional.WasmBranch.native L .entry s f older tail rest valueLocal)

/-- OPEN actual control obligations, not toy-relation controls. A concrete
instantiation must establish terminality or InfiniteTrace, then evaluate the
same matching predicate model. These declarations assert no result. -/
def actualStuck {H : Type} (P : Profile) (host : HostSemantics H)
    (w : Core.Config H) : Prop := ∀ w', ¬ Core.Step P host w w'

def actualDivergence {H : Type} (P : Profile) (host : HostSemantics H)
    (w : Core.Config H) : Prop := Core.Diverges P host w

def actualTrap {H : Type} (P : Profile) (host : HostSemantics H)
    (initial : Core.Config H) : Prop :=
  ∃ s f, Core.Steps P host initial ⟨s, f, [.trap]⟩
end Task
end Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Native
