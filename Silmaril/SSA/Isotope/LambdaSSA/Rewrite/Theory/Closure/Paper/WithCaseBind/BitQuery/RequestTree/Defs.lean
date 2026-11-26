module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Substitution.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Defs

/-! # Continuation-parameterized queries in selected finite request trees -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree

open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit answer)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite (Expr Assignment)

local notation "U" => (Ty.unit : Ty Empty)

def literal (b : Bool) : Tm signature.Instr := constructorBit b .unit

/-- Choose a continuation by a pure query. Each introduced case binder
weakens both original continuations and the remaining live slots. -/
def choose : {n : Nat} → Expr n → (Fin n → Tm signature.Instr) →
    Region signature.Instr → Region signature.Instr → Region signature.Instr
  | _, .literal b, _, l, r => if b then r else l
  | _, .read i, slots, l, r => .case (slots i) (l.renameVars Nat.succ) (r.renameVars Nat.succ)
  | _, .split lo hi, slots, l, r =>
    let older := fun i => (slots i.succ).rename Nat.succ
    let wl := l.renameVars Nat.succ
    let wr := r.renameVars Nat.succ
    .case (slots 0) (choose lo older wl wr) (choose hi older wl wr)

theorem choose_typed :
    {n : Nat} → (e : Expr n) → {slots : Fin n → Tm signature.Instr} →
      {Γ : VCtx (Ty Empty)} → (∀ i, Tm.HasType Γ (slots i) Bit) →
      {L : LCtx (Ty Empty)} → {l r : Region signature.Instr} →
      ValueBranches Γ l L → ValueBranches Γ r L → ValueBranches Γ (choose e slots l r) L
  | _, .literal false, _, _, _, _, _, _, hl, _ => hl
  | _, .literal true, _, _, _, _, _, _, _, hr => hr
  | _, .read i, _, Γ, typed, _, _, _, hl, hr =>
    .case (typed i) (hl.renameVars (Ren.wk Γ U)) (hr.renameVars (Ren.wk Γ U))
  | _, .split lo hi, _, Γ, typed, _, _, _, hl, hr =>
    let older := fun i => (typed (Fin.succ i)).rename (Ren.wk Γ U)
    let wl := hl.renameVars (Ren.wk Γ U)
    let wr := hr.renameVars (Ren.wk Γ U)
    .case (typed 0) (choose_typed lo older wl wr) (choose_typed hi older wl wr)

def focus (i : Nat) (b : Bool) (j : Nat) : Tm signature.Instr :=
  if j = i then constructorBit b (.var 0) else .var j.succ

theorem focus_typed {Γ : VCtx (Ty Empty)} {i : Nat} (hi : At Γ i Bit) (b : Bool)
    {j : Nat} {A : Ty Empty} (hj : At Γ j A) : Tm.BranchValue (U :: Γ) (focus i b j) A := by
  by_cases e : j = i
  · subst j
    cases Option.some.inj (hj.symm.trans hi)
    simpa only [focus, ite_true] using constructorBit_value b (.var (i := 0) (Γ := U :: Γ) rfl)
  · simpa only [focus, e, ite_false] using Tm.BranchValue.var (i := j.succ) (Γ := U :: Γ) hj

/-- Values stay at their original positions until a real reply inserts a new
slot zero. All lookup evidence is at the exact native context. -/
structure Slots (Γ : VCtx (Ty Empty)) (n : Nat) where
  index : Fin n → Nat
  typed : ∀ i, At Γ (index i) Bit
  distinct : Function.Injective index

def Slots.terms {Γ : VCtx (Ty Empty)} {n : Nat} (slots : Slots Γ n) : Fin n → Tm signature.Instr :=
  fun i => .var (slots.index i)

theorem Slots.term_typed {Γ : VCtx (Ty Empty)} {n : Nat} (slots : Slots Γ n) (i : Fin n) :
    Tm.HasType Γ (slots.terms i) Bit := .var (slots.typed i)

def Slots.bind {Γ : VCtx (Ty Empty)} {n : Nat} (slots : Slots Γ n) : Slots (Bit :: Γ) (n + 1) where
  index := Fin.cases 0 (fun i => (slots.index i).succ)
  typed := Fin.cases rfl (fun i => slots.typed i)
  distinct := by
    intro i j h
    refine Fin.cases (fun h => ?_) (fun a h => ?_) i h
    · exact Fin.cases (fun _ => rfl) (fun _ h => by cases h) j h
    · refine Fin.cases (fun h => ?_) (fun b h => ?_) j h
      · cases h
      · exact congrArg Fin.succ (slots.distinct (Nat.succ.inj h))

def inputSlots : Slots [Bit] 1 :=
  ⟨fun _ => 0, fun _ => rfl, fun {_ _} _ => Subsingleton.elim _ _⟩

/-- The reply tag selects a subtree and both branches receive the actual
payload. A terminal returns a live Bit at one of the ordered exits. -/
inductive Tree : Nat → Type where
  | ret {n : Nat} (right : Bool) (slot : Fin n) : Tree n
  | ask {n : Nat} (label : Bool) (query : Expr n) (left right : Tree (n + 1)) : Tree n

def requestRegion (label b : Bool) (left right : Region signature.Instr) : Region signature.Instr :=
  .case (.op (.ask label) (literal b)) left right

theorem request_typed (label b : Bool) {Γ : VCtx (Ty Empty)} {l r : Region signature.Instr}
    (hl : ValueBranches (Bit :: Γ) l Exits) (hr : ValueBranches (Bit :: Γ) r Exits) :
    ValueBranches Γ (requestRegion label b l r) Exits :=
  .case (.op (constructorBit_value b .unit).hasType) hl hr

def Tree.region : {n : Nat} → Tree n → {Γ : VCtx (Ty Empty)} → Slots Γ n → Region signature.Instr
  | _, .ret right i, _, slots => .br (if right then 1 else 0) (slots.terms i)
  | _, .ask label query l r, _, slots =>
    let left := l.region slots.bind
    let right := r.region slots.bind
    choose query slots.terms (requestRegion label false left right) (requestRegion label true left right)

theorem exit_typed (right : Bool) : At Exits (if right then 1 else 0) Bit := by
  cases right <;> rfl

theorem Tree.typed : {n : Nat} → (t : Tree n) → {Γ : VCtx (Ty Empty)} → (slots : Slots Γ n) →
    ValueBranches Γ (t.region slots) Exits
  | _, .ret right i, _, slots => .br (exit_typed right) (.var (slots.typed i))
  | _, .ask label query l r, _, slots =>
    let left := l.typed slots.bind
    let right := r.typed slots.bind
    choose_typed query slots.term_typed (request_typed label false left right)
      (request_typed label true left right)

/-- The structural key quotes every query in fixed slot order. -/
def Tree.key : {n : Nat} → Tree n → Tree n
  | _, .ret right i => .ret right i
  | n, .ask label query l r => .ask label (Expr.quote n query.eval) l.key r.key

/-- Keep the actual guard. Its branch substitutes the constructor built
from that branch's unit payload before any request takes place. -/
def Tree.guarded (t : Tree 1) : Region signature.Instr :=
  let r := t.region inputSlots
  .case (.var 0) (r.substVars (focus 0 false)) (r.substVars (focus 0 true))

theorem Tree.guarded_typed (t : Tree 1) : ValueBranches [Bit] t.guarded Exits :=
  .case (.var (i := 0) rfl)
    ((t.typed inputSlots).substVars (fun _ _ h => focus_typed (i := 0) rfl false h))
    ((t.typed inputSlots).substVars (fun _ _ h => focus_typed (i := 0) rfl true h))

def Tree.packed (t : Tree 1) :=
  Extension.Singleton.ofRegion Seed t.guarded_typed.packExits

abbrev Reply := Bool × Bool

def event (label query : Bool) (reply : Reply) : Event :=
  ⟨label, query, reply.1, reply.2⟩

abbrev Result := value (packedExitType Exits)
abbrev Word := FreeMonoid Event
abbrev Observation := Except Bool Result × Word

def terminal (right b : Bool) : Result :=
  atExit (answer right b)

/-- Along each admitted reply, keep the exact ordered event, then use its
payload as the newest bit of the selected child. -/
def Tree.outcomes : {n : Nat} → Tree n → Assignment n → Set Observation
  | _, .ret right i, env => {(.ok (terminal right (env i)), 1)}
  | _, .ask label query l r, env =>
    {obs | ∃ (reply : Reply) (tail : Word),
      (obs.1, tail) ∈ (if reply.1 then r.outcomes (env.push reply.2) else l.outcomes (env.push reply.2)) ∧
        FreeMonoid.of (event label (query.eval env) reply) * tail = obs.2}

noncomputable def Tree.observations (t : Tree 1) (input : Bool) :=
  ((denote.map t.packed).of (bit input)).outcomes

namespace Example

/-- The last query is true exactly for a true guard, true first payload,
and false second payload. The newest slot is tested first. -/
def lastQuery : Expr 3 :=
  .split (.split (.literal false) (.read 0)) (.literal false)

def third (altered firstTag secondTag : Bool) : Tree 3 :=
  .ask false (if altered && firstTag && secondTag then .literal false else lastQuery)
    (.ret false 0) (.ret true 0)

def second (altered firstTag : Bool) : Tree 2 :=
  .ask true (.read 0) (third altered firstTag false) (third altered firstTag true)

def program (altered : Bool) : Tree 1 :=
  .ask false (.read 0) (second altered false) (second altered true)

/-- The first reply is right/true and the second is right/false.
The final reply is right/false and still returns at exit one. -/
def observation (last : Bool) : Observation :=
  (.ok (terminal true false),
    FreeMonoid.of (event false true (true, true)) *
      (FreeMonoid.of (event true true (true, false)) *
        (FreeMonoid.of (event false last (true, false)) * 1)))

end Example

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree
