module

public import Silmaril.Semantics.Region.Defs

/-! # First-exit semantics, independent of instruction decoding

`State` includes registers, memory, call stack, guards and frame/interface
state. An adapter must supply the actual transition relation; no implicit
call resumption exists. `Event` is the observed effect alphabet (for example
syscall/foreign-call/UB); `Stop` is the distinguished halt alphabet (for
example return/trap/raise/UB). The adapter chooses which policy represents
traps and UB, and documents it. A step may emit several effects.

The relations below observe the FIRST normal transfer out of support. Later
reentry is irrelevant. Halts inside support, divergence and stuckness are
separate queries. An empty normal-exit allowance does not exclude any of them.
-/

@[expose] public section
namespace Silmaril.Semantics.Region

universe u v w z

structure TransitionSystem (State : Type u) (Lab : Type v) (Event : Type w) (Stop : Type z) where
  pc : State → Lab
  step : State → List Event → State → Prop
  halt : State → Stop → Prop

variable {State : Type u} {Lab : Type v} {Event : Type w} {Stop : Type z}

/-- A finite prefix staying inside support, including both endpoints. -/
inductive Inside (T : TransitionSystem State Lab Event Stop) (U : Lab → Prop) :
    State → List Event → State → Prop where
  | refl {s : State} (inside : U (T.pc s)) : Inside T U s [] s
  | step {s t f : State} {es rest : List Event}
      (inside : U (T.pc s)) (edge : T.step s es t) (tail : Inside T U t rest f) :
      Inside T U s (es ++ rest) f

/-- A nonempty finite run, stopping at its first normal transfer out of U. -/
inductive FirstExit (T : TransitionSystem State Lab Event Stop) (U : Lab → Prop) :
    State → List Event → State → Prop where
  | leave {s t : State} {es : List Event}
      (inside : U (T.pc s)) (edge : T.step s es t) (outside : ¬ U (T.pc t)) :
      FirstExit T U s es t
  | step {s t f : State} {es rest : List Event}
      (inside : U (T.pc s)) (edge : T.step s es t) (tail : FirstExit T U t rest f) :
      FirstExit T U s (es ++ rest) f

/-- Admitted states are explicit; strengthening this domain is sound for a
fixed semantics but may invalidate a separate nonvacuity requirement. -/
def Sound (T : TransitionSystem State Lab Event Stop) (A : State → Prop)
    (U : Lab → Prop) (X : Lab → Prop) : Prop :=
  ∀ s es t, A s → FirstExit T U s es t → X (T.pc t)

/-- Semantic validity adds entry/support and label well-formedness plus an
inhabited admitted domain. It does not require that any normal exit occurs. -/
def Valid (T : TransitionSystem State Lab Event Stop) (wf : Lab → Prop)
    (A : State → Prop) (U : Lab → Prop) (entry : Lab) (X : Finset Lab) : Prop :=
  wf entry ∧ U entry ∧ (∃ s, A s) ∧ (∀ s, A s → T.pc s = entry) ∧
    (∀ l ∈ X, wf l) ∧ Sound T A U (fun l => l ∈ X)

/-- All normal exits; this is the LEAST sound target overapproximation. It
need not be finite or computable. -/
def outward (T : TransitionSystem State Lab Event Stop) (A : State → Prop)
    (U : Lab → Prop) (l : Lab) : Prop :=
  ∃ s es t, A s ∧ FirstExit T U s es t ∧ T.pc t = l

/-- The GREATEST relation of sound rows for fixed T/A/wf/support interpretation.
Validity is semantic, never defined by a partition into locally certified BBs. -/
def greatest {Seg : Type*} (T : TransitionSystem State Lab Event Stop)
    (wf : Lab → Prop) (admit : Lab → State → Prop) (labels : Finset Seg → Lab → Prop) :
    Finset Seg → Lab → Finset Lab → Prop :=
  fun ss e xs => Valid T wf (admit e) (labels ss) e xs

/-- Stronger exact-exit reading: every declared exit is actually reachable.
This is not preserved by arbitrary exit enlargement or entry-domain restriction. -/
def Exact (T : TransitionSystem State Lab Event Stop) (A : State → Prop)
    (U : Lab → Prop) (X : Lab → Prop) : Prop :=
  ∀ l, X l ↔ outward T A U l

/-- Arbitrary state-machine/CFG label-only semantic model. Its interface carrier
can encode entry domains, guard assumptions and frame invariants explicitly. -/
def semanticModel {Img Assum : Type*}
    (systems : Img → Assum → TransitionSystem State Lab Event Stop)
    (wf : Img → Assum → Lab → Prop) (admit : Img → Assum → Lab → State → Prop)
    (supports : Img → Assum → Lab → Lab → Prop) : RegionModel Img Assum Lab :=
  ⟨fun i a e xs => Valid (systems i a) (wf i a) (admit i a e) (supports i a e) e xs⟩

/-- A local certificate includes an invariant on ALL admitted internal states.
Boundary postconditions can carry registers, memory and interface/frame facts. -/
def Local (T : TransitionSystem State Lab Event Stop) (U : Lab → Prop)
    (D B : State → Prop) : Prop :=
  ∀ s es t, D s → U (T.pc s) → T.step s es t →
    (U (T.pc t) → D t) ∧ (¬ U (T.pc t) → B t)

/-- Actual cross-boundary transfers must enter the other child's domain at its
entry label; actual outward transfers must satisfy X. Shared T fixes image,
interface, frame and effect policy. This is a premise to prove, not a heuristic
that subtracts a label from the union of declared exits. -/
def Wiring (T : TransitionSystem State Lab Event Stop) (U V : Lab → Prop)
    (D B E : State → Prop) (entry : Lab) (X : Lab → Prop) : Prop :=
  ∀ s es t, D s → U (T.pc s) → T.step s es t → ¬ U (T.pc t) → B t →
    (V (T.pc t) → T.pc t = entry ∧ E t) ∧ (¬ V (T.pc t) → X (T.pc t))

/-- A wired family can be finite (CFG extraction) or arbitrary. Only actual
steps crossing a child boundary must establish another child's entry domain,
or an outward allowance. This does not assume arbitrary parents are valid. -/
def FamilyWiring {Index : Type*} (T : TransitionSystem State Lab Event Stop)
    (supports : Index → Lab → Prop) (domains boundaries : Index → State → Prop)
    (entries : Index → Lab) (X : Lab → Prop) : Prop :=
  ∀ i s es t, domains i s → supports i (T.pc s) → T.step s es t →
    ¬ supports i (T.pc t) → boundaries i t →
      ((∃ j, supports j (T.pc t)) →
        ∃ j, supports j (T.pc t) ∧ T.pc t = entries j ∧ domains j t) ∧
      ((¬ ∃ j, supports j (T.pc t)) → X (T.pc t))

/-- Structural single entry is separate from admitted-state semantic validity. -/
def SingleEntry (edge : Lab → Lab → Prop) (U : Lab → Prop) (entry : Lab) : Prop :=
  U entry ∧ ∀ x y, edge x y → ¬ U x → U y → y = entry

/-- Infinite internal execution; effects are retained at each step. -/
def Diverges (T : TransitionSystem State Lab Event Stop) (U : Lab → Prop) (s : State) : Prop :=
  ∃ states : Nat → State, ∃ events : Nat → List Event, states 0 = s ∧
    ∀ n, U (T.pc (states n)) ∧ T.step (states n) (events n) (states (n + 1))

/-- A reachable stuck state has neither a transition nor a distinguished halt. -/
def Stuck (T : TransitionSystem State Lab Event Stop) (s : State) : Prop :=
  (∀ es t, ¬ T.step s es t) ∧ ∀ k, ¬ T.halt s k

def ReachableExit (T : TransitionSystem State Lab Event Stop) (A : State → Prop)
    (U : Lab → Prop) (l : Lab) (t : State) : Prop :=
  ∃ s es, A s ∧ FirstExit T U s es t ∧ T.pc t = l

def MayEffect (T : TransitionSystem State Lab Event Stop) (A : State → Prop)
    (U : Lab → Prop) (event : Event) : Prop :=
  ∃ s es t tail f, A s ∧ Inside T U s es t ∧ T.step t tail f ∧ event ∈ es ++ tail

/-- Multi-exit partial correctness includes a separate indexed halt policy.
The postconditions see the trace and final state. Divergence is permitted. -/
def PartialHoare (T : TransitionSystem State Lab Event Stop) (A : State → Prop)
    (U : Lab → Prop) (Q : Lab → List Event → State → Prop)
    (R : Stop → List Event → State → Prop) : Prop :=
  (∀ s es t, A s → FirstExit T U s es t → Q (T.pc t) es t) ∧
  (∀ s es t k, A s → Inside T U s es t → T.halt t k → R k es t)

/-- Internal termination uses accessibility, ruling out infinite internal runs.
Progress separately excludes stuck states. Accepted halts are finishing
outcomes; they are not relabelled as normal exits. -/
def Finishes (T : TransitionSystem State Lab Event Stop) (U : Lab → Prop) (s : State) : Prop :=
  Acc (fun t s => U (T.pc s) ∧ U (T.pc t) ∧ ∃ es, T.step s es t) s ∧
    ∀ es t, Inside T U s es t → (∃ k, T.halt t k) ∨ ∃ tail f, T.step t tail f

def TotalHoare (T : TransitionSystem State Lab Event Stop) (A : State → Prop)
    (U : Lab → Prop) (Q : Lab → List Event → State → Prop)
    (R : Stop → List Event → State → Prop) : Prop :=
  PartialHoare T A U Q R ∧ ∀ s, A s → Finishes T U s

/-- Single-exit specialization still checks every normal outcome's label. -/
def SinglePost (exit : Lab) (Q : List Event → State → Prop) :
    Lab → List Event → State → Prop := fun l es s => l = exit ∧ Q es s

/-- Demonic partial weakest precondition. -/
def wp (T : TransitionSystem State Lab Event Stop) (U : Lab → Prop)
    (Q : Lab → List Event → State → Prop) (R : Stop → List Event → State → Prop)
    (s : State) : Prop := PartialHoare T (fun t => t = s) U Q R

/-- A semantic helper certificate must cover every FIRST exit from admitted
states. Terminator-only coverage is an additional, independent premise. -/
def TargetSound (T : TransitionSystem State Lab Event Stop) (A : State → Prop)
    (U : Lab → Prop) (targets : Targets Lab) : Prop := Sound T A U targets.Allows

def TerminatorCoverage {Term : Type*} (T : TransitionSystem State Lab Event Stop)
    (A : State → Prop) (U : Lab → Prop) (term : Term) (transfer : Term → State → Prop) : Prop :=
  ∀ s es t, A s → FirstExit T U s es t → transfer term t

end Silmaril.Semantics.Region
