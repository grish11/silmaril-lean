module

public import Mathlib.Basic.Rel
public import Silmaril.Semantics.ITree.Kleisli.Defs

/-! Exact single-exchange lowering of indexed weak ITrees over a fixed execution profile. -/

@[expose] public section

namespace Silmaril.Elgot.ITree.Exact

open CategoryTheory

universe u v w z

/-- An indexed event signature. A request/reply signature supplies an event at the
reply type of each request. -/
structure Signature where
  Event : Type u → Type u

/-- The one target request and pure reply projection for a source event. -/
structure Exchange (T : Signature.{u}) (R : Type u) where
  Reply : Type u
  event : T.Event Reply
  project : Reply → R

structure Signature.Hom (S T : Signature.{u}) where
  exchange : {R : Type u} → S.Event R → Exchange T R

instance : Category.{u + 1} Signature.{u} where
  Hom S T := S.Hom T
  id _ := ⟨fun e => ⟨_, e, id⟩⟩
  comp f g := ⟨fun e =>
    let x := f.exchange e
    let y := g.exchange x.event
    ⟨y.Reply, y.event, x.project ∘ y.project⟩⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

namespace Signature.Hom

variable {S T : Signature.{u}}

def layer (f : S ⟶ T) {A : Type v} {X : Type w} {Y : Type z} (lower : X → Y) :
    Visible S.Event A X → Visible T.Event A Y
  | .ret a => .ret a
  | .vis e k =>
    let x := f.exchange e
    .vis x.event (fun r => lower (k (x.project r)))

def approx (f : S ⟶ T) {A : Type v} :
    (n : Nat) → Approx S.Event A n → Approx T.Event A n
  | 0, _ => PUnit.unit
  | n + 1, x => Part.map (f.layer (f.approx n)) x

theorem truncate_approx (f : S ⟶ T) {A : Type v}
    (n : Nat) (x : Approx S.Event A (n + 1)) :
    Approx.truncate n (f.approx (n + 1) x) = f.approx n (Approx.truncate n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [approx, Approx.truncate, Part.map_eq_map, Part.map_map]
    apply congrArg (fun g => Part.map g x)
    funext root
    cases root with
    | ret => rfl
    | vis e k =>
      simp only [Function.comp_apply, layer, Visible.map_vis]
      congr 1
      funext r
      exact ih _

/-- Translate each finite depth, leaving the return type and silent divergence fixed. -/
def lower (f : S ⟶ T) {A : Type v} (t : Tree S.Event A) : Tree T.Event A where
  observe n := f.approx n (t.observe n)
  coherent n := (truncate_approx f n _).trans (congrArg (f.approx n) (t.coherent n))

end Signature.Hom

/-- A fixed profile chooses the environment, shared store, public outputs and stop reasons.
Use a stop type with distinct exit, fault, UB and unsupported tags when observing them. -/
structure Profile where
  Env : Type v
  Store : Type v
  Output : Type v
  Stop : Type v

inductive Completion (P : Profile.{v}) (R : Type u) where
  | reply (value : R) (store : P.Store) (batch : List P.Output)
  | stop (reason : P.Stop) (store : Option P.Store) (batch : List P.Output)

def Completion.map {P : Profile.{v}} {R T : Type u} (project : R → T) :
    Completion P R → Completion P T
  | .reply r w batch => .reply (project r) w batch
  | .stop reason w batch => .stop reason w batch

/-- At a fixed environment and store, a request may have several completions or none. -/
abbrev Kernel (P : Profile.{v}) (S : Signature.{u}) :=
  P.Env → P.Store → {R : Type u} → S.Event R → Completion P R → Prop

def Kernel.reduct {P : Profile.{v}} {S T : Signature.{u}} (f : S ⟶ T) (K : Kernel P T) :
    Kernel P S := fun env store {_} e answer =>
  ∃ concrete, K env store (f.exchange e).event concrete ∧ concrete.map (f.exchange e).project = answer

abbrev Config (P : Profile.{v}) (S : Signature.{u}) (A : Type v) :=
  Tree S.Event A × P.Store

def Config.lower {P : Profile.{v}} {S T : Signature.{u}} {A : Type v} (f : S ⟶ T)
    (s : Config P S A) : Config P T A := (f.lower s.1, s.2)

inductive End (P : Profile.{v}) (A : Type v) where
  | returned (value : A) (store : P.Store)
  | blocked (store : P.Store)
  | stopped (reason : P.Stop) (store : Option P.Store)

/-- Inspect the partial weak root classically, preserving silent bottom. -/
noncomputable def root {S : Signature.{u}} {A : Type v}
    (t : Tree S.Event A) : Option (Visible S.Event A (Tree S.Event A)) := by
  classical
  exact (out t).toOption

variable {S : Signature.{u}} {A : Type v} in
@[simp] theorem root_diverge : root (S := S) (diverge : Tree S.Event A) = none := by
  simp [root, Part.toOption]

variable {S : Signature.{u}} {A : Type v} in
@[simp] theorem root_ret (a : A) : root (S := S) (ret a) = some (.ret a) := by
  simp [root, Part.toOption]

variable {S : Signature.{u}} {A : Type v} in
@[simp] theorem root_vis {R : Type u} (e : S.Event R) (k : R → Tree S.Event A) :
    root (S := S) (vis e k) = some (.vis e k) := by
  simp [root, Part.toOption]

/-- A continuing transition either completes an exchange or silently self-loops. -/
def Step {P : Profile.{v}} {S : Signature.{u}} {A : Type v}
    (K : Kernel P S) (env : P.Env) (s : Config P S A) (batch : List P.Output)
    (s' : Config P S A) : Prop :=
  match root s.1 with
  | none => batch = [] ∧ s' = s
  | some (.ret _) => False
  | some (.vis e k) => ∃ r, K env s.2 e (.reply r s'.2 batch) ∧ s'.1 = k r

/-- A return, a request with no completion, or a stopping completion ends a run. -/
def Finish {P : Profile.{v}} {S : Signature.{u}} {A : Type v}
    (K : Kernel P S) (env : P.Env) (s : Config P S A) (batch : List P.Output)
    (last : End P A) : Prop :=
  match root s.1 with
  | none => False
  | some (.ret a) => batch = [] ∧ last = .returned a s.2
  | some (.vis e _) =>
    (¬ (∃ c, K env s.2 e c)) ∧ batch = [] ∧ last = .blocked s.2 ∨
      ∃ reason store, K env s.2 e (.stop reason store batch) ∧ last = .stopped reason store

inductive Path {P : Profile.{v}} {S : Signature.{u}} {A : Type v}
    (K : Kernel P S) (env : P.Env) : Config P S A → List P.Output → Config P S A → Prop
  | nil (s) : Path K env s [] s
  | cons {s m t batch log} : Step K env s batch m → Path K env m log t →
      Path K env s (batch ++ log) t

def Infinite {P : Profile.{v}} {S : Signature.{u}} {A : Type v}
    (K : Kernel P S) (env : P.Env) (s : Config P S A) (batches : Nat → List P.Output) : Prop :=
  ∃ states : Nat → Config P S A, states 0 = s ∧
    ∀ n, Step K env (states n) (batches n) (states (n + 1))

def outputThrough {V : Type v} (batches : Nat → List V) : Nat → List V
  | 0 => []
  | n + 1 => outputThrough batches n ++ batches n

/-- The log of an actual infinite run, represented by all its finite word prefixes
so that different batch boundaries give the same observation. -/
def infiniteLog {V : Type v} (batches : Nat → List V) : Set (List V) :=
  { word | ∃ n, word <+: outputThrough batches n }

inductive Observation (P : Profile.{v}) (A : Type v) where
  | prefix (log : List P.Output)
  | finished (log : List P.Output) (last : End P A)
  | infinite (log : Set (List P.Output))

def Observes {P : Profile.{v}} {S : Signature.{u}} {A : Type v}
    (K : Kernel P S) (env : P.Env) (s : Config P S A) : Observation P A → Prop
  | .prefix log => ∃ (pathLog : List P.Output) (t : Config P S A),
      Path K env s pathLog t ∧
        (log <+: pathLog ∨ ∃ batch last, Finish K env t batch last ∧ log <+: pathLog ++ batch)
  | .finished log last => ∃ (pathLog : List P.Output) (t : Config P S A) (batch : List P.Output),
      Path K env s pathLog t ∧ Finish K env t batch last ∧ log = pathLog ++ batch
  | .infinite log => ∃ batches, Infinite K env s batches ∧ log = infiniteLog batches

/-- Relate trees to their public observations in one fixed initial context. -/
def observationRelation {P : Profile.{v}} {S : Signature.{u}} {A : Type v}
    (K : Kernel P S) (env : P.Env) (store : P.Store) :
    SetRel (Tree S.Event A) (Observation P A) :=
  { p | Observes K env (p.1, store) p.2 }

structure Sentence (P : Profile.{v}) (S : Signature.{u}) where
  Return : Type v
  test : Tree S.Event Return
  pre : P.Env → P.Store → Prop
  post : P.Env → P.Store → Observation P Return → Prop

def Sentence.lower {P : Profile.{v}} {S T : Signature.{u}} (f : S ⟶ T)
    (φ : Sentence P S) : Sentence P T :=
  ⟨φ.Return, f.lower φ.test, φ.pre, φ.post⟩

def Satisfies {P : Profile.{v}} {S : Signature.{u}} (K : Kernel P S)
    (φ : Sentence P S) : Prop :=
  ∀ env store, φ.pre env store →
    ∀ obs, Observes K env (φ.test, store) obs → φ.post env store obs

end Silmaril.Elgot.ITree.Exact
