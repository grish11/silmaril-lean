module

public import Silmaril.Semantics.TrackA.Concurrency.Defs
public import Silmaril.Semantics.TrackA.Interaction.WeakITree.Defs

/-! Finite store observations for the raw read/write fragment. -/

@[expose] public section

namespace Silmaril.Semantics.Brookes.TreeSC

open TrackA.Interaction
open TrackA.Concurrency (AccessMode Program Shared sequential)

abbrev Store (R : Type) := R → Nat

inductive Request (R : Type) where
  | read (mode : AccessMode) (location : R)
  | write (mode : AccessMode) (location : R) (value : Nat)

def Request.Reply {R : Type} : Request R → Type
  | .read .. => Nat
  | .write .. => Unit

def signature (R : Type) : Signature := ⟨Request R, Request.Reply⟩

/-- One completed component operation, with the actual reply and the stores
immediately before and after the operation. -/
structure Frame (R : Type) where
  exchange : (signature R).Exchange
  before : Store R
  after : Store R

variable {R : Type}

def Frame.event {T : Type} (thread : T) (frame : Frame R) :
    TrackA.Concurrency.Event T Empty R :=
  ⟨thread, match frame.exchange with
    | ⟨.read mode loc, value⟩ => .read mode loc value
    | ⟨.write mode loc value, _⟩ => .write mode loc value⟩

/-- The store law for an exchange is independent of the continuation. -/
def Frame.Valid [DecidableEq R] (frame : Frame R) : Prop :=
  match frame.exchange with
  | ⟨.read _ loc, value⟩ => value = frame.before loc ∧ frame.after = frame.before
  | ⟨.write _ loc value, _⟩ => frame.after = Function.update frame.before loc value

abbrev Gap (R : Type) := Store R → Store R → Prop

/-- A gap can precede each component operation, including the first. Endpoints
are exact after the last operation. An empty prefix leaves its store unchanged. -/
inductive StoreFollows [DecidableEq R] (gap : Gap R) :
    Store R → List (Frame R) → Store R → Prop where
  | nil (s : Store R) : StoreFollows gap s [] s
  | cons {s last : Store R} {frame : Frame R} {frames : List (Frame R)} :
      gap s frame.before → frame.Valid → StoreFollows gap frame.after frames last →
      StoreFollows gap s (frame :: frames) last

variable [DecidableEq R]

/-- A finite prefix follows one tree path and one compatible store history.
Tau and both choice kinds are internal according to Track A's weak policy. -/
def Follows {B : Signature} {A X : Type*} (tree : Coalgebra (signature R) B A X)
    (gap : Gap R) (x : X) (s : Store R) (frames : List (Frame R)) (y : X)
    (last : Store R) : Prop :=
  tree.Follows x (frames.map Frame.exchange) y ∧ StoreFollows gap s frames last

/-- A finished prefix additionally reaches a return along finite silent moves.
The silent suffix leaves the final store unchanged. -/
def Returns {B : Signature} {A X : Type*} (tree : Coalgebra (signature R) B A X)
    (gap : Gap R) (x : X) (s : Store R) (frames : List (Frame R)) (result : A)
    (last : Store R) : Prop :=
  ∃ y z, Follows tree gap x s frames y last ∧ tree.Silent y z ∧ tree z = .ret result

/-- Every finished observation comes from a single root of the existing forest. -/
def ForestReturns {B : Signature} {A I : Type*} (forest : Forest (signature R) B A I)
    (gap : Gap R) (s : Store R) (frames : List (Frame R)) (result : A)
    (last : Store R) : Prop :=
  ∃ i, Returns forest.unfold gap (forest.root i) s frames result last

/-- Removing lock names makes both mutex constructors impossible. Both of
Track A's memory access modes are still available. -/
abbrev Code (R : Type) := Program Empty R

abbrev Tree (R : Type) := WeakITree (signature R) Unit

/-- Interpret the SC syntax using the existing weak ITree constructors. -/
noncomputable def Code.toTree : Code R → Tree R
  | .done => Silmaril.Elgot.ITree.ret ()
  | .load mode loc k =>
      Silmaril.Elgot.ITree.vis (IndexedEvent.request (S := signature R) (Request.read mode loc))
        (fun v => Code.toTree (k v))
  | .store mode loc v k =>
      Silmaril.Elgot.ITree.vis (IndexedEvent.request (S := signature R) (Request.write mode loc v))
        (fun _ => Code.toTree k)
  | .acquire lock _ | .release lock _ => nomatch lock

noncomputable def Code.forest {I : Type*} (code : I → Code R) :
    Forest (signature R) Signature.noChoice Unit I where
  State := Tree R
  unfold := WeakITree.unfold
  root i := (WeakITree.toDelayed (Code.toTree (code i))).root ()

/-- Embed a layer without choice underneath the internal selection. -/
def choiceLayer :
    Node (signature R) Signature.noChoice Unit (Tree R) →
      Node (signature R) Signature.finiteChoice Unit (Option (Tree R))
  | .ret a => .ret a
  | .tau next => .tau (some next)
  | .vis q next => .vis q fun r => some (next r)
  | .branch _ shape _ => nomatch shape

/-- The root chooses a whole component program once. Each selected tree uses
the weak ITree adapter, and its subsequent exchanges cannot revisit the root.
Primitive scheduler selections do not use this operation. -/
noncomputable def choiceUnfold {n : Nat} (kind : ChoiceKind) (code : Fin n → Code R) :
    Coalgebra (signature R) Signature.finiteChoice Unit (Option (Tree R))
  | none => .branch kind n fun i => some (code i).toTree
  | some tree => choiceLayer (WeakITree.unfold tree)

noncomputable def choose {n : Nat} (kind : ChoiceKind) (code : Fin n → Code R) :
    CTree (signature R) Unit where
  State := Option (Tree R)
  unfold := choiceUnfold kind code
  root _ := none

/-- One independently replayable machine action at the frame's supplied
pre-store, using the actual Track A sequential primitive. -/
def MachineStep (p : Code R) (frame : Frame R) (q : Code R) : Prop :=
  (sequential ()).Tr (p, Shared.initial frame.before) (frame.event ())
    (q, Shared.initial frame.after)

/-- With an open component, the gap relation describes admissible changes by
its environment. With a closed singleton scheduler, use equality. -/
inductive MachineFollows (gap : Gap R) :
    Code R → Store R → List (Frame R) → Code R → Store R → Prop where
  | nil (p : Code R) (s : Store R) : MachineFollows gap p s [] p s
  | cons {p q lastCode : Code R} {s last : Store R}
      {frame : Frame R} {frames : List (Frame R)} :
      gap s frame.before → MachineStep p frame q →
      MachineFollows gap q frame.after frames lastCode last →
      MachineFollows gap p s (frame :: frames) lastCode last

end Silmaril.Semantics.Brookes.TreeSC
