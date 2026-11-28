module

public import Silmaril.Semantics.Brookes.Defs
public import Silmaril.Semantics.Brookes.TreeSC.Defs

/-! Brookes closure of finite completed read/write observations. -/

@[expose] public section

namespace Silmaril.Semantics.Brookes.TreeSC

open TrackA.Interaction

variable {R : Type} [DecidableEq R]
variable {B : Signature} {A C X I : Type*}

/-- The standard Brookes gap imposes no constraint on the environment's store. -/
def openGap : Gap R := fun _ _ => True

/-- Only a witnessed return contributes a seed. The empty frame list represents
a successful return by an identity transition at its store. -/
def treeBehavior (tree : Coalgebra (signature R) B A X) (root : X) : Behavior (Store R) A :=
  Behavior.generate fun word result =>
    ∃ initial frames last, Returns tree openGap root initial frames result last ∧
      returnTrace initial frames = word

def forestBehavior (forest : Forest (signature R) B A I) : Behavior (Store R) A :=
  Behavior.generate fun word result =>
    ∃ initial frames last, ForestReturns forest openGap initial frames result last ∧
      returnTrace initial frames = word

def machineBehavior (code : Code R) : Behavior (Store R) Unit :=
  Behavior.generate fun word _ =>
    ∃ initial frames last, MachineFollows openGap code initial frames .done last ∧
      returnTrace initial frames = word

/-- The atomic load replies with the value in the transition's pre-store. -/
def readBehavior (loc : R) : Behavior (Store R) Nat :=
  Behavior.atomic fun s t reply => t = s ∧ reply = s loc

def writeBehavior (loc : R) (value : Nat) : Behavior (Store R) Unit :=
  Behavior.atomic fun s t _ => t = Function.update s loc value

/-- Denotation of the lock-free Track A syntax, with open joins at every bind. -/
def Code.denote : Code R → Behavior (Store R) Unit
  | .done => Behavior.ret ()
  | .load _ loc next => (readBehavior loc).bind fun reply => Code.denote (next reply)
  | .store _ loc value next => (writeBehavior loc value).bind fun _ => Code.denote next
  | .acquire lock _ | .release lock _ => nomatch lock

/-- Run the second program after every successful return of the first. -/
def Code.seq (first second : Code R) : Code R :=
  match first with
  | .done => second
  | .load mode loc next => .load mode loc fun reply => Code.seq (next reply) second
  | .store mode loc value next => .store mode loc value (Code.seq next second)
  | .acquire lock _ | .release lock _ => nomatch lock

/-- Existential union of already saturated behaviors. -/
def behaviorUnion (branch : I → Behavior (Store R) A) : Behavior (Store R) A where
  accepts word result := ∃ i, (branch i).accepts word result
  nonempty := by
    rintro _ _ ⟨i, h⟩
    exact (branch i).nonempty h
  stable := by
    rintro _ _ _ ⟨i, h⟩ step
    exact ⟨i, (branch i).stable h step⟩

/-- Map only terminal values, preserving the existing coalgebra's state,
choice, requests and reply-selected continuations. -/
def mapReturns (f : A → C) (tree : Coalgebra (signature R) B A X) :
    Coalgebra (signature R) B C X := fun x =>
  match tree x with
  | .ret a => .ret (f a)
  | .tau next => .tau next
  | .vis q next => .vis q next
  | .branch kind shape next => .branch kind shape next

/-- Direct image of the accepted terminal values. -/
def mapBehavior (f : A → C) (behavior : Behavior (Store R) A) : Behavior (Store R) C where
  accepts word result := ∃ a, f a = result ∧ behavior.accepts word a
  nonempty := by
    rintro _ _ ⟨_, _, h⟩
    exact behavior.nonempty h
  stable := by
    rintro _ _ _ ⟨a, eq, h⟩ step
    exact ⟨a, eq, behavior.stable h step⟩

end Silmaril.Semantics.Brookes.TreeSC
