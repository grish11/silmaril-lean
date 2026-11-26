module

public import Init

/-! Numbered-page computations and their completion semantics. -/

@[expose] public section
namespace Silmaril.Semantics.Page

universe u v w a b

/-- The ordinary state of a page. `undef` is allocated storage awaiting initialization. -/
inductive Slot (Content : Type v) where
  | absent
  | undef
  | defined (content : Content)

def Slot.value {Content : Type v} : Slot Content → Option Content
  | .defined value => some value
  | _ => none

/-- A store exposes page lookup and a point update. Other components of `Memory`
remain available to clients through their own invariants and observations. -/
structure Store (Id : Type u) (Content : Type v) (Memory : Type w) where
  lookup : Memory → Id → Slot Content
  set : Memory → Id → Slot Content → Memory
  lookup_set_same (m : Memory) (p : Id) (s : Slot Content) : lookup (set m p s) p = s
  lookup_set_other (m : Memory) (p q : Id) (s : Slot Content) :
    q ≠ p → lookup (set m p s) q = lookup m q

def Store.domain {Id Content Memory} (store : Store Id Content Memory) (m : Memory) (p : Id) : Prop :=
  store.lookup m p ≠ .absent

/-- A pointwise override, used both in the concrete store and in completed images. -/
def override {Id : Type u} {Value : Type v} [DecidableEq Id]
    (image : Id → Value) (p : Id) (value : Value) : Id → Value :=
  fun q => if q = p then value else image q

abbrev MapMemory (Id : Type u) (Content : Type v) := Id → Slot Content

def mapStore (Id : Type u) (Content : Type v) [DecidableEq Id] :
    Store Id Content (MapMemory Id Content) where
  lookup m p := m p
  set := override
  lookup_set_same := by intros; simp [override]
  lookup_set_other := by intros; simp_all [override]

/-- Eligibility can depend on the current allocated domain, for instance to
reserve IDs or impose a quota. All eligible absent pages are possible choices. -/
structure Model (Id : Type u) (Content : Type v) (Memory : Type w) where
  store : Store Id Content Memory
  eligible : (Id → Prop) → Id → Prop

variable {Id : Type u} {Content : Type v} {Memory : Type w}
variable {α : Type a} {β : Type b}

def Model.Fresh (M : Model Id Content Memory) (m : Memory) (p : Id) : Prop :=
  M.store.lookup m p = .absent ∧ M.eligible (M.store.domain m) p

inductive Op (Id : Type u) (Content : Type v) where
  | read (page : Id)
  | write (page : Id) (value : Content)
  | allocate
  | deallocate (page : Id)

inductive Reply : Op Id Content → Type (max u v) where
  | value {p : Id} (value : Content) : Reply (.read p)
  | written {p : Id} {value : Content} : Reply (.write p value)
  | allocated (page : Option Id) : Reply (.allocate : Op Id Content)
  | deallocated {p : Id} : Reply (.deallocate (Content := Content) p)

/-- Page effects, demonic binary choice and an explicit divergent branch. -/
inductive Program (Id : Type u) (Content : Type v) (α : Type a) where
  | pure (value : α)
  | call (op : Op Id Content) (next : Reply op → Program Id Content α)
  | choose (left right : Program Id Content α)
  | diverge

namespace Program

def bind (p : Program Id Content α) (next : α → Program Id Content β) : Program Id Content β :=
  match p with
  | .pure value => next value
  | .call op k => .call op (fun reply => (k reply).bind next)
  | .choose left right => .choose (left.bind next) (right.bind next)
  | .diverge => .diverge

instance : Bind (Program Id Content) := ⟨bind⟩
instance : Pure (Program Id Content) := ⟨.pure⟩

def read (p : Id) : Program Id Content Content := .call (.read p) fun
  | .value value => .pure value

def write (p : Id) (value : Content) : Program Id Content Unit :=
  .call (.write p value) fun _ => .pure ()

def allocate : Program Id Content (Option Id) := .call .allocate fun
  | .allocated page => .pure page

def deallocate (p : Id) : Program Id Content Unit := .call (.deallocate p) fun _ => .pure ()

end Program

/-- Semantic UB records the invalid operation, including a distinct UNDEF read. -/
inductive Fault (Id : Type u) where
  | readAbsent (page : Id)
  | readUndef (page : Id)
  | writeAbsent (page : Id)
  | deallocateAbsent (page : Id)

inductive Stop (Id : Type u) where
  | ub (fault : Fault Id)
  | diverged

inductive Exit (Id : Type u) (Memory : Type w) (α : Type a) where
  | returned (value : α) (memory : Memory)
  | stopped (reason : Stop Id)

/-- Only successful updates contribute an edit. The log carries no filled-in values. -/
inductive Edit (Id : Type u) (Content : Type v) where
  | allocate (page : Id)
  | write (page : Id) (value : Content)
  | deallocate (page : Id)

inductive Action (Memory : Type w) (op : Op Id Content) where
  | ok (reply : Reply op) (memory : Memory) (edit : Option (Edit Id Content))
  | ub (fault : Fault Id)

inductive Step (M : Model Id Content Memory) : (op : Op Id Content) → Memory → Action Memory op → Prop
  | readDefined {m p value} : M.store.lookup m p = .defined value →
      Step M (.read p) m (.ok (.value value) m none)
  | readUndef {m p} : M.store.lookup m p = .undef → Step M (.read p) m (.ub (.readUndef p))
  | readAbsent {m p} : M.store.lookup m p = .absent → Step M (.read p) m (.ub (.readAbsent p))
  | write {m p value} : M.store.domain m p →
      Step M (.write p value) m (.ok .written (M.store.set m p (.defined value)) (some (.write p value)))
  | writeAbsent {m p value} : M.store.lookup m p = .absent →
      Step M (.write p value) m (.ub (.writeAbsent p))
  | allocate {m p} : M.Fresh m p →
      Step M .allocate m (.ok (.allocated (some p)) (M.store.set m p .undef) (some (.allocate p)))
  | allocateNone {m} : (∀ p, ¬ M.Fresh m p) → Step M .allocate m (.ok (.allocated none) m none)
  | deallocate {m p} : M.store.domain m p →
      Step M (.deallocate p) m (.ok .deallocated (M.store.set m p .absent) (some (.deallocate p)))
  | deallocateAbsent {m p} : M.store.lookup m p = .absent →
      Step M (.deallocate p) m (.ub (.deallocateAbsent p))

/-- Maximal branch outcomes. A branch ending at `diverge` has a divergence outcome;
invalid page operations stop with UB and never invoke the continuation. -/
inductive Run (M : Model Id Content Memory) : Program Id Content α → Memory →
    List (Edit Id Content) → Exit Id Memory α → Prop
  | pure {m value} : Run M (.pure value) m [] (.returned value m)
  | diverge {m} : Run M .diverge m [] (.stopped .diverged)
  | left {l r m edits out} : Run M l m edits out → Run M (.choose l r) m edits out
  | right {l r m edits out} : Run M r m edits out → Run M (.choose l r) m edits out
  | call {op next m reply m' edit edits out} :
      Step M op m (.ok reply m' edit) → Run M (next reply) m' edits out →
      Run M (.call op next) m (edit.toList ++ edits) out
  | ub {op next m fault} : Step M op m (.ub fault) → Run M (.call op next) m [] (.stopped (.ub fault))

abbrev Image (Id : Type u) (Content : Type v) := Id → Option Content

def Slot.CompletedBy (slot : Slot Content) (fill : Option Content) : Prop :=
  match slot with
  | .absent => fill = none
  | .undef => ∃ value, fill = some value
  | .defined value => fill = some value

/-- Exactly the allocated domain has values. Defined source values are preserved. -/
def Completion (M : Model Id Content Memory) (m : Memory) (image : Image Id Content) : Prop :=
  ∀ p, (M.store.lookup m p).CompletedBy (image p)

def FullyDefined (M : Model Id Content Memory) (m : Memory) : Prop :=
  ∀ p, M.store.lookup m p ≠ .undef

def definedImage (M : Model Id Content Memory) (m : Memory) : Image Id Content :=
  fun p => (M.store.lookup m p).value

/-- Fill each new allocation once, overwrite on write, and discard on deallocation.
The next allocation of the same ID may receive a different value. -/
def Edit.Apply [DecidableEq Id] : Edit Id Content → Image Id Content → Image Id Content → Prop
  | .allocate p, image, next => ∃ value, next = override image p (some value)
  | .write p value, image, next => next = override image p (some value)
  | .deallocate p, image, next => next = override image p none

inductive Replay [DecidableEq Id] : List (Edit Id Content) → Image Id Content → Image Id Content → Prop
  | nil {image} : Replay [] image image
  | cons {edit edits image next final} : edit.Apply image next → Replay edits next final →
      Replay (edit :: edits) image final

/-- Ordinary total correctness. Every maximal branch must return and satisfy `post`. -/
def Correct (M : Model Id Content Memory) (p : Program Id Content α) (m : Memory)
    (post : α → Memory → Prop) : Prop :=
  ∀ edits out, Run M p m edits out → match out with
    | .returned value final => post value final
    | .stopped _ => False

/-- Total correctness from a fixed image. Every ordinary branch must terminate
normally, admit a replay, and satisfy `post` for every replay. -/
def CorrectFrom [DecidableEq Id] (M : Model Id Content Memory) (p : Program Id Content α)
    (m : Memory) (image : Image Id Content) (post : α → Memory → Image Id Content → Prop) : Prop :=
  ∀ edits out, Run M p m edits out → match out with
    | .returned value final => (∃ finalImage, Replay edits image finalImage) ∧
        ∀ finalImage, Replay edits image finalImage → post value final finalImage
    | .stopped _ => False

/-- A single witness precedes all execution choices and fresh allocation fills. -/
def ExistsCorrect [DecidableEq Id] (M : Model Id Content Memory) (p : Program Id Content α)
    (m : Memory) (post : α → Memory → Image Id Content → Prop) : Prop :=
  ∃ image, Completion M m image ∧ CorrectFrom M p m image post

/-- Every initial completion works, and at least one must exist. -/
def ForallCorrect [DecidableEq Id] (M : Model Id Content Memory) (p : Program Id Content α)
    (m : Memory) (post : α → Memory → Image Id Content → Prop) : Prop :=
  (∃ image, Completion M m image) ∧
    ∀ image, Completion M m image → CorrectFrom M p m image post

end Silmaril.Semantics.Page
