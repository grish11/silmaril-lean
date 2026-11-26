module

public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.GroupTheory.Congruence.Hom

/-! # Finite concurrent traces

A trace is a finite word modulo adjacent swaps of independent letters. Synchronizations
carry a literal participant list. Membership in that list controls swaps with events.
-/

@[expose] public section

namespace Silmaril.Semantics.ConcurrentTrace

universe u v u' v' w

/-- An event belongs to one thread. A synchronization records its participant list. -/
inductive Letter (Thread : Type u) (Event : Type v) where
  | event (thread : Thread) (value : Event)
  | sync (participants : List Thread)

abbrev Word (Thread : Type u) (Event : Type v) := List (Letter Thread Event)

variable {T : Type u} {E : Type v} {T' : Type u'} {E' : Type v'}

namespace Letter

/-- The three ordered forms of independent pairs. Every pair of sync letters is dependent. -/
inductive Independent : Letter T E → Letter T E → Prop where
  | events {t u : T} {e f : E} : t ≠ u → Independent (.event t e) (.event u f)
  | eventSync {t : T} {e : E} {ts : List T} : t ∉ ts → Independent (.event t e) (.sync ts)
  | syncEvent {t : T} {e : E} {ts : List T} : t ∉ ts → Independent (.sync ts) (.event t e)

/-- Map the thread IDs and the event payload, retaining the participant list structure. -/
def map (f : T → T') (g : E → E') : Letter T E → Letter T' E'
  | .event t e => .event (f t) (g e)
  | .sync ts => .sync (ts.map f)

end Letter

/-- The pairs of length-two words generating the congruence. -/
inductive Swap : FreeMonoid (Letter T E) → FreeMonoid (Letter T E) → Prop where
  | pair {a b : Letter T E} : a.Independent b → Swap (.ofList [a, b]) (.ofList [b, a])

/-- The least concatenation congruence containing the generating swaps. -/
def congruence (T : Type u) (E : Type v) : Con (FreeMonoid (Letter T E)) := conGen Swap

/-- Equivalence of raw words under the swap congruence. -/
def Equivalent (x y : Word T E) : Prop := congruence T E (.ofList x) (.ofList y)

/-- A finite concurrent trace with the inherited monoid structure. -/
abbrev Trace (T : Type u) (E : Type v) := (congruence T E).Quotient

/-- The class of a word. Multiplication of classes is induced by concatenation. -/
def ofWord (word : Word T E) : Trace T E := (congruence T E).mk' (.ofList word)

/-- The trace containing a single letter. -/
def singleton (letter : Letter T E) : Trace T E := ofWord [letter]

@[simp] theorem ofWord_nil : ofWord ([] : Word T E) = 1 := rfl

theorem ofWord_append (x y : Word T E) : ofWord (x ++ y) = ofWord x * ofWord y := rfl

theorem ofWord_eq_iff (x y : Word T E) : ofWord x = ofWord y ↔ Equivalent x y :=
  (congruence T E).eq

theorem swap {a b : Letter T E} (h : a.Independent b) :
    singleton a * singleton b = singleton b * singleton a := by
  apply (congruence T E).eq.mpr
  exact Con.le_conGen (r := Swap) _ _ (Swap.pair h)

theorem ofWord_surjective : Function.Surjective (ofWord (T := T) (E := E)) := by
  intro x
  obtain ⟨w, rfl⟩ := Con.mk'_surjective (c := congruence T E) x
  exact ⟨w.toList, rfl⟩

/-- Interpret letters in a monoid where images of independent letters commute. -/
def lift {M : Type w} [Monoid M] (f : Letter T E → M)
    (commutes : ∀ ⦃a b⦄, a.Independent b → f a * f b = f b * f a) : Trace T E →* M :=
  (congruence T E).lift (FreeMonoid.lift f) (Con.conGen_le.mpr (by
    rintro _ _ ⟨h⟩
    simpa [Con.ker_apply, FreeMonoid.lift_ofList] using commutes h))

@[simp] theorem lift_singleton {M : Type w} [Monoid M] (f : Letter T E → M)
    (h : ∀ ⦃a b⦄, a.Independent b → f a * f b = f b * f a) (a : Letter T E) :
    lift f h (singleton a) = f a :=
  FreeMonoid.lift_eval_of f a

/-- Raw words admit arbitrary pointwise maps. -/
def mapWord (f : T → T') (g : E → E') (word : Word T E) : Word T' E' :=
  word.map (Letter.map f g)

/-- The given thread map must be injective on its domain. A subtype of thread IDs
can serve as the source type when only those IDs are in use. -/
def mapTrace (f : T → T') (hf : Function.Injective f) (g : E → E') : Trace T E →* Trace T' E' :=
  lift (singleton ∘ Letter.map f g) (by
    intro a b h
    apply swap
    cases h with
    | events h => exact .events (fun heq => h (hf heq))
    | eventSync h => exact .eventSync (h ∘ (List.mem_map_of_injective hf).mp)
    | syncEvent h => exact .syncEvent (h ∘ (List.mem_map_of_injective hf).mp))

/-- Rename threads across types by an injective function. -/
def rename (f : T → T') (hf : Function.Injective f) : Trace T E →* Trace T' E :=
  mapTrace f hf id

/-- Change event payloads by an arbitrary function. -/
def mapEvents (g : E → E') : Trace T E →* Trace T E' :=
  mapTrace id Function.injective_id g

/-- Lift a sequential event word into the current thread. -/
def liftThread (thread : T) : FreeMonoid E →* Trace T E :=
  FreeMonoid.lift (fun e => singleton (.event thread e))

/-- A thread sees its own event payloads and the full list of each sync it participates in. -/
inductive LocalLetter (Thread : Type u) (Event : Type v) where
  | event (value : Event)
  | sync (participants : List Thread)

/-- Map the fields retained by the local observation. -/
def LocalLetter.map (f : T → T') (g : E → E') : LocalLetter T E → LocalLetter T' E'
  | .event e => .event (g e)
  | .sync ts => .sync (ts.map f)

/-- Per-letter observation by one thread. -/
def observeLetter [DecidableEq T] (thread : T) : Letter T E → FreeMonoid (LocalLetter T E)
  | .event t e => if t = thread then .of (.event e) else 1
  | .sync ts => if thread ∈ ts then .of (.sync ts) else 1

/-- Local observation in order, including participating synchronizations. -/
def observe [DecidableEq T] (thread : T) : Trace T E →* FreeMonoid (LocalLetter T E) :=
  lift (observeLetter thread) (by
    intro a b h
    cases h with
    | @events t u e f h =>
      by_cases ht : t = thread
      · subst t
        simp [observeLetter, Ne.symm h]
      · simp [observeLetter, ht]
    | @eventSync t e ts h =>
      by_cases ht : t = thread
      · subst t
        simp [observeLetter, h]
      · simp [observeLetter, ht]
    | @syncEvent t e ts h =>
      by_cases ht : t = thread
      · subst t
        simp [observeLetter, h]
      · simp [observeLetter, ht])

/-- The event-only observation explicitly erases the synchronization markers. -/
def events [DecidableEq T] (thread : T) : Trace T E →* FreeMonoid E :=
  (FreeMonoid.lift fun l => match l with
    | .event e => .of e
    | .sync _ => 1).comp (observe thread)

/-- The global synchronization observation retains every participant list in order,
including empty lists. It erases all event letters. -/
def syncs : Trace T E →* FreeMonoid (List T) :=
  lift (fun l => match l with
    | .event .. => 1
    | .sync ts => .of ts) (by intro a b h; cases h <;> simp)

/-- A word language is saturated if it contains every representative of each of its traces. -/
def Saturated (s : Set (Word T E)) : Prop :=
  ∀ ⦃x y⦄, x ∈ s → Equivalent x y → y ∈ s

/-- Send a word language to the set of trace classes it meets. -/
def toTraces (s : Set (Word T E)) : Set (Trace T E) := ofWord '' s

/-- Take all representatives of the traces in a language. -/
def ofTraces (s : Set (Trace T E)) : Set (Word T E) := ofWord ⁻¹' s

/-- Close a word language under the swap congruence. -/
def saturate (s : Set (Word T E)) : Set (Word T E) := ofTraces (toTraces s)

/-- Sequential composition of word languages, closed under the swap congruence. -/
def concat (s t : Set (Word T E)) : Set (Word T E) := saturate (Set.image2 List.append s t)

end Silmaril.Semantics.ConcurrentTrace
