module

public import Silmaril.Formats.JsonEvents.Defs
public import Silmaril.Semantics.StreamBounds.Thms
import Silmaril.Proofs.Formats.JsonEvents.Basic

/-!
# JSON event streams and JSON trees: lemmas

* `ofEvents?_toEvents`, `toEvents_of_ofEvents?`: the decoder inverts the encoding on exactly
  the well-formed streams. Hence `Tree.toEvents_injective`, `mem_language_iff`, a `Decidable`
  instance, and `equivLanguage : Tree K S ≃ language K S`;
* `toEvents_mem_depthBound_iff`: the generic depth bound of `Silmaril.Streams` over events
  (`DepthBound Event.kind d`, a safety property over prefixes) holds exactly when the tree
  has `Tree.depth ≤ d`. So a streaming consumer that tracks depth on events enforces the
  format-specific depth bound, prefix by prefix;
* examples.

Stable API for interface bridges: `Tree`, `Event`, `Event.kind`, `Tree.toEvents`,
`ofEvents?`, `language`, `equivLanguage`, `Tree.depth`, `toEvents_mem_depthBound_iff`.
-/

@[expose] public section

namespace Silmaril.Formats.JsonEvents

universe u v

variable {K : Type u} {S : Type v}

theorem ofEvents?_toEvents (t : Tree K S) : ofEvents? t.toEvents = some t :=
  Silmaril.Proofs.Formats.JsonEvents.ofEvents?_toEvents t

theorem toEvents_of_ofEvents? {es : List (Event K S)} {t : Tree K S}
    (h : ofEvents? es = some t) : t.toEvents = es :=
  Silmaril.Proofs.Formats.JsonEvents.toEvents_of_ofEvents? h

theorem ofEvents?_eq_some_iff {es : List (Event K S)} {t : Tree K S} :
    ofEvents? es = some t ↔ t.toEvents = es :=
  ⟨toEvents_of_ofEvents?, fun h => h ▸ ofEvents?_toEvents t⟩

theorem Tree.toEvents_injective : Function.Injective (Tree.toEvents : Tree K S → _) :=
  fun t t' h => Option.some.inj ((ofEvents?_toEvents t).symm.trans (h ▸ ofEvents?_toEvents t'))

theorem mem_language_iff {es : List (Event K S)} : es ∈ language K S ↔ (ofEvents? es).isSome := by
  constructor
  · rintro ⟨t, rfl⟩; simp [ofEvents?_toEvents]
  · intro h
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h
    exact ⟨t, toEvents_of_ofEvents? ht⟩

instance language.decidableMem (es : List (Event K S)) : Decidable (es ∈ language K S) :=
  decidable_of_iff _ mem_language_iff.symm

/-- Trees are in bijection with well-formed event streams. -/
def equivLanguage : Tree K S ≃ {es : List (Event K S) // es ∈ language K S} where
  toFun t := ⟨t.toEvents, t, rfl⟩
  invFun es := (ofEvents? es.1).get (mem_language_iff.mp es.2)
  left_inv t := by simp [ofEvents?_toEvents]
  right_inv es := Subtype.ext (toEvents_of_ofEvents? (Option.some_get _).symm)

/-- The generic event-level depth bound is the format-specific tree depth. -/
theorem toEvents_mem_depthBound_iff (t : Tree K S) (d : Nat) :
    t.toEvents ∈ Silmaril.Streams.DepthBound Event.kind d ↔ t.depth ≤ d :=
  Silmaril.Proofs.Formats.JsonEvents.toEvents_mem_depthBound_iff t d

/-! ## Examples, with string keys and natural-number scalars -/

section Examples

/-- `{"a":[1,[]],"a":2}`, duplicate key kept. -/
def sample : Tree String Nat :=
  .object [("a", .array [.scalar 1, .array []]), ("a", .scalar 2)]

example : sample.toEvents = [.beginObject, .key "a", .beginArray, .scalar 1, .beginArray,
    .endArray, .endArray, .key "a", .scalar 2, .endObject] := rfl
example : sample.depth = 3 := by decide
example : sample.toEvents ∈ Silmaril.Streams.DepthBound Event.kind 3 :=
  (toEvents_mem_depthBound_iff sample 3).mpr (by decide)
example : sample.toEvents ∉ Silmaril.Streams.DepthBound Event.kind 2 :=
  fun h => absurd ((toEvents_mem_depthBound_iff sample 2).mp h) (by decide)
-- Ill-formed streams: unclosed, a key outside an object, a missing key, two values,
-- a stray close, a missing value.
example : ([.beginArray] : List (Event String Nat)) ∉ language String Nat := by decide
example : ([.key "a", .scalar 1] : List (Event String Nat)) ∉ language String Nat := by decide
example : ([.beginObject, .scalar 1, .endObject] : List (Event String Nat)) ∉
    language String Nat := by decide
example : ([.scalar 1, .scalar 2] : List (Event String Nat)) ∉ language String Nat := by decide
example : ([.endArray] : List (Event String Nat)) ∉ language String Nat := by decide
example : ([.beginObject, .key "a", .endObject] : List (Event String Nat)) ∉
    language String Nat := by decide
example : ([] : List (Event String Nat)) ∉ language String Nat := by decide
example : ([.beginObject, .key "a", .beginArray, .endArray, .endObject] :
    List (Event String Nat)) ∈ language String Nat := by decide

end Examples

end Silmaril.Formats.JsonEvents

end
