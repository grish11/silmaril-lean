module

public import Silmaril.Formats.JsonEvents.Defs
public import Silmaril.Semantics.StreamBounds.Thms

/-! # Proofs: JSON event streams and trees (`Silmaril.Formats.JsonEvents.Thms`) -/

@[expose] public section

namespace Silmaril.Proofs.Formats.JsonEvents

open Silmaril.Formats.JsonEvents

universe u v

variable {K : Type u} {S : Type v}

/-! ## Decoding inverts encoding -/

theorem toEvents_length_pos (t : Tree K S) : 1 ≤ t.toEvents.length := by
  cases t <;> simp [Tree.toEvents]

mutual

theorem parseValue_toEvents (t : Tree K S) :
    ∀ n r, 2 * t.toEvents.length + 1 ≤ n → parseValue n (t.toEvents ++ r) = some (t, r) := by
  intro n r hn
  match t with
  | .scalar s =>
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rfl
  | .array items =>
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [Tree.toEvents, List.length_cons, List.length_append, List.length_nil] at hn
    simp only [Tree.toEvents, List.cons_append, List.append_assoc, List.nil_append, parseValue]
    rw [parseItems_itemsEvents items k r (by omega)]; rfl
  | .object members =>
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [Tree.toEvents, List.length_cons, List.length_append, List.length_nil] at hn
    simp only [Tree.toEvents, List.cons_append, List.append_assoc, List.nil_append, parseValue]
    rw [parseMembers_membersEvents members k r (by omega)]; rfl

theorem parseItems_itemsEvents (ts : List (Tree K S)) :
    ∀ n r, 2 * (itemsEvents ts).length + 2 ≤ n →
      parseItems n (itemsEvents ts ++ .endArray :: r) = some (ts, r) := by
  intro n r hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  match ts with
  | [] => rfl
  | t :: ts =>
    simp only [itemsEvents, List.length_append] at hn
    have := toEvents_length_pos t
    have hv := parseValue_toEvents t k (itemsEvents ts ++ .endArray :: r) (by omega)
    have hi := parseItems_itemsEvents ts k r (by omega)
    have key : parseItems (k + 1) (t.toEvents ++ (itemsEvents ts ++ .endArray :: r)) =
        (parseValue k (t.toEvents ++ (itemsEvents ts ++ .endArray :: r))).bind fun p =>
          (parseItems k p.2).map fun q => (p.1 :: q.1, q.2) := by
      cases t <;> simp [Tree.toEvents, parseItems]
    simp only [itemsEvents, List.append_assoc, key, hv, Option.bind_some, hi, Option.map_some]

theorem parseMembers_membersEvents (ms : List (K × Tree K S)) :
    ∀ n r, 2 * (membersEvents ms).length + 2 ≤ n →
      parseMembers n (membersEvents ms ++ .endObject :: r) = some (ms, r) := by
  intro n r hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  match ms with
  | [] => rfl
  | (key, t) :: ms =>
    simp only [membersEvents, List.length_cons, List.length_append] at hn
    have := toEvents_length_pos t
    have hv := parseValue_toEvents t k (membersEvents ms ++ .endObject :: r) (by omega)
    have hm := parseMembers_membersEvents ms k r (by omega)
    simp only [membersEvents, List.cons_append, List.append_assoc, parseMembers, hv,
      Option.bind_some, hm, Option.map_some]

end

/-! ## Decoding is sound -/

mutual

theorem parseValue_sound : ∀ (n : Nat) (es : List (Event K S)) (t : Tree K S) (r : List (Event K S)),
    parseValue n es = some (t, r) → es = t.toEvents ++ r
  | 0, _, _, _, h => by simp [parseValue] at h
  | _ + 1, [], _, _, h => by simp [parseValue] at h
  | n + 1, e :: es, t, r, h => by
    cases e with
    | scalar s =>
      simp only [parseValue, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    | beginArray =>
      simp only [parseValue, Option.map_eq_some_iff] at h
      obtain ⟨⟨xs, r'⟩, hp, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [parseItems_sound n es xs r' hp]
      simp [Tree.toEvents]
    | beginObject =>
      simp only [parseValue, Option.map_eq_some_iff] at h
      obtain ⟨⟨ms, r'⟩, hp, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [parseMembers_sound n es ms r' hp]
      simp [Tree.toEvents]
    | endArray | key _ | endObject => simp [parseValue] at h

theorem parseItems_sound : ∀ (n : Nat) (es : List (Event K S)) (ts : List (Tree K S))
    (r : List (Event K S)), parseItems n es = some (ts, r) → es = itemsEvents ts ++ .endArray :: r
  | 0, _, _, _, h => by simp [parseItems] at h
  | n + 1, es, ts, r, h => by
    have key : (∃ r', es = .endArray :: r' ∧ ts = [] ∧ r = r') ∨
        ((parseValue n es).bind fun p => (parseItems n p.2).map fun q => (p.1 :: q.1, q.2)) =
          some (ts, r) := by
      rcases es with _ | ⟨e, es⟩
      · exact Or.inr (by simpa [parseItems] using h)
      · cases e with
        | endArray =>
          simp only [parseItems, Option.some.injEq, Prod.mk.injEq] at h
          exact Or.inl ⟨es, rfl, h.1.symm, h.2.symm⟩
        | _ => exact Or.inr (by simpa [parseItems] using h)
    rcases key with ⟨r', rfl, rfl, rfl⟩ | h
    · rfl
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨⟨t, r1⟩, hv, ⟨ts', r2⟩, hi, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [parseValue_sound n es t r1 hv, parseItems_sound n r1 ts' r2 hi]
      simp [itemsEvents]

theorem parseMembers_sound : ∀ (n : Nat) (es : List (Event K S)) (ms : List (K × Tree K S))
    (r : List (Event K S)), parseMembers n es = some (ms, r) →
      es = membersEvents ms ++ .endObject :: r
  | 0, _, _, _, h => by simp [parseMembers] at h
  | _ + 1, [], _, _, h => by simp [parseMembers] at h
  | n + 1, e :: es, ms, r, h => by
    cases e with
    | endObject =>
      simp only [parseMembers, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    | key k =>
      simp only [parseMembers, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨⟨t, r1⟩, hv, ⟨ms', r2⟩, hm, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [parseValue_sound n es t r1 hv, parseMembers_sound n r1 ms' r2 hm]
      simp [membersEvents]
    | scalar _ | beginArray | endArray | beginObject => simp [parseMembers] at h

end

theorem ofEvents?_toEvents (t : Tree K S) : ofEvents? t.toEvents = some t := by
  have := parseValue_toEvents t (2 * t.toEvents.length + 1) [] le_rfl
  simp only [List.append_nil] at this
  simp [ofEvents?, this]

theorem toEvents_of_ofEvents? {es : List (Event K S)} {t : Tree K S} (h : ofEvents? es = some t) :
    t.toEvents = es := by
  unfold ofEvents? at h
  split at h
  · next t' hp =>
    simp only [Option.some.injEq] at h
    subst h
    simpa using (parseValue_sound _ _ _ _ hp).symm
  · simp at h

/-! ## Depth -/

open Silmaril.Streams

/-- The truncated depth from a starting depth `c`. -/
def depthFrom (c : Nat) (w : List (Event K S)) : Nat := w.foldl (depthStep Event.kind) c

theorem prefix_append_cases {p a b : List (Event K S)} (h : p <+: a ++ b) :
    p <+: a ∨ ∃ q, q <+: b ∧ p = a ++ q := by
  obtain ⟨t, ht⟩ := h
  rcases List.append_eq_append_iff.mp ht with ⟨a', rfl, -⟩ | ⟨c', rfl, rfl⟩
  · exact Or.inl ⟨a', rfl⟩
  · exact Or.inr ⟨c', ⟨t, rfl⟩, rfl⟩

/-- What one encoded tree, list of items or list of members does to the depth: it returns to
the start depth, never exceeds start + depth, and reaches it. -/
structure Peak (c : Nat) (w : List (Event K S)) (d : Nat) : Prop where
  final : depthFrom c w = c
  le : ∀ p, p <+: w → depthFrom c p ≤ c + d
  reach : ∃ p, p <+: w ∧ depthFrom c p = c + d

theorem Peak.append {c d e : Nat} {a b : List (Event K S)} (ha : Peak c a d) (hb : Peak c b e) :
    Peak c (a ++ b) (max d e) where
  final := by
    have h1 := ha.final; have h2 := hb.final
    simp only [depthFrom, List.foldl_append] at h1 h2 ⊢
    rw [h1, h2]
  le p hp := by
    rcases prefix_append_cases hp with hp | ⟨q, hq, rfl⟩
    · have := ha.le p hp; omega
    · have := hb.le q hq
      simp only [depthFrom, List.foldl_append] at this ⊢
      rw [show List.foldl (depthStep Event.kind) c a = c from ha.final]
      omega
  reach := by
    rcases le_total d e with hde | hde
    · obtain ⟨q, hq, hv⟩ := hb.reach
      refine ⟨a ++ q, by simpa using hq, ?_⟩
      simp only [depthFrom, List.foldl_append] at hv ⊢
      rw [show List.foldl (depthStep Event.kind) c a = c from ha.final, hv]
      omega
    · obtain ⟨q, hq, hv⟩ := ha.reach
      exact ⟨q, hq.trans (List.prefix_append a b), by rw [hv]; omega⟩

theorem Peak.nil (c : Nat) : Peak c ([] : List (Event K S)) 0 where
  final := rfl
  le p hp := by simp at hp; subst hp; simp [depthFrom]
  reach := ⟨[], List.prefix_refl _, by simp [depthFrom]⟩

theorem Peak.neutral (c : Nat) {e : Event K S} (he : e.kind = .neutral) : Peak c [e] 0 where
  final := by simp [depthFrom, depthStep, he]
  le p hp := by
    rcases List.prefix_cons_iff.mp hp with rfl | ⟨t, rfl, ht⟩
    · simp [depthFrom]
    · simp at ht; subst ht; simp [depthFrom, depthStep, he]
  reach := ⟨[], List.nil_prefix, by simp [depthFrom]⟩

/-- Brackets around a body that peaks at `d` from `c + 1` peak at `d + 1` from `c`. -/
theorem Peak.bracket {c d : Nat} {o x : Event K S} {w : List (Event K S)}
    (ho : o.kind = .opening) (hx : x.kind = .closing) (hw : Peak (c + 1) w d) :
    Peak c (o :: w ++ [x]) (d + 1) where
  final := by
    have := hw.final
    simp only [depthFrom, List.foldl_cons, List.foldl_append, depthStep, ho, hx,
      List.foldl_nil] at this ⊢
    rw [this]; omega
  le p hp := by
    rw [List.cons_append] at hp
    rcases List.prefix_cons_iff.mp hp with rfl | ⟨q, rfl, hq⟩
    · simp [depthFrom]
    · rcases List.prefix_concat_iff.mp hq with rfl | hq
      · have := hw.final
        simp only [depthFrom, List.foldl_cons, List.foldl_append, depthStep, ho, hx,
          List.foldl_nil] at this ⊢
        rw [this]; omega
      · have := hw.le q hq
        simp only [depthFrom, List.foldl_cons, depthStep, ho] at this ⊢
        omega
  reach := by
    obtain ⟨q, hq, hv⟩ := hw.reach
    refine ⟨o :: q, by simpa using hq.trans (List.prefix_append w [x]), ?_⟩
    simp only [depthFrom, List.foldl_cons, depthStep, ho] at hv ⊢
    omega

mutual

theorem peak_toEvents (c : Nat) (t : Tree K S) : Peak c t.toEvents t.depth := by
  match t with
  | .scalar s => exact Peak.neutral c rfl
  | .array items =>
    exact Peak.bracket (o := .beginArray) (x := .endArray) rfl rfl (peak_itemsEvents (c + 1) items)
  | .object members =>
    exact Peak.bracket (o := .beginObject) (x := .endObject) rfl rfl
      (peak_membersEvents (c + 1) members)

theorem peak_itemsEvents (c : Nat) (ts : List (Tree K S)) :
    Peak c (itemsEvents ts) (itemsDepth ts) := by
  match ts with
  | [] => exact Peak.nil c
  | t :: ts => exact (peak_toEvents c t).append (peak_itemsEvents c ts)

theorem peak_membersEvents (c : Nat) (ms : List (K × Tree K S)) :
    Peak c (membersEvents ms) (membersDepth ms) := by
  match ms with
  | [] => exact Peak.nil c
  | (k, t) :: ms =>
    have h := ((Peak.neutral c (e := Event.key (S := S) k) rfl).append (peak_toEvents c t)).append
      (peak_membersEvents c ms)
    simp only [Nat.zero_max] at h
    simpa [membersEvents, membersDepth] using h

end

theorem toEvents_mem_depthBound_iff (t : Tree K S) (d : Nat) :
    t.toEvents ∈ DepthBound Event.kind d ↔ t.depth ≤ d := by
  have h := peak_toEvents 0 t
  constructor
  · intro hb
    obtain ⟨p, hp, hv⟩ := h.reach
    have := hb p hp
    simp only [depthFrom, Nat.zero_add] at hv
    simp only [depth] at this
    omega
  · intro hd p hp
    have := h.le p hp
    simp only [depthFrom, Nat.zero_add] at this
    simp only [depth]
    omega

end Silmaril.Proofs.Formats.JsonEvents

end
