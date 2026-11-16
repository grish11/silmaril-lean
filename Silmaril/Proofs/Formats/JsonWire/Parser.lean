module

public import Silmaril.Formats.JsonWire.Grammar.Defs

/-! # Proofs: the parser accepts exactly the token grammar (`Silmaril.Formats.JsonWire.Grammar.Thms`) -/

@[expose] public section

namespace Silmaril.Proofs.Formats.JsonWire.Parser

open Silmaril.Formats.JsonWire Silmaril.Formats.JsonWire.Internal

theorem value_head {p : List Token} (h : TValue p) :
    ∃ t q, p = t :: q ∧ (t.IsScalar ∨ t = .arrayOpen ∨ t = .objectOpen) := by
  cases h with
  | scalar ht => exact ⟨_, _, rfl, Or.inl ht⟩
  | array _ => exact ⟨_, _, rfl, Or.inr (Or.inl rfl)⟩
  | object _ => exact ⟨_, _, rfl, Or.inr (Or.inr rfl)⟩

theorem scalar_complete {t : Token} (ht : t.IsScalar) (n : Nat) (r : List Token) :
    ∃ a, value? .rfc8259 (n + 1) (t :: r) = some (a, r) := by
  cases t <;> simp [Token.IsScalar] at ht <;> simp [value?]
  rename_i name plain
  cases plain <;> simp at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl <;> simp (config := { decide := true })

@[simp] theorem rfc8259_beq_json5 : (Dialect.rfc8259 == Dialect.json5) = false := rfl

mutual
theorem value_complete {p : List Token} : TValue p → ∀ f, p.length ≤ f → ∀ r,
    ∃ a, value? .rfc8259 f (p ++ r) = some (a, r)
  | .scalar (t := t) ht, f, hf, r => by
    obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by simp at hf; omega⟩
    exact scalar_complete ht n r
  | .array (xs := xs) hx, f, hf, r => by
    obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by simp at hf; omega⟩
    obtain ⟨a, ha⟩ := elems_complete hx n (by simp at hf; omega) r
    exact ⟨.list a, by simp [value?, ha]⟩
  | .object (xs := xs) hx, f, hf, r => by
    obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by simp at hf; omega⟩
    obtain ⟨a, ha⟩ := members_complete hx n (by simp at hf; omega) r
    exact ⟨.map a, by simp [value?, ha]⟩
theorem elems_complete {p : List Token} : TElems p → ∀ f, p.length ≤ f → ∀ r,
    ∃ a, array? .rfc8259 f true (p ++ r) = some (a, r)
  | .empty, f, hf, r => by
    obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by simp at hf; omega⟩
    simp [array?]
  | .ne hx, f, hf, r => elemsNE_complete hx true f hf r
theorem elemsNE_complete {p : List Token} : TElemsNE p → ∀ (e : Bool) f, p.length ≤ f → ∀ r,
    ∃ a, array? .rfc8259 f e (p ++ r) = some (a, r)
  | .last (v := v) hv, e, f, hf, r => by
    obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by simp at hf; omega⟩
    obtain ⟨a, ha⟩ := value_complete hv n (by simp at hf ⊢; omega) (.arrayClose :: r)
    obtain ⟨t, q, rfl, ht⟩ := value_head hv
    rcases ht with ht | rfl | rfl
    · cases t <;> simp [Token.IsScalar] at ht <;> simp_all [array?]
    all_goals simp_all [array?]
  | .cons (v := v) (xs := xs) hv hx, e, f, hf, r => by
    obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by simp at hf; omega⟩
    obtain ⟨a, ha⟩ := value_complete hv n (by simp at hf ⊢; omega) (.comma :: (xs ++ r))
    obtain ⟨b, hb⟩ := elemsNE_complete hx false n (by simp at hf ⊢; omega) r
    obtain ⟨t, q, rfl, ht⟩ := value_head hv
    rcases ht with ht | rfl | rfl
    · cases t <;> simp [Token.IsScalar] at ht <;> simp_all [array?]
    all_goals simp_all [array?]
theorem members_complete {p : List Token} : TMembers p → ∀ f, p.length ≤ f → ∀ r,
    ∃ a, object? .rfc8259 f true (p ++ r) = some (a, r)
  | .empty, f, hf, r => by
    obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by simp at hf; omega⟩
    simp [object?]
  | .ne hx, f, hf, r => membersNE_complete hx true f hf r
theorem membersNE_complete {p : List Token} : TMembersNE p → ∀ (e : Bool) f, p.length ≤ f → ∀ r,
    ∃ a, object? .rfc8259 f e (p ++ r) = some (a, r)
  | .last (v := v) hv, e, f, hf, r => by
    obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by simp at hf; omega⟩
    obtain ⟨a, ha⟩ := value_complete hv n (by simp at hf ⊢; omega) (.objectClose :: r)
    simp_all [object?]
  | .cons (v := v) (xs := xs) hv hx, e, f, hf, r => by
    obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by simp at hf; omega⟩
    obtain ⟨a, ha⟩ := value_complete hv n (by simp at hf ⊢; omega) (.comma :: (xs ++ r))
    obtain ⟨b, hb⟩ := membersNE_complete hx false n (by simp at hf ⊢; omega) r
    simp_all [object?]
end



theorem array?_inv {n : Nat} {e : Bool} {ts r : List Token} {a : Syn Number .arr}
    (h : array? .rfc8259 (n + 1) e ts = some (a, r)) :
    (ts = .arrayClose :: r ∧ e = true) ∨
    ∃ v rest, ts.head? ≠ some .arrayClose ∧ value? .rfc8259 n ts = some (v, rest) ∧
      (rest = .arrayClose :: r ∨ ∃ r' b, rest = .comma :: r' ∧ array? .rfc8259 n false r' = some (b, r)) := by
  unfold array? at h
  split at h
  · left; cases e <;> simp_all
  right
  rename_i hne
  obtain ⟨⟨v, rest⟩, hv, h'⟩ := Option.bind_eq_some_iff.mp h
  refine ⟨v, rest, ?_, hv, ?_⟩
  · rcases ts with _ | ⟨t, ts⟩
    · simp
    · simp only [List.head?_cons, ne_eq, Option.some.injEq]
      rintro rfl; exact hne ts rfl
  rcases rest with _ | ⟨u, rest⟩
  · simp at h'
  cases u <;> simp only [reduceCtorEq] at h'
  all_goals first
    | (simp at h'; done)
    | (simp at h'; exact Or.inl (by rw [h'.2]))
    | (obtain ⟨⟨b, r'⟩, hb, h''⟩ := Option.bind_eq_some_iff.mp h'
       simp at h''
       exact Or.inr ⟨rest, b, rfl, h''.2 ▸ hb⟩)

theorem object?_inv {n : Nat} {e : Bool} {ts r : List Token} {a : Syn Number .obj}
    (h : object? .rfc8259 (n + 1) e ts = some (a, r)) :
    (ts = .objectClose :: r ∧ e = true) ∨
    ∃ k after v rest, ts = .string k :: .colon :: after ∧ value? .rfc8259 n after = some (v, rest) ∧
      (rest = .objectClose :: r ∨ ∃ r' b, rest = .comma :: r' ∧ object? .rfc8259 n false r' = some (b, r)) := by
  rcases ts with _ | ⟨t, ts⟩
  · simp [object?] at h
  by_cases ht : t = .objectClose
  · subst ht; left; cases e <;> simp_all [object?]
  right
  obtain ⟨k, after, rfl, rfl⟩ : ∃ k after, t = .string k ∧ ts = .colon :: after := by
    rcases ts with _ | ⟨t', after⟩
    · cases t <;> simp_all [object?]
    cases t <;> cases t' <;> simp_all [object?]
  have e1 : object? .rfc8259 (n + 1) e (.string k :: .colon :: after) =
      (value? .rfc8259 n after).bind (fun x => match x.2 with
        | .objectClose :: rest => some (.objCons k x.1 .objNil, rest)
        | .comma :: rest => (object? .rfc8259 n false rest).bind (fun y => some (.objCons k x.1 y.1, y.2))
        | _ => none) := rfl
  rw [e1] at h
  obtain ⟨⟨v, rest⟩, hv, h'⟩ := Option.bind_eq_some_iff.mp h
  refine ⟨k, after, v, rest, rfl, hv, ?_⟩
  rcases rest with _ | ⟨u, rest⟩
  · simp at h'
  cases u <;> simp only [reduceCtorEq] at h'
  all_goals first
    | (simp at h'; done)
    | (simp at h'; exact Or.inl (by rw [h'.2]))
    | (obtain ⟨⟨b, r'⟩, hb, h''⟩ := Option.bind_eq_some_iff.mp h'
       simp at h''
       exact Or.inr ⟨rest, b, rfl, h''.2 ▸ hb⟩)

theorem value?_inv {n : Nat} {ts r : List Token} {a : Ast Number}
    (h : value? .rfc8259 (n + 1) ts = some (a, r)) :
    (∃ t, t.IsScalar ∧ ts = t :: r) ∨
    (∃ xs b, ts = .arrayOpen :: xs ∧ array? .rfc8259 n true xs = some (b, r)) ∨
    (∃ xs b, ts = .objectOpen :: xs ∧ object? .rfc8259 n true xs = some (b, r)) := by
  unfold value? at h
  rcases ts with _ | ⟨t, ts⟩
  · simp at h
  cases t
  case identifier name plain =>
    cases plain
    · simp at h
    simp only at h
    split_ifs at h with h1 h2 h3 h4 h5 <;> simp at h
    all_goals exact Or.inl ⟨.identifier name true, by simp_all [Token.IsScalar, beq_iff_eq], by rw [h.2]⟩
  case arrayOpen =>
    obtain ⟨⟨b, r'⟩, hb, h'⟩ := Option.bind_eq_some_iff.mp h
    simp at h'
    exact Or.inr (Or.inl ⟨ts, b, rfl, h'.2 ▸ hb⟩)
  case objectOpen =>
    obtain ⟨⟨b, r'⟩, hb, h'⟩ := Option.bind_eq_some_iff.mp h
    simp at h'
    exact Or.inr (Or.inr ⟨ts, b, rfl, h'.2 ▸ hb⟩)
  all_goals simp at h
  all_goals (refine Or.inl ⟨_, ?_, by rw [h.2]⟩; simp [Token.IsScalar])


/-- What the parser returns is a token-grammar prefix of its input. -/
theorem sound : ∀ f : Nat,
    (∀ ts a r, value? .rfc8259 f ts = some (a, r) → ∃ p, ts = p ++ r ∧ TValue p) ∧
    (∀ e ts a r, array? .rfc8259 f e ts = some (a, r) → ∃ p, ts = p ++ r ∧
      (if e then TElems p else TElemsNE p)) ∧
    (∀ e ts a r, object? .rfc8259 f e ts = some (a, r) → ∃ p, ts = p ++ r ∧
      (if e then TMembers p else TMembersNE p))
  | 0 => by
    refine ⟨?_, ?_, ?_⟩ <;> intros <;> simp_all [value?, array?, object?]
  | n + 1 => by
    obtain ⟨hV, hA, hO⟩ := sound n
    refine ⟨?_, ?_, ?_⟩
    · intro ts a r h
      rcases value?_inv h with ⟨t, ht, rfl⟩ | ⟨xs, b, rfl, hb⟩ | ⟨xs, b, rfl, hb⟩
      · exact ⟨[t], rfl, .scalar ht⟩
      · obtain ⟨p, rfl, hp⟩ := hA true xs b r hb
        exact ⟨.arrayOpen :: p, rfl, .array (by simpa using hp)⟩
      · obtain ⟨p, rfl, hp⟩ := hO true xs b r hb
        exact ⟨.objectOpen :: p, rfl, .object (by simpa using hp)⟩
    · intro e ts a r h
      rcases array?_inv h with ⟨rfl, rfl⟩ | ⟨v, rest, hh, hv, hr⟩
      · exact ⟨[.arrayClose], rfl, by simpa using TElems.empty⟩
      obtain ⟨p, rfl, hp⟩ := hV ts v rest hv
      have key : ∃ q, p ++ rest = q ++ r ∧ TElemsNE q := by
        rcases hr with rfl | ⟨r', b, rfl, hb⟩
        · exact ⟨p ++ [.arrayClose], by simp, .last hp⟩
        · obtain ⟨q, rfl, hq⟩ := hA false r' b r hb
          exact ⟨p ++ .comma :: q, by simp, .cons hp (by simpa using hq)⟩
      obtain ⟨q, hq, hq'⟩ := key
      refine ⟨q, hq, ?_⟩
      cases e
      · simpa using hq'
      · simpa using TElems.ne hq'
    · intro e ts a r h
      rcases object?_inv h with ⟨rfl, rfl⟩ | ⟨k, after, v, rest, rfl, hv, hr⟩
      · exact ⟨[.objectClose], rfl, by simpa using TMembers.empty⟩
      obtain ⟨p, rfl, hp⟩ := hV after v rest hv
      have key : ∃ q, Token.string k :: .colon :: (p ++ rest) = q ++ r ∧ TMembersNE q := by
        rcases hr with rfl | ⟨r', b, rfl, hb⟩
        · exact ⟨.string k :: .colon :: (p ++ [.objectClose]), by simp, .last hp⟩
        · obtain ⟨q, rfl, hq⟩ := hO false r' b r hb
          exact ⟨.string k :: .colon :: (p ++ .comma :: q), by simp, .cons hp (by simpa using hq)⟩
      obtain ⟨q, hq, hq'⟩ := key
      refine ⟨q, hq, ?_⟩
      cases e
      · simpa using hq'
      · simpa using TMembers.ne hq'

/-- **The parser accepts exactly the token grammar**: with at least as much fuel as tokens,
`value?` reads all of `ts` iff `ts` is a JSON value of the token grammar. -/
theorem value?_eq_some_nil_iff {ts : List Token} {f : Nat} (hf : ts.length ≤ f) :
    (∃ a, value? .rfc8259 f ts = some (a, [])) ↔ TValue ts := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨p, rfl, hp⟩ := (sound f).1 ts a [] ha
    simpa using hp
  · intro h
    simpa using value_complete h f hf []

/-- The same, as the parser's result is a function of its input: if the token grammar holds,
any successful parse consumed everything. -/
theorem value?_rest_eq_nil {ts r : List Token} {f : Nat} {a : Ast Number} (hf : ts.length ≤ f)
    (h : value? .rfc8259 f ts = some (a, r)) (hT : TValue ts) : r = [] := by
  obtain ⟨b, hb⟩ := value_complete hT f hf []
  simp only [List.append_nil] at hb
  rw [hb] at h
  simp at h
  exact h.2

end Silmaril.Proofs.Formats.JsonWire.Parser

end
