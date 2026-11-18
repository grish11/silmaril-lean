module

public import Silmaril.Formats.SExp.Clojure.Defs
import Silmaril.Proofs.Formats.SExp.Reader.Basic

/-! # Proofs: the fuel of `Clojure.equal?` always suffices on the values a key check compares -/

@[expose] public section

namespace Silmaril.Proofs.Formats.SExp.Clojure

open Silmaril.Formats Silmaril.Formats.SExpReader Silmaril.Formats.Clojure

/-! ## Measures -/

theorem size_le_of_mem {x : Value} : ∀ {xs : List Value}, x ∈ xs → x.size ≤ Value.sizeList xs
  | [], h => by simp at h
  | y :: ys, h => by
      simp only [Value.sizeList]
      rcases List.mem_cons.1 h with rfl | h
      · omega
      · have := size_le_of_mem h; omega

theorem evenMapsList_iff : ∀ {xs : List Value},
    Value.evenMapsList xs = true ↔ ∀ x ∈ xs, x.evenMaps = true
  | [] => by simp [Value.evenMapsList]
  | x :: xs => by simp [Value.evenMapsList, evenMapsList_iff]

/-! ## Three-valued connectives never invent `none` -/

theorem all3_isSome : ∀ {l : List (Option Bool)}, (∀ o ∈ l, o.isSome = true) →
    (all3 l).isSome = true
  | [], _ => rfl
  | o :: l, h => by
      have ho := h o (by simp)
      have hl := all3_isSome (l := l) (fun o' ho' => h o' (List.mem_cons_of_mem _ ho'))
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 ho
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hl
      subst hb
      simp only [all3, hc]
      cases b <;> cases c <;> rfl

theorem any3_isSome : ∀ {l : List (Option Bool)}, (∀ o ∈ l, o.isSome = true) →
    (any3 l).isSome = true
  | [], _ => rfl
  | o :: l, h => by
      have ho := h o (by simp)
      have hl := any3_isSome (l := l) (fun o' ho' => h o' (List.mem_cons_of_mem _ ho'))
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 ho
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hl
      subst hb
      simp only [any3, hc]
      cases b <;> cases c <;> rfl

/-! ## Map forms -/

theorem pairs_isSome : ∀ {xs : List Value}, xs.length % 2 = 0 → (pairs xs).isSome = true
  | [], _ => rfl
  | [_], h => by simp at h
  | k :: v :: r, h => by
      have := pairs_isSome (xs := r) (by simp at h; omega)
      obtain ⟨ps, hps⟩ := Option.isSome_iff_exists.1 this
      simp [pairs, hps]

theorem mem_pairs : ∀ {xs : List Value} {ps : List (Value × Value)}, pairs xs = some ps →
    ∀ p ∈ ps, p.1 ∈ xs ∧ p.2 ∈ xs
  | [], ps, h => by simp [pairs] at h; subst h; simp
  | [_], ps, h => by simp [pairs] at h
  | k :: v :: r, ps, h => by
      simp only [pairs] at h
      cases hr : pairs r with
      | none => rw [hr] at h; cases h
      | some qs =>
          rw [hr] at h
          simp only [Option.map_eq_map, Option.map_some, Option.some.injEq] at h
          subst h
          intro p hp
          rcases List.mem_cons.1 hp with rfl | hp
          · simp
          · obtain ⟨h1, h2⟩ := mem_pairs hr p hp
            exact ⟨by simp [h1], by simp [h2]⟩

/-! ## Adequacy of the fuel -/

/-- **Fuel adequacy**: with more fuel than the size of the first value, and every map even,
`equalFuel` answers. Every recursive call compares elements of the first value, which are
strictly smaller. -/
theorem equalFuel_isSome : ∀ (n : Nat) (a b : Value), a.size < n → a.evenMaps = true →
    b.evenMaps = true → (equalFuel n a b).isSome = true := by
  intro n
  induction n with
  | zero => intro a b h; omega
  | succ n ih =>
      intro a b hs ha hb
      cases a <;> cases b <;> simp only [equalFuel, Option.isSome_some]
      case seq.seq xs ys =>
        simp only [Value.size] at hs
        simp only [Value.evenMaps, evenMapsList_iff] at ha hb
        split
        · apply all3_isSome
          intro o ho
          obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ho
          have h1 := List.of_mem_zip hp
          exact ih p.1 p.2 (by have := size_le_of_mem h1.1; omega) (ha _ h1.1) (hb _ h1.2)
        · rfl
      case map.map xs ys =>
        simp only [Value.size] at hs
        simp only [Value.evenMaps, Bool.and_eq_true, beq_iff_eq, evenMapsList_iff] at ha hb
        obtain ⟨ps, hps⟩ := Option.isSome_iff_exists.1 (pairs_isSome ha.1)
        obtain ⟨qs, hqs⟩ := Option.isSome_iff_exists.1 (pairs_isSome hb.1)
        simp only [hps, hqs]
        split
        · apply all3_isSome
          intro o ho
          obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ho
          apply any3_isSome
          intro o' ho'
          obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ho'
          have hp' := mem_pairs hps p hp
          have hq' := mem_pairs hqs q hq
          apply all3_isSome
          intro o'' ho''
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho''
          rcases ho'' with rfl | rfl
          · exact ih p.1 q.1 (by have := size_le_of_mem hp'.1; omega) (ha.2 _ hp'.1)
              (hb.2 _ hq'.1)
          · exact ih p.2 q.2 (by have := size_le_of_mem hp'.2; omega) (ha.2 _ hp'.2)
              (hb.2 _ hq'.2)
        · rfl
      case set.set xs ys =>
        simp only [Value.size] at hs
        simp only [Value.evenMaps, evenMapsList_iff] at ha hb
        split
        · apply all3_isSome
          intro o ho
          obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ho
          apply any3_isSome
          intro o' ho'
          obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ho'
          exact ih x y (by have := size_le_of_mem hx; omega) (ha _ hx) (hb _ hy)
        · rfl

theorem equal?_isSome {a b : Value} (ha : a.evenMaps = true) (hb : b.evenMaps = true) :
    (equal? a b).isSome = true :=
  equalFuel_isSome _ a b (by omega) ha hb

/-! ## Decoding data -/

/-- Marker heads of collections. -/
def NotMarker (x : Datum) : Prop := ∀ m, x = .atom m → m ≠ .vector ∧ m ≠ .map ∧ m ≠ .set

theorem toValues_cons_eq {x r : Datum} {vs : List Value} :
    toValues (.cons x r) = some vs ↔
      ∃ v vs', toValue x = some v ∧ toValues r = some vs' ∧ vs = v :: vs' := by
  cases hx : toValue x <;> cases hr : toValues r <;> simp [toValues, hx, hr, eq_comm]

theorem toValue_cons_general {x r : Datum} (hx : NotMarker x) {v : Value} :
    toValue (.cons x r) = some v ↔
      ∃ v₀ vs, toValue x = some v₀ ∧ toValues r = some vs ∧ v = .seq (v₀ :: vs) := by
  have h1 : x ≠ .atom .vector := fun h => (hx _ h).1 rfl
  have h2 : x ≠ .atom .map := fun h => (hx _ h).2.1 rfl
  have h3 : x ≠ .atom .set := fun h => (hx _ h).2.2 rfl
  rw [toValue.eq_12 x r h1 h2 h3]
  cases toValue x <;> cases toValues r <;> simp [eq_comm]

theorem toValues_length : ∀ {r : Datum} {vs : List Value}, toValues r = some vs →
    vs.length = (elems r).length
  | .nil, vs, h => by simp [toValues] at h; subst h; rfl
  | .atom _, vs, h => by simp [toValues] at h
  | .cons x r, vs, h => by
      obtain ⟨v, vs', -, hr, rfl⟩ := toValues_cons_eq.1 h
      simp [elems, toValues_length hr]

theorem issue_cons {x r : Datum} (h : issue (.cons x r) = none) :
    issue x = none ∧ issue r = none ∧ (∀ m, x = .atom m → literalIssue m r = none) := by
  simp [issue] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun m hm => ?_⟩
  subst hm; simpa using h3

theorem map_even {r : Datum} (h : literalIssue .map r = none) : (elems r).length % 2 = 0 := by
  simp only [literalIssue] at h
  split at h
  · cases h
  · simpa using (by assumption : ¬((elems r).length % 2 ≠ 0))

/-- Values of data without literal issues have only even maps. -/
theorem toValue_evenMaps : ∀ d : Datum,
    (∀ v, toValue d = some v → issue d = none → v.evenMaps = true) ∧
    (∀ vs, toValues d = some vs → issue d = none → Value.evenMapsList vs = true) := by
  intro d
  induction d with
  | nil =>
      exact ⟨fun v h _ => by simp [toValue] at h; subst h; rfl,
        fun vs h _ => by simp [toValues] at h; subst h; rfl⟩
  | atom a =>
      refine ⟨fun v h _ => ?_, fun vs h _ => by simp [toValues] at h⟩
      rcases a with _ | _ | _ | ⟨d, _ | _⟩ | _ | _ | _ | _ | _ | _ | _ <;>
        simp [toValue] at h <;> subst h <;> rfl
  | cons x r ihx ihr =>
      refine ⟨fun v h hi => ?_, fun vs h hi => ?_⟩
      · obtain ⟨hix, hir, hlit⟩ := issue_cons hi
        by_cases hm : NotMarker x
        · obtain ⟨v₀, vs, h0, hvs, rfl⟩ := (toValue_cons_general hm).1 h
          simp [Value.evenMaps, Value.evenMapsList, ihx.1 v₀ h0 hix, ihr.2 vs hvs hir]
        · simp only [NotMarker, not_forall] at hm
          obtain ⟨m, rfl, hm⟩ := hm
          have hlm := hlit m rfl
          cases m <;> simp at hm
          · simp only [toValue, Option.map_eq_map, Option.map_eq_some_iff] at h
            obtain ⟨vs, hvs, rfl⟩ := h
            simpa [Value.evenMaps] using ihr.2 vs hvs hir
          · simp only [toValue, Option.map_eq_map, Option.map_eq_some_iff] at h
            obtain ⟨vs, hvs, rfl⟩ := h
            simp only [Value.evenMaps, Bool.and_eq_true, beq_iff_eq]
            exact ⟨by rw [toValues_length hvs]; exact map_even hlm, ihr.2 vs hvs hir⟩
          · simp only [toValue, Option.map_eq_map, Option.map_eq_some_iff] at h
            obtain ⟨vs, hvs, rfl⟩ := h
            simpa [Value.evenMaps] using ihr.2 vs hvs hir
      · obtain ⟨hix, hir, -⟩ := issue_cons hi
        obtain ⟨v, vs', hv, hr, rfl⟩ := toValues_cons_eq.1 h
        simp [Value.evenMapsList, ihx.1 v hv hix, ihr.2 vs' hr hir]

/-! ## Well-formed data decode -/

open Silmaril.Proofs.Formats.SExp.Reader in
theorem wf_cons_nonatom {x r : Datum} (hx : ∀ m, x ≠ .atom m) :
    syntaxNotation.wf (.cons x r) = (syntaxNotation.wf x && syntaxNotation.wfItems false false r) :=
  wf_cons_of_not_atom syntaxNotation hx

open Silmaril.Proofs.Formats.SExp.Reader in
theorem wfItems_cons_nonatom {first : Bool} {x r : Datum} (hx : ∀ m, x ≠ .atom m) :
    syntaxNotation.wfItems false first (.cons x r) =
      (syntaxNotation.wf x && syntaxNotation.wfItems false false r) :=
  wfItems_cons_of_not_atom syntaxNotation hx

theorem role_coll {m : Atom} {c : Closer} {d : Bool} (h : role m = .coll c d) :
    d = false ∧ (m = .vector ∨ m = .map ∨ m = .set) := by
  cases m <;> simp only [role] at h <;> (try split at h) <;> simp_all

theorem role_ne_prefix (m : Atom) : role m ≠ .prefix := by
  cases m <;> simp only [role] <;> (try split) <;> simp

theorem plain_notMarker {m : Atom} (h : role m = .plain) : NotMarker (.atom m) := by
  intro m' hm; cases hm; refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> simp [role] at h

theorem toValue_atom_isSome {m : Atom} (h : role m = .plain) : (toValue (.atom m)).isSome := by
  rcases m with _ | _ | _ | ⟨d, _ | _⟩ | _ | _ | _ | _ | _ | _ | _ <;> simp_all [toValue, role]

theorem wf_atom_iff {m : Atom} : syntaxNotation.wf (.atom m) = true ↔ role m = .plain := by
  simp only [Notation.wf, syntaxNotation]
  cases role m <;> simp [Role.isPlain]

theorem toValue_isSome_of_wf : ∀ d : Datum,
    (syntaxNotation.wf d = true → (toValue d).isSome = true) ∧
    (∀ first, syntaxNotation.wfItems false first d = true → (toValues d).isSome = true) := by
  intro d
  induction d with
  | nil => exact ⟨fun _ => rfl, fun _ _ => rfl⟩
  | atom a =>
      refine ⟨fun h => toValue_atom_isSome (wf_atom_iff.1 h), fun first h => ?_⟩
      simp [Notation.wfItems] at h
  | cons x r ihx ihr =>
      have consSome : (toValue x).isSome = true → (toValues r).isSome = true → NotMarker x →
          (toValue (.cons x r)).isSome = true := by
        intro h1 h2 hm
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h1
        obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.1 h2
        exact Option.isSome_iff_exists.2 ⟨_, (toValue_cons_general hm).2 ⟨v, vs, hv, hvs, rfl⟩⟩
      have consesSome : (toValue x).isSome = true → (toValues r).isSome = true →
          (toValues (.cons x r)).isSome = true := by
        intro h1 h2
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h1
        obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.1 h2
        exact Option.isSome_iff_exists.2 ⟨_, toValues_cons_eq.2 ⟨v, vs, hv, hvs, rfl⟩⟩
      refine ⟨fun h => ?_, fun first h => ?_⟩
      · cases x with
        | atom m =>
            cases hm : role m with
            | plain =>
                simp only [Notation.wf, syntaxNotation, hm] at h
                exact consSome (toValue_atom_isSome hm) (ihr.2 false h) (plain_notMarker hm)
            | coll c d =>
                simp only [Notation.wf, syntaxNotation, hm] at h
                obtain ⟨rfl, hmk⟩ := role_coll hm
                have hr := ihr.2 true h
                obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.1 hr
                rcases hmk with rfl | rfl | rfl <;> simp [toValue, hvs]
            | «prefix» => exact absurd hm (role_ne_prefix m)
            | unwritable => simp [Notation.wf, syntaxNotation, hm] at h
        | nil =>
            rw [wf_cons_nonatom (by simp)] at h
            simp only [Bool.and_eq_true] at h
            exact consSome (ihx.1 h.1) (ihr.2 false h.2) (by intro m hm; cases hm)
        | cons a b =>
            rw [wf_cons_nonatom (by simp)] at h
            simp only [Bool.and_eq_true] at h
            exact consSome (ihx.1 h.1) (ihr.2 false h.2) (by intro m hm; cases hm)
      · cases x with
        | atom m =>
            cases hm : role m with
            | plain =>
                simp only [Notation.wfItems, syntaxNotation, hm] at h
                exact consesSome (toValue_atom_isSome hm) (ihr.2 false h)
            | coll => simp [Notation.wfItems, syntaxNotation, hm] at h
            | «prefix» => simp [Notation.wfItems, syntaxNotation, hm] at h
            | unwritable => simp [Notation.wfItems, syntaxNotation, hm] at h
        | nil =>
            rw [wfItems_cons_nonatom (by simp)] at h
            simp only [Bool.and_eq_true] at h
            exact consesSome (ihx.1 h.1) (ihr.2 false h.2)
        | cons a b =>
            rw [wfItems_cons_nonatom (by simp)] at h
            simp only [Bool.and_eq_true] at h
            exact consesSome (ihx.1 h.1) (ihr.2 false h.2)

/-! ## Elements of literals -/

theorem elems_wf : ∀ {r : Datum} {first : Bool}, syntaxNotation.wfItems false first r = true →
    ∀ x ∈ elems r, syntaxNotation.wf x = true
  | .nil, _, _ => by simp [elems]
  | .atom _, _, _ => by simp [elems]
  | .cons y r, first, h => by
      intro x hx
      simp only [elems, List.mem_cons] at hx
      cases y with
      | atom m =>
          cases hm : role m with
          | plain =>
              simp only [Notation.wfItems, syntaxNotation, hm] at h
              rcases hx with rfl | hx
              · exact wf_atom_iff.2 hm
              · exact elems_wf h x hx
          | coll => simp [Notation.wfItems, syntaxNotation, hm] at h
          | «prefix» => simp [Notation.wfItems, syntaxNotation, hm] at h
          | unwritable => simp [Notation.wfItems, syntaxNotation, hm] at h
      | nil =>
          rw [wfItems_cons_nonatom (by simp)] at h
          simp only [Bool.and_eq_true] at h
          rcases hx with rfl | hx
          · exact h.1
          · exact elems_wf h.2 x hx
      | cons a b =>
          rw [wfItems_cons_nonatom (by simp)] at h
          simp only [Bool.and_eq_true] at h
          rcases hx with rfl | hx
          · exact h.1
          · exact elems_wf h.2 x hx

theorem elems_issue : ∀ {r : Datum}, issue r = none → ∀ x ∈ elems r, issue x = none
  | .nil, _ => by simp [elems]
  | .atom _, _ => by simp [elems]
  | .cons y r, h => by
      intro x hx
      obtain ⟨hy, hr, -⟩ := issue_cons h
      simp only [elems, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hy
      · exact elems_issue hr x hx

theorem mem_keysOf : ∀ {l : List Datum} {x : Datum}, x ∈ keysOf l → x ∈ l
  | [], _, h => by simp [keysOf] at h
  | [k], _, h => by simpa [keysOf] using h
  | k :: v :: r, x, h => by
      simp only [keysOf, List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · simp [mem_keysOf h]

theorem mapM_toValue : ∀ {l : List Datum}, (∀ x ∈ l, (toValue x).isSome = true) →
    ∃ vs, l.mapM toValue = some vs ∧ ∀ v ∈ vs, ∃ x ∈ l, toValue x = some v
  | [], _ => ⟨[], rfl, by simp⟩
  | x :: l, h => by
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (h x (by simp))
      obtain ⟨vs, hvs, hmem⟩ := mapM_toValue (l := l) (fun y hy => h y (by simp [hy]))
      refine ⟨v :: vs, by simp [List.mapM_cons, hv, hvs], ?_⟩
      intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · exact ⟨x, by simp, hv⟩
      · obtain ⟨y, hy, hyw⟩ := hmem w hw
        exact ⟨y, by simp [hy], hyw⟩

/-! ## No spurious `unsupported` -/

theorem worse_unsupported {i j : Option Issue} (h : worse i j = some .unsupported) :
    i = some .unsupported ∨ j = some .unsupported := by
  rcases i with _ | (_ | _ | _) <;> rcases j with _ | (_ | _ | _) <;> simp_all [worse]

theorem pairIssue_ne {x y : Value} (hx : x.evenMaps = true) (hy : y.evenMaps = true) :
    pairIssue x y ≠ some .unsupported := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (equal?_isSome hx hy)
  unfold pairIssue
  rw [hb]
  cases b <;> simp

theorem keysIssue_ne_unsupported : ∀ {vs : List Value}, (∀ v ∈ vs, v.evenMaps = true) →
    keysIssue vs ≠ some .unsupported
  | [], _ => by simp [keysIssue]
  | x :: xs, h => by
      have fold : ∀ ys : List Value, (∀ y ∈ ys, y.evenMaps = true) →
          ys.foldr (fun y acc => worse (pairIssue x y) acc) none ≠ some .unsupported := by
        intro ys
        induction ys with
        | nil => simp
        | cons y ys ih =>
            intro hys hf
            simp only [List.foldr_cons] at hf
            rcases worse_unsupported hf with hf | hf
            · exact pairIssue_ne (h x (by simp)) (hys y (by simp)) hf
            · exact ih (fun z hz => hys z (by simp [hz])) hf
      intro hk
      simp only [keysIssue] at hk
      rcases worse_unsupported hk with hk | hk
      · exact fold xs (fun y hy => h y (by simp [hy])) hk
      · exact keysIssue_ne_unsupported (fun y hy => h y (by simp [hy])) hk

/-- Keys of a literal in well-formed data without inner issues decode to even values. -/
theorem keys_ok {r : Datum} {first : Bool} (hw : syntaxNotation.wfItems false first r = true)
    (hi : issue r = none) {ks : List Datum} (hks : ∀ k ∈ ks, k ∈ elems r) :
    ∃ vs, ks.mapM toValue = some vs ∧ ∀ v ∈ vs, v.evenMaps = true := by
  obtain ⟨vs, hvs, hmem⟩ := mapM_toValue (l := ks) (fun k hk =>
    (toValue_isSome_of_wf k).1 (elems_wf hw k (hks k hk)))
  refine ⟨vs, hvs, fun v hv => ?_⟩
  obtain ⟨k, hk, hkv⟩ := hmem v hv
  exact (toValue_evenMaps k).1 v hkv (elems_issue hi k (hks k hk))

theorem literalIssue_ne {m : Atom} {r : Datum} {first : Bool}
    (hw : syntaxNotation.wfItems false first r = true) (hi : issue r = none) :
    literalIssue m r ≠ some .unsupported := by
  cases m with
  | map =>
      simp only [literalIssue]
      split
      · simp
      · obtain ⟨vs, hvs, hev⟩ := keys_ok hw hi (ks := keysOf (elems r))
          (fun k hk => mem_keysOf hk)
        rw [hvs]
        exact keysIssue_ne_unsupported hev
  | set =>
      simp only [literalIssue]
      obtain ⟨vs, hvs, hev⟩ := keys_ok hw hi (ks := elems r) (fun k hk => hk)
      rw [hvs]
      exact keysIssue_ne_unsupported hev
  | _ => simp [literalIssue]

theorem orElse_ne {a b : Option Issue} (ha : a ≠ some .unsupported)
    (hb : a = none → b ≠ some .unsupported) : (a <|> b) ≠ some .unsupported := by
  cases a with
  | none => simpa using hb rfl
  | some i => simpa using ha

/-- **No spurious `unsupported`**: on well-formed data the literal check never reports an
undecided key comparison. -/
theorem issue_ne_unsupported : ∀ d : Datum,
    (syntaxNotation.wf d = true → issue d ≠ some .unsupported) ∧
    (∀ first, syntaxNotation.wfItems false first d = true → issue d ≠ some .unsupported) := by
  intro d
  induction d with
  | nil => exact ⟨fun _ => by simp [issue], fun _ _ => by simp [issue]⟩
  | atom a => exact ⟨fun _ => by simp [issue], fun _ _ => by simp [issue]⟩
  | cons x r ihx ihr =>
      have step : syntaxNotation.wf x = true → (∃ first, syntaxNotation.wfItems false first r = true) →
          issue (.cons x r) ≠ some .unsupported := by
        rintro hx ⟨first, hr⟩
        simp only [issue]
        refine orElse_ne (ihx.1 hx) (fun hix => orElse_ne (ihr.2 first hr) (fun hir => ?_))
        cases x with
        | atom m => exact literalIssue_ne hr hir
        | _ => simp
      have markerStep : ∀ m first, syntaxNotation.wfItems false first r = true →
          issue (.cons (.atom m) r) ≠ some .unsupported := by
        intro m first hr
        simp only [issue]
        refine orElse_ne (by simp) (fun _ => orElse_ne (ihr.2 first hr) (fun hir => ?_))
        exact literalIssue_ne hr hir
      refine ⟨fun h => ?_, fun first h => ?_⟩
      · cases x with
        | atom m =>
            cases hm : role m with
            | plain =>
                simp only [Notation.wf, syntaxNotation, hm] at h
                exact markerStep m false h
            | coll c d =>
                simp only [Notation.wf, syntaxNotation, hm] at h
                obtain ⟨rfl, -⟩ := role_coll hm
                exact markerStep m true h
            | «prefix» => exact absurd hm (role_ne_prefix m)
            | unwritable => simp [Notation.wf, syntaxNotation, hm] at h
        | nil =>
            rw [wf_cons_nonatom (by simp)] at h
            simp only [Bool.and_eq_true] at h
            exact step h.1 ⟨false, h.2⟩
        | cons a b =>
            rw [wf_cons_nonatom (by simp)] at h
            simp only [Bool.and_eq_true] at h
            exact step h.1 ⟨false, h.2⟩
      · cases x with
        | atom m =>
            cases hm : role m with
            | plain =>
                simp only [Notation.wfItems, syntaxNotation, hm] at h
                exact markerStep m false h
            | coll => simp [Notation.wfItems, syntaxNotation, hm] at h
            | «prefix» => simp [Notation.wfItems, syntaxNotation, hm] at h
            | unwritable => simp [Notation.wfItems, syntaxNotation, hm] at h
        | nil =>
            rw [wfItems_cons_nonatom (by simp)] at h
            simp only [Bool.and_eq_true] at h
            exact step h.1 ⟨false, h.2⟩
        | cons a b =>
            rw [wfItems_cons_nonatom (by simp)] at h
            simp only [Bool.and_eq_true] at h
            exact step h.1 ⟨false, h.2⟩

end Silmaril.Proofs.Formats.SExp.Clojure
