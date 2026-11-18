module

public import Silmaril.Formats.SExp.Clojure.Defs

/-! # Proofs: the Clojure key-equality decision is sound for `Equal` -/

@[expose] public section

namespace Silmaril.Proofs.Formats.SExp.Clojure

open Silmaril.Formats Silmaril.Formats.Clojure

/-! ## Three-valued connectives -/

theorem all3_sound {α : Type} {P : α → Prop} {f : α → Option Bool} : ∀ (l : List α),
    (∀ x ∈ l, ∀ r, f x = some r → (P x ↔ r = true)) →
      ∀ r, all3 (l.map f) = some r → ((∀ x ∈ l, P x) ↔ r = true)
  | [], _, r, h => by simp [all3] at h; subst h; simp
  | x :: xs, hf, r, h => by
      have hx := hf x (by simp)
      have ih := all3_sound xs (fun y hy => hf y (by simp [hy]))
      simp only [List.map_cons, all3] at h
      cases hfx : f x with
      | none =>
          cases hr : all3 (xs.map f) with
          | none => simp [hfx, hr] at h
          | some b =>
              cases b
              · simp [hfx, hr] at h; subst h
                have := (ih false hr); simp only [Bool.false_eq_true, iff_false] at this
                simp only [List.forall_mem_cons, Bool.false_eq_true, iff_false, not_and]
                exact fun _ => this
              · simp [hfx, hr] at h
      | some c =>
          have hc := hx c hfx
          cases c
          · simp [hfx] at h; subst h
            simp only [Bool.false_eq_true, iff_false] at hc
            simp [hc]
          · cases hr : all3 (xs.map f) with
            | none => simp [hfx, hr] at h
            | some b =>
                have hb := ih b hr
                cases b
                · simp [hfx, hr] at h; subst h
                  simp only [Bool.false_eq_true, iff_false] at hb
                  simp [hb]
                · simp [hfx, hr] at h; subst h
                  simp only [iff_true] at hc hb
                  simp only [List.forall_mem_cons, iff_true]
                  exact ⟨hc, hb⟩

theorem any3_sound {α : Type} {P : α → Prop} {f : α → Option Bool} : ∀ (l : List α),
    (∀ x ∈ l, ∀ r, f x = some r → (P x ↔ r = true)) →
      ∀ r, any3 (l.map f) = some r → ((∃ x ∈ l, P x) ↔ r = true)
  | [], _, r, h => by simp [any3] at h; subst h; simp
  | x :: xs, hf, r, h => by
      have hx := hf x (by simp)
      have ih := any3_sound xs (fun y hy => hf y (by simp [hy]))
      simp only [List.map_cons, any3] at h
      cases hfx : f x with
      | none =>
          cases hr : any3 (xs.map f) with
          | none => simp [hfx, hr] at h
          | some b =>
              cases b
              · simp [hfx, hr] at h
              · simp [hfx, hr] at h; subst h
                have := (ih true hr); simp only [iff_true] at this
                obtain ⟨y, hy, hp⟩ := this
                simp only [iff_true]
                exact ⟨y, by simp [hy], hp⟩
      | some c =>
          have hc := hx c hfx
          cases c
          · cases hr : any3 (xs.map f) with
            | none => simp [hfx, hr] at h
            | some b =>
                have hb := ih b hr
                cases b
                · simp [hfx, hr] at h; subst h
                  simp only [Bool.false_eq_true, iff_false] at hc hb
                  simp only [Bool.false_eq_true, iff_false]
                  rintro ⟨y, hy, hp⟩
                  rcases List.mem_cons.1 hy with rfl | hy
                  · exact hc hp
                  · exact hb ⟨y, hy, hp⟩
                · simp [hfx, hr] at h; subst h
                  simp only [iff_true] at hb
                  obtain ⟨y, hy, hp⟩ := hb
                  simp only [iff_true]
                  exact ⟨y, by simp [hy], hp⟩
          · simp [hfx] at h; subst h
            simp only [iff_true] at hc
            simp only [iff_true]
            exact ⟨x, by simp, hc⟩

theorem and3_sound {o₁ o₂ : Option Bool} {P₁ P₂ : Prop}
    (h₁ : ∀ r, o₁ = some r → (P₁ ↔ r = true)) (h₂ : ∀ r, o₂ = some r → (P₂ ↔ r = true))
    {r : Bool} (h : all3 [o₁, o₂] = some r) : (P₁ ∧ P₂) ↔ r = true := by
  rcases o₁ with _ | ⟨_ | _⟩ <;> rcases o₂ with _ | ⟨_ | _⟩ <;> simp [all3] at h <;>
    subst h <;> simp_all

/-! ## The specification, list by list -/

theorem pointwise_iff : ∀ {xs ys : List Value},
    Pointwise xs ys ↔ xs.length = ys.length ∧ ∀ p ∈ xs.zip ys, Equal p.1 p.2
  | [], [] => by simp [Pointwise.nil]
  | [], _ :: _ => by simp; intro h; cases h
  | _ :: _, [] => by simp; intro h; cases h
  | x :: xs, y :: ys => by
      constructor
      · intro h
        cases h with
        | cons hx hr =>
            obtain ⟨hl, hall⟩ := pointwise_iff.1 hr
            refine ⟨by simp [hl], ?_⟩
            simp only [List.zip_cons_cons, List.forall_mem_cons]
            exact ⟨hx, hall⟩
      · rintro ⟨hl, hall⟩
        simp only [List.zip_cons_cons, List.forall_mem_cons] at hall
        exact .cons hall.1 (pointwise_iff.2 ⟨by simpa using hl, hall.2⟩)

theorem entryIn_iff {k v : Value} : ∀ {qs : List (Value × Value)},
    EntryIn (k, v) qs ↔ ∃ q ∈ qs, Equal k q.1 ∧ Equal v q.2
  | [] => by simp; intro h; cases h
  | (k', v') :: qs => by
      constructor
      · intro h
        cases h with
        | here hk hv => exact ⟨(k', v'), by simp, hk, hv⟩
        | there h =>
            obtain ⟨q, hq, hk⟩ := entryIn_iff.1 h
            exact ⟨q, by simp [hq], hk⟩
      · rintro ⟨q, hq, hk, hv⟩
        rcases List.mem_cons.1 hq with rfl | hq
        · exact .here hk hv
        · exact .there (entryIn_iff.2 ⟨q, hq, hk, hv⟩)

theorem entries_iff {qs : List (Value × Value)} : ∀ {ps : List (Value × Value)},
    Entries ps qs ↔ ∀ p ∈ ps, EntryIn p qs
  | [] => by simp [Entries.nil]
  | p :: ps => by
      constructor
      · intro h
        cases h with
        | cons hp hr => exact List.forall_mem_cons.2 ⟨hp, entries_iff.1 hr⟩
      · intro h
        rw [List.forall_mem_cons] at h
        exact .cons h.1 (entries_iff.2 h.2)

theorem memberIn_iff {x : Value} : ∀ {ys : List Value}, MemberIn x ys ↔ ∃ y ∈ ys, Equal x y
  | [] => by simp; intro h; cases h
  | y :: ys => by
      constructor
      · intro h
        cases h with
        | here hy => exact ⟨y, by simp, hy⟩
        | there h =>
            obtain ⟨z, hz, he⟩ := memberIn_iff.1 h
            exact ⟨z, by simp [hz], he⟩
      · rintro ⟨z, hz, he⟩
        rcases List.mem_cons.1 hz with rfl | hz
        · exact .here he
        · exact .there (memberIn_iff.2 ⟨z, hz, he⟩)

theorem members_iff {ys : List Value} : ∀ {xs : List Value},
    Members xs ys ↔ ∀ x ∈ xs, MemberIn x ys
  | [] => by simp [Members.nil]
  | x :: xs => by
      constructor
      · intro h
        cases h with
        | cons hx hr => exact List.forall_mem_cons.2 ⟨hx, members_iff.1 hr⟩
      · intro h
        rw [List.forall_mem_cons] at h
        exact .cons h.1 (members_iff.2 h.2)

/-! ## Soundness of the decision -/

theorem equalFuel_sound : ∀ (n : Nat) (a b : Value) (r : Bool),
    equalFuel n a b = some r → (Equal a b ↔ r = true) := by
  intro n
  induction n with
  | zero => intro a b r h; simp [equalFuel] at h
  | succ n ih =>
      intro a b r h
      have cross : r = false → ¬ Equal a b → (Equal a b ↔ r = true) := by
        intro hr hne; subst hr; simpa using hne
      cases a <;> cases b <;> simp only [equalFuel] at h
      all_goals try
        (simp only [Option.some.injEq] at h
         exact cross h.symm (by intro he; cases he))
      case scalar.scalar a b =>
        simp only [Option.some.injEq] at h; subst h
        constructor
        · intro he; cases he; simp
        · intro hd; simp at hd; subst hd; exact .scalar a
      case integer.integer m k =>
        simp only [Option.some.injEq] at h; subst h
        constructor
        · intro he; cases he; simp
        · intro hd; simp at hd; subst hd; exact .integer m
      case double.double x y =>
        simp only [Option.some.injEq] at h; subst h
        constructor
        · intro he; cases he; assumption
        · intro hd; exact .double hd
      case decimal.decimal x y =>
        simp only [Option.some.injEq] at h; subst h
        constructor
        · intro he; cases he; simpa
        · intro hd; exact .decimal (by simpa using hd)
      case seq.seq xs ys =>
        split at h
        · rename_i hl
          have := all3_sound (P := fun p : Value × Value => Equal p.1 p.2)
            (f := fun p => equalFuel n p.1 p.2) (xs.zip ys)
            (fun p _ r hp => ih p.1 p.2 r hp) r h
          rw [← this]
          constructor
          · intro he; cases he with
            | seq hp => exact (pointwise_iff.1 hp).2
          · intro hall; exact .seq (pointwise_iff.2 ⟨hl, hall⟩)
        · rename_i hl
          simp only [Option.some.injEq] at h
          refine cross h.symm ?_
          intro he; cases he with
          | seq hp => exact hl (pointwise_iff.1 hp).1
      case map.map xs ys =>
        split at h
        · rename_i ps qs hps hqs
          split at h
          · rename_i hl
            have hent : ∀ p ∈ ps, ∀ r', any3 (qs.map fun q =>
                all3 [equalFuel n p.1 q.1, equalFuel n p.2 q.2]) = some r' →
                (EntryIn p qs ↔ r' = true) := by
              intro p _ r' hr'
              obtain ⟨k, v⟩ := p
              rw [entryIn_iff]
              exact any3_sound (P := fun q : Value × Value => Equal k q.1 ∧ Equal v q.2) qs
                (fun q _ r'' hq => and3_sound (ih k q.1) (ih v q.2) hq) r' hr'
            have := all3_sound (P := fun p => EntryIn p qs) ps hent r h
            rw [← this]
            constructor
            · intro he; cases he with
              | map hp hq _ he =>
                  rw [hp] at hps; rw [hq] at hqs
                  cases hps; cases hqs
                  exact entries_iff.1 he
            · intro hall; exact .map hps hqs hl (entries_iff.2 hall)
          · rename_i hl
            simp only [Option.some.injEq] at h
            refine cross h.symm ?_
            intro he; cases he with
            | map hp hq hl' _ =>
                rw [hp] at hps; rw [hq] at hqs
                cases hps; cases hqs
                exact hl hl'
        · cases h
      case set.set xs ys =>
        split at h
        · rename_i hl
          have hmem : ∀ x ∈ xs, ∀ r', any3 (ys.map fun y => equalFuel n x y) = some r' →
              (MemberIn x ys ↔ r' = true) := by
            intro x _ r' hr'
            rw [memberIn_iff]
            exact any3_sound (P := fun y => Equal x y) ys (fun y _ r'' hy => ih x y r'' hy) r' hr'
          have := all3_sound (P := fun x => MemberIn x ys) xs hmem r h
          rw [← this]
          constructor
          · intro he; cases he with
            | set _ hm => exact members_iff.1 hm
          · intro hall; exact .set hl (members_iff.2 hall)
        · rename_i hl
          simp only [Option.some.injEq] at h
          refine cross h.symm ?_
          intro he; cases he with
          | set hl' _ => exact hl hl'

theorem equal?_sound (a b : Value) (r : Bool) (h : equal? a b = some r) :
    Equal a b ↔ r = true :=
  equalFuel_sound _ a b r h

theorem worse_eq_none {i j : Option Issue} : worse i j = none ↔ i = none ∧ j = none := by
  rcases i with _ | (_ | _ | _) <;> rcases j with _ | (_ | _ | _) <;> simp [worse]

theorem pairIssue_none {x y : Value} (h : pairIssue x y = none) : ¬ Equal x y := by
  unfold pairIssue at h
  split at h
  · rename_i hx; simpa using equal?_sound x y false hx
  · cases h
  · cases h

theorem pairIssue_duplicate {x y : Value} (h : pairIssue x y = some .duplicate) :
    Equal x y := by
  unfold pairIssue at h
  split at h
  · cases h
  · rename_i hx; simpa using equal?_sound x y true hx
  · cases h

theorem foldr_none (x : Value) : ∀ ys : List Value,
    ys.foldr (fun y acc => worse (pairIssue x y) acc) none = none → ∀ y ∈ ys, ¬ Equal x y
  | [], _ => by simp
  | y :: ys, h => by
      simp only [List.foldr_cons, worse_eq_none] at h
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact pairIssue_none h.1
      · exact foldr_none x ys h.2 z hz

theorem keysIssue_none : ∀ vs : List Value,
    keysIssue vs = none → vs.Pairwise (fun a b => ¬ Equal a b)
  | [], _ => List.Pairwise.nil
  | x :: xs, h => by
      simp only [keysIssue, worse_eq_none] at h
      exact List.Pairwise.cons (foldr_none x xs h.1) (keysIssue_none xs h.2)

theorem worse_duplicate {i j : Option Issue} (h : worse i j = some .duplicate) :
    i = some .duplicate ∨ j = some .duplicate := by
  rcases i with _ | (_ | _ | _) <;> rcases j with _ | (_ | _ | _) <;> simp_all [worse]

theorem foldr_duplicate (x : Value) : ∀ ys : List Value,
    ys.foldr (fun y acc => worse (pairIssue x y) acc) none = some .duplicate →
      ∃ y ∈ ys, Equal x y
  | [], h => by simp at h
  | y :: ys, h => by
      simp only [List.foldr_cons] at h
      rcases worse_duplicate h with h | h
      · exact ⟨y, by simp, pairIssue_duplicate h⟩
      · obtain ⟨z, hz, he⟩ := foldr_duplicate x ys h
        exact ⟨z, by simp [hz], he⟩

theorem keysIssue_duplicate : ∀ vs : List Value,
    keysIssue vs = some .duplicate → ¬ vs.Pairwise (fun a b => ¬ Equal a b)
  | [], h => by simp [keysIssue] at h
  | x :: xs, h => by
      simp only [keysIssue] at h
      intro hp
      rcases worse_duplicate h with h | h
      · obtain ⟨y, hy, he⟩ := foldr_duplicate x xs h
        exact (List.pairwise_cons.1 hp).1 y hy he
      · exact keysIssue_duplicate xs h (List.pairwise_cons.1 hp).2

end Silmaril.Proofs.Formats.SExp.Clojure

namespace Silmaril.Proofs.Formats.SExp.Clojure

open Silmaril.Formats Silmaril.Formats.Clojure

theorem map_literal_ok {r : Datum} (h : literalIssue .map r = none) :
    (elems r).length % 2 = 0 ∧ ∃ vs, (keysOf (elems r)).mapM toValue = some vs ∧
      vs.Pairwise (fun a b => ¬ Equal a b) := by
  simp only [literalIssue] at h
  split at h
  · cases h
  · rename_i heven
    refine ⟨by simpa using heven, ?_⟩
    split at h
    · rename_i vs hvs; exact ⟨vs, hvs, keysIssue_none vs h⟩
    · cases h

theorem set_literal_ok {r : Datum} (h : literalIssue .set r = none) :
    ∃ vs, (elems r).mapM toValue = some vs ∧ vs.Pairwise (fun a b => ¬ Equal a b) := by
  simp only [literalIssue] at h
  split at h
  · rename_i vs hvs; exact ⟨vs, hvs, keysIssue_none vs h⟩
  · cases h

theorem issue_cons_none {x r : Datum} (h : issue (.cons x r) = none) :
    (∀ m, x = .atom m → literalIssue m r = none) ∧ issue x = none ∧ issue r = none := by
  simp [issue] at h
  obtain ⟨h2, h3, h1⟩ := h
  refine ⟨fun m hm => ?_, h2, h3⟩
  subst hm
  simpa using h1

end Silmaril.Proofs.Formats.SExp.Clojure
