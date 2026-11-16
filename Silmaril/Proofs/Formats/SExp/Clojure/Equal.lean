module

public import Silmaril.Formats.SExp.Clojure.Defs

/-! # Proofs: the Clojure key-equality decision is sound for `Equal` -/

@[expose] public section

namespace Silmaril.Proofs.Formats.SExp.Clojure

open Silmaril.Formats Silmaril.Formats.Clojure

theorem collEqual?_sound {R : List Value → List Value → Prop}
    (hlen : ∀ xs ys, R xs ys → xs.length = ys.length) (hnil : R [] [])
    {xs ys : List Value} {r : Bool} (h : collEqual? xs ys = some r) : R xs ys ↔ r = true := by
  unfold collEqual? at h
  split at h
  · rename_i hne
    cases h
    exact ⟨fun hr => absurd (hlen _ _ hr) hne, fun h => by cases h⟩
  · split at h
    · rename_i hx
      cases h
      subst hx
      have : ys = [] := by
        rename_i hl; simp only [ne_eq, Decidable.not_not, List.length_nil] at hl
        exact List.eq_nil_of_length_eq_zero hl.symm
      subst this
      simp [hnil]
    · cases h

mutual
  theorem equal?_sound (Q : CollEq) : ∀ (a b : Value) (r : Bool),
      equal? a b = some r → (Equal Q a b ↔ r = true)
    | .scalar a, b, r, h => by
        cases b <;> simp_all [equal?, Equal]
        subst h; simp
    | .integer m, b, r, h => by
        cases b <;> simp_all [equal?, Equal]
        subst h; simp
    | .double x, b, r, h => by cases b <;> simp_all [equal?, Equal]
    | .decimal x, b, r, h => by
        cases b <;> simp_all [equal?, Equal]
        subst h; simp
    | .seq xs, b, r, h => by
        cases b with
        | seq ys =>
            simp only [equal?] at h
            simp only [Equal]
            exact equalList?_sound Q xs ys r h
        | _ => simp_all [equal?, Equal]
    | .map xs, b, r, h => by
        cases b with
        | map ys =>
            simp only [equal?] at h
            simp only [Equal]
            exact collEqual?_sound Q.map_length Q.map_nil h
        | _ => simp_all [equal?, Equal]
    | .set xs, b, r, h => by
        cases b with
        | set ys =>
            simp only [equal?] at h
            simp only [Equal]
            exact collEqual?_sound Q.set_length Q.set_nil h
        | _ => simp_all [equal?, Equal]

  theorem equalList?_sound (Q : CollEq) : ∀ (xs ys : List Value) (r : Bool),
      equalList? xs ys = some r → (EqualList Q xs ys ↔ r = true)
    | [], [], r, h => by simp_all [equalList?, EqualList]
    | [], _ :: _, r, h => by simp_all [equalList?, EqualList]
    | _ :: _, [], r, h => by simp_all [equalList?, EqualList]
    | x :: xs, y :: ys, r, h => by
        simp only [EqualList]
        simp only [equalList?] at h
        cases hx : equal? x y with
        | none =>
            cases hr : equalList? xs ys with
            | none => simp [hx, hr] at h
            | some b =>
                cases b
                · simp [hx, hr] at h; subst h
                  have := (equalList?_sound Q xs ys false hr)
                  simp only [Bool.false_eq_true, iff_false] at this
                  simp [this]
                · simp [hx, hr] at h
        | some a =>
            have ha := equal?_sound Q x y a hx
            cases a
            · simp [hx] at h; subst h
              simp only [Bool.false_eq_true, iff_false] at ha
              simp [ha]
            · cases hr : equalList? xs ys with
              | none => simp [hx, hr] at h
              | some b =>
                  have hb := equalList?_sound Q xs ys b hr
                  cases b
                  · simp [hx, hr] at h; subst h
                    simp only [Bool.false_eq_true, iff_false] at hb
                    simp [hb]
                  · simp [hx, hr] at h; subst h
                    simp only [iff_true] at ha hb
                    simp [ha, hb]
end

theorem worse_eq_none {i j : Option Issue} : worse i j = none ↔ i = none ∧ j = none := by
  rcases i with _ | (_ | _ | _) <;> rcases j with _ | (_ | _ | _) <;> simp [worse]

theorem pairIssue_none (Q : CollEq) {x y : Value} (h : pairIssue x y = none) : ¬ Equal Q x y := by
  unfold pairIssue at h
  split at h
  · rename_i hx; simpa using equal?_sound Q x y false hx
  · cases h
  · cases h

theorem pairIssue_duplicate (Q : CollEq) {x y : Value} (h : pairIssue x y = some .duplicate) :
    Equal Q x y := by
  unfold pairIssue at h
  split at h
  · cases h
  · rename_i hx; simpa using equal?_sound Q x y true hx
  · cases h

theorem foldr_none (Q : CollEq) (x : Value) : ∀ ys : List Value,
    ys.foldr (fun y acc => worse (pairIssue x y) acc) none = none → ∀ y ∈ ys, ¬ Equal Q x y
  | [], _ => by simp
  | y :: ys, h => by
      simp only [List.foldr_cons, worse_eq_none] at h
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact pairIssue_none Q h.1
      · exact foldr_none Q x ys h.2 z hz

theorem keysIssue_none (Q : CollEq) : ∀ vs : List Value,
    keysIssue vs = none → vs.Pairwise (fun a b => ¬ Equal Q a b)
  | [], _ => List.Pairwise.nil
  | x :: xs, h => by
      simp only [keysIssue, worse_eq_none] at h
      exact List.Pairwise.cons (foldr_none Q x xs h.1) (keysIssue_none Q xs h.2)

theorem worse_duplicate {i j : Option Issue} (h : worse i j = some .duplicate) :
    i = some .duplicate ∨ j = some .duplicate := by
  rcases i with _ | (_ | _ | _) <;> rcases j with _ | (_ | _ | _) <;> simp_all [worse]

theorem foldr_duplicate (Q : CollEq) (x : Value) : ∀ ys : List Value,
    ys.foldr (fun y acc => worse (pairIssue x y) acc) none = some .duplicate →
      ∃ y ∈ ys, Equal Q x y
  | [], h => by simp at h
  | y :: ys, h => by
      simp only [List.foldr_cons] at h
      rcases worse_duplicate h with h | h
      · exact ⟨y, by simp, pairIssue_duplicate Q h⟩
      · obtain ⟨z, hz, he⟩ := foldr_duplicate Q x ys h
        exact ⟨z, by simp [hz], he⟩

theorem keysIssue_duplicate (Q : CollEq) : ∀ vs : List Value,
    keysIssue vs = some .duplicate → ¬ vs.Pairwise (fun a b => ¬ Equal Q a b)
  | [], h => by simp [keysIssue] at h
  | x :: xs, h => by
      simp only [keysIssue] at h
      intro hp
      rcases worse_duplicate h with h | h
      · obtain ⟨y, hy, he⟩ := foldr_duplicate Q x xs h
        exact (List.pairwise_cons.1 hp).1 y hy he
      · exact keysIssue_duplicate Q xs h (List.pairwise_cons.1 hp).2

end Silmaril.Proofs.Formats.SExp.Clojure

namespace Silmaril.Proofs.Formats.SExp.Clojure

open Silmaril.Formats Silmaril.Formats.Clojure

theorem map_literal_ok (Q : CollEq) {r : Datum} (h : literalIssue .map r = none) :
    (elems r).length % 2 = 0 ∧ ∃ vs, (keysOf (elems r)).mapM toValue = some vs ∧
      vs.Pairwise (fun a b => ¬ Equal Q a b) := by
  simp only [literalIssue] at h
  split at h
  · cases h
  · rename_i heven
    refine ⟨by simpa using heven, ?_⟩
    split at h
    · rename_i vs hvs; exact ⟨vs, hvs, keysIssue_none Q vs h⟩
    · cases h

theorem set_literal_ok (Q : CollEq) {r : Datum} (h : literalIssue .set r = none) :
    ∃ vs, (elems r).mapM toValue = some vs ∧ vs.Pairwise (fun a b => ¬ Equal Q a b) := by
  simp only [literalIssue] at h
  split at h
  · rename_i vs hvs; exact ⟨vs, hvs, keysIssue_none Q vs h⟩
  · cases h

theorem issue_cons_none {x r : Datum} (h : issue (.cons x r) = none) :
    (∀ m, x = .atom m → literalIssue m r = none) ∧ issue x = none ∧ issue r = none := by
  simp [issue] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun m hm => ?_, h2, h3⟩
  subst hm
  simpa using h1

end Silmaril.Proofs.Formats.SExp.Clojure
