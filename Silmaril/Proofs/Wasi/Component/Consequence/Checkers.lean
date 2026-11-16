module

public import Silmaril.Wasi.Component.Consequence.Checkers.Defs
public import Silmaril.Proofs.Wasi.Component.Consequence.Basic
public import Silmaril.Wasi.Component.Accept.Thms

/-!
# Specification checker components: proofs

`answerChecker enc ans` is a generated strategy: each generating play is one call of `check`
with the encoding of a query `q`, answered `ans q`. Its returns are Proponent moves, so they are
read off the generating plays (`Strategy.accepted_generate`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasi.Component.Consequence

open Silmaril.Games Silmaril.Games.Accept Silmaril.Wasi Silmaril.Wasi.Accept
  Silmaril.Wasi.Consequence
open Silmaril.Wasm.Component (Val)

variable {Q : Type} {enc : Q → List Val} {ans : Q → Bool}

/-- The returns of a move. -/
def retObs {I X : Set FnName} (m : Move (nsig I) (nsig X)) :
    Option (FnName × List Val × Option (List Val)) :=
  match wev m with
  | .ret g args res => some (g, args, res)
  | _ => none

theorem retObs_not_isO {I X : Set FnName} (m : Move (nsig I) (nsig X)) (a)
    (h : retObs m = some a) : ¬ m.IsO := by
  rcases m with (_ | _) | (_ | _) <;> simp_all [retObs, wev, Move.IsO]

/-- **The returns of the checker** are the answers to encoded queries. -/
theorem ret_answerChecker {s : List WEv} {g : FnName} {args : List Val}
    {res : Option (List Val)} (h : s ++ [.ret g args res] ∈ Traces (answerChecker enc ans)) :
    ∃ q, g = checkFn ∧ args = enc q ∧ res = some [.bool (ans q)] := by
  obtain ⟨p, hp, hw⟩ := h
  have hacc : (g, args, res) ∈ (answerChecker enc ans).accepted retObs := by
    obtain ⟨l₁, l₂, rfl, -, h₂⟩ := List.map_eq_append_iff.1 hw
    obtain ⟨m, rfl⟩ : ∃ m, l₂ = [m] := by
      rcases l₂ with _ | ⟨m, _ | _⟩ <;> simp_all
    refine ⟨l₁ ++ [m], hp, m, by simp, ?_⟩
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h₂
    simp [retObs, h₂]
  rw [answerChecker, Strategy.accepted_generate retObs_not_isO] at hacc
  obtain ⟨u, ⟨⟨q, rfl⟩, -⟩, m, hm, ho⟩ := hacc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> simp [retObs, wev] at ho
  exact ⟨q, ho.1.symm, ho.2.1.symm, ho.2.2.symm⟩

/-- The checker answers every encoded query. -/
theorem play_answerChecker (q : Q) :
    [] ++ [WEv.call checkFn (enc q), .ret checkFn (enc q) (some [.bool (ans q)])] ∈
      Traces (answerChecker enc ans) := by
  refine ⟨_, Strategy.subset_generate ⟨q, rfl⟩
    ⟨_, .cons (.ask _) (.cons (.ret _ _) (.nil _))⟩, ?_⟩
  rfl

variable {X C : Type} {dec : List Val → Option (X × C)}

/-- **Answers of the checker**: exactly `ans (x, c)`, when the decoder inverts the encoding. -/
theorem answered_answerChecker {enc : X × C → List Val} {ans : X × C → Bool}
    (hdec : ∀ args q, dec args = some q ↔ args = enc q) (x : X) (c : C) (a : Answer) :
    Answered (Traces (answerChecker enc ans)) (exportCheck checkFn dec) x c a ↔
      a = .ofResult (some [.bool (ans (x, c))]) := by
  constructor
  · rintro ⟨s, e, hT, hr⟩
    cases e with
    | ret g args res =>
      obtain ⟨q, rfl, rfl, rfl⟩ := ret_answerChecker hT
      simp only [exportCheck, ite_true, Option.map_eq_some_iff, Prod.mk.injEq] at hr
      obtain ⟨p, hp, rfl, rfl, rfl⟩ := hr
      rw [(hdec _ _).2 rfl] at hp
      cases hp
      rfl
    | _ => simp [exportCheck] at hr
  · rintro rfl
    refine ⟨[WEv.call checkFn (enc (x, c))], _, play_answerChecker (x, c), ?_⟩
    simp [exportCheck, (hdec _ _).2 rfl]

/-- The silent checker never returns. -/
theorem not_ret_silentChecker {s : List WEv} {g : FnName} {args : List Val}
    {res : Option (List Val)} : s ++ [.ret g args res] ∉ Traces silentChecker := by
  rintro ⟨p, hp, hw⟩
  have hacc : (g, args, res) ∈ silentChecker.accepted retObs := by
    obtain ⟨l₁, l₂, rfl, -, h₂⟩ := List.map_eq_append_iff.1 hw
    obtain ⟨m, rfl⟩ : ∃ m, l₂ = [m] := by
      rcases l₂ with _ | ⟨m, _ | _⟩ <;> simp_all
    refine ⟨l₁ ++ [m], hp, m, by simp, ?_⟩
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h₂
    simp [retObs, h₂]
  rw [silentChecker, Strategy.accepted_generate retObs_not_isO] at hacc
  obtain ⟨u, ⟨hu, -⟩, -⟩ := hacc
  exact hu

theorem not_answered_silentChecker (x : X) (c : C) (a : Answer) :
    ¬ Answered (Traces silentChecker) (exportCheck checkFn dec) x c a := by
  rintro ⟨s, e, hT, hr⟩
  cases e with
  | ret g args res => exact not_ret_silentChecker hT
  | _ => simp [exportCheck] at hr

theorem ofU32?_eq_some {v : Val} {y : BitVec 32} : ofU32? v = some y ↔ v = .u32 y := by
  cases v <;> simp [ofU32?]

theorem ofRecord?_eq_some {v : Val} {vs : List Val} : ofRecord? v = some vs ↔ v = .record vs := by
  cases v <;> simp [ofRecord?]

theorem mapM_ofU32?_eq_some (vs : List Val) (xs : List (BitVec 32)) :
    vs.mapM ofU32? = some xs ↔ vs = xs.map .u32 := by
  induction vs generalizing xs with
  | nil => cases xs <;> simp
  | cons v vs ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq]
    constructor
    · rintro ⟨y, hy, ys, hys, rfl⟩
      simp [ofU32?_eq_some.1 hy, (ih ys).1 hys]
    · intro h
      cases xs with
      | nil => cases h
      | cons y ys =>
        simp only [List.map_cons, List.cons.injEq] at h
        exact ⟨y, ofU32?_eq_some.2 h.1, ys, (ih ys).2 h.2, rfl⟩

theorem u32s?_eq_some {v : Val} {xs : List (BitVec 32)} :
    u32s? v = some xs ↔ v = .record (xs.map .u32) := by
  simp only [u32s?, Option.bind_eq_some_iff, ofRecord?_eq_some, mapM_ofU32?_eq_some]
  constructor
  · rintro ⟨vs, rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨_, rfl, rfl⟩

theorem u32Dec_iff (args : List Val) (q : List (BitVec 32) × BitVec 32) :
    u32Dec args = some q ↔ args = u32Enc q := by
  obtain ⟨xs, y⟩ := q
  rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;>
    simp [u32Dec, args2, u32Enc, Option.bind_eq_some_iff, u32s?_eq_some, ofU32?_eq_some]

end Silmaril.Proofs.Wasi.Component.Consequence
