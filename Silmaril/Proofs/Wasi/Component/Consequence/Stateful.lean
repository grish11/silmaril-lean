module

public import Silmaril.Wasi.Component.Consequence.Stateful.Defs
public import Silmaril.Proofs.Wasi.Component.Consequence.Checkers

/-!
# A stateful specification checker: proofs

The events of a generating play (`evsOf`) are computed operation by operation. Every return of
`check` in them answers membership in the state folded from the steps before it (`inv`), and a
trace's last Proponent move lies in a generating play (`Strategy.generatePlays`), so the same
holds in every trace.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasi.Component.Consequence

open Silmaril.Games Silmaril.Wasi Silmaril.Wasi.Accept Silmaril.Wasi.Consequence
open Silmaril.Wasm.Component (Val)

variable {C : Type} [DecidableEq C] {enc : C → Val} {decA decC : List Val → Option C}

/-- The events of an operation. -/
def opEvs (enc : C → Val) (xs : List C) : Op C → List WEv
  | .axiom a => [.call axiomFn [enc a], .ret axiomFn [enc a] (some [])]
  | .reset => [.call resetFn [], .ret resetFn [] (some [])]
  | .check c => [.call checkFn [enc c], .ret checkFn [enc c] (some [.bool (decide (c ∈ xs))])]

/-- The events of a generating play. -/
def evsOf (enc : C → Val) : List C → List (Op C) → List WEv
  | _, [] => []
  | xs, o :: os => opEvs enc xs o ++ evsOf enc (opNext xs o) os

theorem wtrace_playOf (xs : List C) (os : List (Op C)) :
    wtrace (playOf enc xs os) = evsOf enc xs os := by
  induction os generalizing xs with
  | nil => rfl
  | cons o os ih =>
    simp only [playOf, evsOf, wtrace, List.map_append] at ih ⊢
    rw [ih]
    cases o <;> rfl

theorem path_playOf (xs : List C) (os : List (Op C)) :
    Path .idle (playOf enc xs os) .idle := by
  induction os generalizing xs with
  | nil => exact .nil _
  | cons o os ih =>
    refine Path.append_iff.2 ⟨.idle, ?_, ih _⟩
    cases o <;> exact .cons (.ask _) (.cons (.ret _ _) (.nil _))

/-- The observed step of the stateful protocol. -/
abbrev stp (decA : List Val → Option C) : WEv → Option (Step C) :=
  step .call true statefulFns decA

theorem stp_opEvs (hA : ∀ args a, decA args = some a ↔ args = [enc a]) (xs : List C)
    (o : Op C) :
    (opEvs enc xs o).filterMap (stp decA) = match o with
      | .axiom a => [.add a]
      | .reset => [.reset]
      | .check _ => [] := by
  cases o <;>
    simp [opEvs, step, statefulFns, isResetEv, addArgs, axiomFn, resetFn, checkFn,
      (hA _ _).2 rfl]

theorem foldl_stp_opEvs (hA : ∀ args a, decA args = some a ↔ args = [enc a]) (xs : List C)
    (o : Op C) : ((opEvs enc xs o).filterMap (stp decA)).foldl Policy.list.apply xs =
      opNext xs o := by
  rw [stp_opEvs hA]
  cases o <;> rfl

/-- **Every return of `check` in a generating play answers membership in the current state.** -/
theorem inv (hA : ∀ args a, decA args = some a ↔ args = [enc a]) (xs : List C)
    (os : List (Op C)) (s post : List WEv) (args : List Val) (res : Option (List Val))
    (h : evsOf enc xs os = s ++ WEv.ret checkFn args res :: post) :
    ∃ c, args = [enc c] ∧
      res = some [.bool (decide (c ∈ (s.filterMap (stp decA)).foldl Policy.list.apply xs))] := by
  induction os generalizing xs s with
  | nil => simp [evsOf] at h
  | cons o os ih =>
    rcases s with _ | ⟨x, _ | ⟨y, s'⟩⟩
    · cases o <;> simp [evsOf, opEvs] at h
    · cases o <;> simp [evsOf, opEvs, axiomFn, resetFn, checkFn] at h
      obtain ⟨rfl, ⟨rfl, rfl⟩, -⟩ := h
      refine ⟨_, rfl, ?_⟩
      simp [step, statefulFns, isResetEv, addArgs, axiomFn, checkFn]
    · have hsplit : evsOf enc xs (o :: os) = opEvs enc xs o ++ evsOf enc (opNext xs o) os := rfl
      have h2 : (opEvs enc xs o).length = 2 := by cases o <;> rfl
      rw [hsplit] at h
      obtain ⟨hxy, hrest⟩ : [x, y] = opEvs enc xs o ∧
          evsOf enc (opNext xs o) os = s' ++ WEv.ret checkFn args res :: post := by
        have := List.append_inj (s₁ := opEvs enc xs o) (s₂ := [x, y])
          (t₁ := evsOf enc (opNext xs o) os) (t₂ := s' ++ WEv.ret checkFn args res :: post)
          (h.trans (by simp)) (by simp [h2])
        exact ⟨this.1.symm, this.2⟩
      obtain ⟨c, hc, hr⟩ := ih (opNext xs o) s' hrest
      refine ⟨c, hc, ?_⟩
      rw [hr, ← foldl_stp_opEvs hA xs o, ← List.foldl_append, ← List.filterMap_append,
        ← hxy]
      rfl

/-- The events of `xs` asserted, then `check c`. -/
theorem evsOf_axioms_check (xs ys : List C) (c : C) :
    evsOf enc ys (xs.map .axiom ++ [.check c]) =
      (xs.flatMap fun a => [.call axiomFn [enc a], .ret axiomFn [enc a] (some [])]) ++
        [.call checkFn [enc c], .ret checkFn [enc c] (some [.bool (decide (c ∈ ys ++ xs))])] := by
  induction xs generalizing ys with
  | nil => simp [evsOf, opEvs]
  | cons a xs ih =>
    simp only [List.map_cons, List.cons_append, evsOf, opNext, ih, List.flatMap_cons, opEvs]
    simp

theorem stp_axioms (hA : ∀ args a, decA args = some a ↔ args = [enc a]) (xs : List C) :
    (xs.flatMap fun a => [WEv.call axiomFn [enc a], .ret axiomFn [enc a] (some [])]).filterMap
      (stp decA) = xs.map .add := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.flatMap_cons, List.filterMap_append, ih]
    have := stp_opEvs (xs := []) hA (.axiom a)
    rw [show List.filterMap (stp decA) [WEv.call axiomFn [enc a], .ret axiomFn [enc a] (some [])]
      = [Step.add a] by simpa [opEvs] using this]
    rfl

omit [DecidableEq C] in
theorem foldl_add (xs ys : List C) :
    (xs.map Step.add).foldl Policy.list.apply ys = ys ++ xs := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [ih]
    simp [Policy.apply, Policy.list]

/-- **The answers of the stateful checker.** -/
theorem answered_statefulMember (hA : ∀ args a, decA args = some a ↔ args = [enc a])
    (hC : ∀ args c, decC args = some c ↔ args = [enc c]) (xs : List C) (c : C) (a : Answer) :
    Answered (Traces (statefulMember enc)) (exportStateful .call statefulFns Policy.list decA decC)
      xs c a ↔ a = .ofResult (some [.bool (decide (c ∈ xs))]) := by
  constructor
  · rintro ⟨s, e, ⟨p, hp, hw⟩, hr⟩
    cases e with
    | ret g args res =>
      simp only [exportStateful, stateful, Option.map_eq_some_iff, Prod.mk.injEq] at hr
      obtain ⟨⟨c', a'⟩, hcl, rfl, rfl, rfl⟩ := hr
      by_cases hg : g = checkFn
      swap
      · simp [statefulFns, hg] at hcl
      subst hg
      have hclaim : statefulFns.claim = checkFn := rfl
      simp only [hclaim, ite_true, Option.map_eq_some_iff, Prod.mk.injEq] at hcl
      obtain ⟨c'', hdc, rfl, rfl⟩ := hcl
      obtain ⟨-, u, hu, hpu⟩ := hp
      have hpre : p <+: u := by
        rcases hpu with hpu | ⟨p₀, o, rfl, -, hO⟩
        · exact hpu
        · exfalso
          have : wev o = WEv.ret checkFn args res := by
            have := congrArg List.getLast? hw
            simpa [wtrace] using this
          rcases o with (_ | _) | (_ | _) <;> simp_all [wev, Move.IsO]
      rcases hu with rfl | ⟨⟨os, rfl⟩, -⟩
      · obtain rfl := List.prefix_nil.1 hpre
        simp [wtrace] at hw
      obtain ⟨post, hpost⟩ := hpre
      have hev : evsOf enc [] os = s ++ WEv.ret checkFn args res :: wtrace post := by
        rw [← wtrace_playOf, ← hpost, wtrace, List.map_append]
        change wtrace p ++ _ = _
        rw [hw]; simp; rfl
      obtain ⟨c₀, rfl, rfl⟩ := inv hA [] os s (wtrace post) args res hev
      obtain rfl : c₀ = c'' := by
        rw [(hC _ c₀).2 rfl] at hdc; exact Option.some.inj hdc
      rfl
    | _ => simp [exportStateful, stateful] at hr
  · rintro rfl
    refine ⟨(xs.flatMap fun a => [WEv.call axiomFn [enc a], .ret axiomFn [enc a] (some [])]) ++
      [.call checkFn [enc c]], .ret checkFn [enc c] (some [.bool (decide (c ∈ [] ++ xs))]),
      ⟨playOf enc [] (xs.map .axiom ++ [.check c]),
        Strategy.subset_generate ⟨_, rfl⟩ ⟨_, path_playOf _ _⟩, ?_⟩, ?_⟩
    · rw [wtrace_playOf, evsOf_axioms_check]; simp
    · have hs : List.filterMap (step .call true statefulFns decA)
          (xs.flatMap fun a => [WEv.call axiomFn [enc a], .ret axiomFn [enc a] (some [])]) =
          xs.map .add := stp_axioms hA xs
      have hck : step .call true statefulFns decA (.call checkFn [enc c]) = none := by
        simp [step, statefulFns, isResetEv, addArgs, axiomFn, resetFn, checkFn]
      have hclaim : statefulFns.claim = checkFn := rfl
      simp only [exportStateful, stateful, hclaim, ite_true, (hC _ _).2 rfl, Option.map_some,
        epochState, List.filterMap_append, hs, List.filterMap_cons, hck, List.filterMap_nil,
        List.append_nil, List.nil_append]
      rw [foldl_add]; rfl

end Silmaril.Proofs.Wasi.Component.Consequence

namespace Silmaril.Proofs.Wasi.Component.Consequence

open Silmaril.Wasi Silmaril.Wasi.Accept Silmaril.Wasi.Consequence
open Silmaril.Wasm.Component (Val)

theorem u32Arg_iff (args : List Val) (c : BitVec 32) :
    u32Arg args = some c ↔ args = [.u32 c] := by
  rcases args with _ | ⟨a, _ | _⟩ <;> simp [u32Arg, args1, ofU32?_eq_some]

end Silmaril.Proofs.Wasi.Component.Consequence
