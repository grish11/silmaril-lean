module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.Det
public import Silmaril.Wasm.Game.Trapped.Thms

/-!
# A refused host call ends the round in a trap

A host call answered by a refusal is a core import call answered by a trap
(`payloadAnswer _ none = .trap`). The importer's thread resumes trapped (`E.fill [TRAP]`), host-free
steps keep it trapped (`trapped_step`), a trapped code decomposes to no callout
(`decompose?_fill_trap`) and is a result only as a trap (`trapped_eq_toAdmin`). So the core
instance makes no further import call and answers the trap (`path_trapped`), and in a
`SessSpec` round a refused host call is the last host call and the outcome is a trap
(`refuse_last`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core (Store Admin Result)
open Silmaril.Wasm.SingleThreaded (Ctx Thread decompose? splitVals)
open Silmaril.Wasm.Game (ScalarInstance Answer)

local notation "IVal" => Silmaril.Wasm.Component.Val

/-! ## Trapped code -/

/-- **A trapped code has no callout.** -/
theorem decompose?_fill_trap {H : Type} (s : Store H) :
    ∀ E : Ctx, decompose? s (E.fill [.trap]) = none
  | .top pre rest => by
    have hs : splitVals (Ctx.fill (.top pre rest) [.trap]) = (pre, .trap :: rest) := by
      simpa [Ctx.fill] using Silmaril.Wasm.SingleThreaded.splitVals_vals_cons (vs := pre)
        (d := .trap) rfl rest
    rw [Silmaril.Wasm.SingleThreaded.decompose?_of_split hs]
    rfl
  | .label pre n cont E rest => by
    have hs : splitVals (Ctx.fill (.label pre n cont E rest) [.trap]) =
        (pre, .label n cont (E.fill [.trap]) :: rest) := by
      simpa [Ctx.fill] using Silmaril.Wasm.SingleThreaded.splitVals_vals_cons (vs := pre)
        (d := .label n cont (E.fill [.trap])) rfl rest
    rw [Silmaril.Wasm.SingleThreaded.decompose?_of_split hs]
    simp [Silmaril.Wasm.SingleThreaded.decompHead, decompose?_fill_trap s E]
  | .handler pre n cs E rest => by
    have hs : splitVals (Ctx.fill (.handler pre n cs E rest) [.trap]) =
        (pre, .handler n cs (E.fill [.trap]) :: rest) := by
      simpa [Ctx.fill] using Silmaril.Wasm.SingleThreaded.splitVals_vals_cons (vs := pre)
        (d := .handler n cs (E.fill [.trap])) rfl rest
    rw [Silmaril.Wasm.SingleThreaded.decompose?_of_split hs]
    simp [Silmaril.Wasm.SingleThreaded.decompHead, decompose?_fill_trap s E]
  | .frame pre n f E rest => by
    have hs : splitVals (Ctx.fill (.frame pre n f E rest) [.trap]) =
        (pre, .frame n f (E.fill [.trap]) :: rest) := by
      simpa [Ctx.fill] using Silmaril.Wasm.SingleThreaded.splitVals_vals_cons (vs := pre)
        (d := .frame n f (E.fill [.trap])) rfl rest
    rw [Silmaril.Wasm.SingleThreaded.decompose?_of_split hs]
    simp [Silmaril.Wasm.SingleThreaded.decompHead, decompose?_fill_trap s E]

/-- A trapped thread. -/
def Trapped (t : Thread) : Prop := ∃ (fr : Silmaril.Wasm.Execution.Core.Frame) (E : Ctx),
  t = .active fr (E.fill [.trap])

/-- **Host-free runs keep a thread trapped.** -/
theorem reach_trapped {P : Profile} {x y : Store Nat × Thread}
    (h : Silmaril.Wasm.Game.Reach P x y) (hx : Trapped x.2) : Trapped y.2 := by
  induction h with
  | refl => exact hx
  | tail _ hst ih =>
    obtain ⟨fr, E, he⟩ := ih
    obtain ⟨f', code', hy, hs⟩ := hst
    rw [he] at hs
    obtain ⟨-, -, E', hc⟩ := Silmaril.Wasm.Game.trapped_step hs
    exact ⟨f', E', by rw [hy]; simpa using hc⟩

/-- **A trapped thread makes no further import call and answers a trap.** -/
theorem path_trapped {P : Profile} {I : ScalarInstance} {f : I.F.Op} {s : Store Nat} {t : Thread}
    (ht : Trapped t) {m : Move I.E I.F} {p : List (Move I.E I.F)} {q : I.HState}
    (h : I.Path P (.running f s t) (m :: p) q) :
    m = .inr (.ans f .trap) := by
  cases h with
  | cons ht' _ =>
    cases ht' with
    | ucall run callout _ =>
      obtain ⟨fr, E, he⟩ := reach_trapped run ht
      obtain ⟨E₀, a, hd⟩ := callout
      simp only at he
      rw [he] at hd
      simp [Thread.config, decompose?_fill_trap] at hd
    | oret run final answer =>
      obtain ⟨fr, E, he⟩ := reach_trapped run ht
      simp only at he
      unfold Silmaril.Wasm.Game.ResultAt at final
      rw [he] at final
      have hr := Silmaril.Wasm.Game.trapped_eq_toAdmin final
      subst hr
      simp only [Silmaril.Wasm.Game.Answer.ofResult?, Option.some.injEq] at answer
      rw [answer]

/-- After a callout, a trap answer resumes the thread trapped. -/
theorem trapped_resume {s : Store Nat} {t : Thread} {h : Nat} {args : List Silmaril.Wasm.Execution.Core.Val}
    (hc : Silmaril.Wasm.Game.CalloutAt s t h args) :
    Trapped (Silmaril.Wasm.SingleThreaded.resumeResult s t .trap) := by
  obtain ⟨E, a, hd⟩ := hc
  refine ⟨(t.config s).frame, E, ?_⟩
  simp only [Silmaril.Wasm.SingleThreaded.resumeResult, hd]
  rfl


/-! ## Rounds -/

variable {l : HLinked2} {Ie Ii : ScalarInstance}

theorem hostCalls_nil : l.hostCalls [] = [] := rfl

/-- The host calls of one core import call: none, or one, and a refused one is answered to the
core by a trap. -/
theorem impRel_hostCalls {c : Σ e : Ii.E.Op, Ii.E.Ar e}
    {ds : List (Call (sigN l.imp.imports.length))}
    (h : Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii c ds) :
    l.hostCalls ds = [] ∨ ∃ y, l.hostCalls ds = [y] ∧ (y.2 = none → c.2 = .trap) := by
  obtain ⟨e, n⟩ := c
  obtain ⟨nm, ft, A, hi, hA, hm⟩ := h
  simp only at hA hm ⊢
  revert hm
  cases liftArgs ft.params (e.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat?) with
  | none =>
    rintro ⟨-, rfl⟩
    exact .inl hostCalls_nil
  | some ws =>
    rintro ⟨hk, R, rfl, rfl⟩
    cases hx : l.hostCall? ⟨(⟨e.1.val, hk⟩, .vals ws), R⟩ with
    | none => exact .inl (by simp [HLinked2.hostCalls, hx])
    | some y =>
      refine .inr ⟨y, by simp [HLinked2.hostCalls, hx], fun hy => ?_⟩
      have hR : y.2 = R := by
        simp only [HLinked2.hostCall?] at hx
        split at hx
        · cases hx; rfl
        · cases hx
      rw [← hA, ← hR, hy]
      rfl

/-- **In the import calls of a round, a refused host call is the last host call and the round
answers a trap.** -/
theorem calls_refuse_last {P : Profile} {f : Ii.F.Op} :
    ∀ (cs : List (Σ e : Ii.E.Op, Ii.E.Ar e))
      (dss : List (List (Call (sigN l.imp.imports.length)))) (s : Store Nat) (t : Thread)
      (w : Ii.F.Ar f) (q : Ii.HState) (H₁ H₂ : List (Call (sigN l.host.length)))
      (m : (sigN l.host.length).Op),
      List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii) cs dss →
      Ii.Path P (.running f s t)
        (Silmaril.Wasm.Component.Reference.callMoves cs ++ [.inr (.ans f w)]) q →
      l.hostCalls dss.flatten = H₁ ++ ⟨m, none⟩ :: H₂ → H₂ = [] ∧ w = .trap
  | [], dss, _, _, _, _, H₁, H₂, m, hr, _, hH => by
    cases hr
    simp [HLinked2.hostCalls] at hH
  | c :: cs, dss, s, t, w, q, H₁, H₂, m, hr, hp, hH => by
    obtain ⟨ds, dss', hd, hr', rfl⟩ := List.forall₂_cons_left_iff.mp hr
    rw [List.flatten_cons, hostCalls_append] at hH
    have hsh := impRel_hostCalls hd
    obtain ⟨e, n⟩ := c
    simp only [Silmaril.Wasm.Component.Reference.callMoves, List.cons_append] at hp
    cases hp with
    | cons h₁ hp =>
      cases h₁ with
      | ucall run callout op =>
        cases hp with
        | cons h₂ hp =>
          cases h₂ with
          | uret _ =>
            rcases hsh with hn | ⟨y, hy, htr⟩
            · rw [hn, List.nil_append] at hH
              exact calls_refuse_last cs dss' _ _ w q H₁ H₂ m hr' hp hH
            · rw [hy, List.singleton_append] at hH
              rcases H₁ with _ | ⟨y', H₁'⟩
              · simp only [List.nil_append, List.cons.injEq] at hH
                obtain ⟨rfl, hrest⟩ := hH
                have hn : n = .trap := htr rfl
                subst hn
                have ht := trapped_resume callout
                rcases cs with _ | ⟨c', cs'⟩
                · cases hr'
                  refine ⟨by simpa [HLinked2.hostCalls] using hrest.symm, ?_⟩
                  have := path_trapped ht hp
                  simp only [Sum.inr.injEq, Ev.ans.injEq, heq_eq_eq, true_and] at this
                  exact this
                · obtain ⟨e', n'⟩ := c'
                  simp only [Silmaril.Wasm.Component.Reference.callMoves, List.cons_append] at hp
                  have := path_trapped ht hp
                  cases this
              · simp only [List.cons_append, List.cons.injEq] at hH
                exact calls_refuse_last cs dss' _ _ w q H₁' H₂ m hr' hp hH.2

/-- **In a round, a refused host call is the last host call and the outcome is a trap.** -/
theorem refuse_last {P : Profile} {u π u' π' : Store Nat} {j : Fin l.imp.exports.length}
    {vs : List IVal} {o : Option (List IVal)} {H : List (Call (sigN l.host.length))}
    (h : HLinked2.SessSpec P l Ie Ii u π [(j, vs)] [o] [H] u' π')
    {H₁ H₂ : List (Call (sigN l.host.length))} {m : (sigN l.host.length).Op}
    (hH : H = H₁ ++ ⟨m, none⟩ :: H₂) : H₂ = [] ∧ o = none := by
  obtain ⟨⟨j₁, vs₁, f, cs, w, dss⟩, -, -, ⟨xs, -, -, -, hrel⟩, hp, -, hans, rfl⟩ :=
    sessSpec_singleH h
  simp only [Linked2.SessRound.instMoves] at hp hrel hH hans
  cases hp with
  | cons h₁ hp =>
    cases h₁ with
    | call =>
      obtain ⟨rfl, hw⟩ := calls_refuse_last cs dss _ _ w _ H₁ H₂ m hrel hp hH
      subst hw
      refine ⟨rfl, ?_⟩
      simp only [Linked2.SessRound.ans, answerPayload, Option.bind_none] at hans
      cases o with
      | none => rfl
      | some _ => cases hans

/-! ## Diverging rounds and host chatter -/

/-- In the import calls of a round still running, a refused host call is the last host call and
leaves the thread trapped. -/
theorem calls_refuse_trapped {P : Profile} {f : Ii.F.Op} :
    ∀ (cs : List (Σ e : Ii.E.Op, Ii.E.Ar e))
      (dss : List (List (Call (sigN l.imp.imports.length)))) (s : Store Nat) (t : Thread)
      (s' : Store Nat) (t' : Thread) (H₁ H₂ : List (Call (sigN l.host.length)))
      (m : (sigN l.host.length).Op),
      List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii) cs dss →
      Ii.Path P (.running f s t) (Silmaril.Wasm.Component.Reference.callMoves cs)
        (.running f s' t') →
      l.hostCalls dss.flatten = H₁ ++ ⟨m, none⟩ :: H₂ → H₂ = [] ∧ Trapped t'
  | [], dss, _, _, _, _, H₁, H₂, m, hr, _, hH => by
    cases hr
    simp [HLinked2.hostCalls] at hH
  | c :: cs, dss, s, t, s', t', H₁, H₂, m, hr, hp, hH => by
    obtain ⟨ds, dss', hd, hr', rfl⟩ := List.forall₂_cons_left_iff.mp hr
    rw [List.flatten_cons, hostCalls_append] at hH
    have hsh := impRel_hostCalls hd
    obtain ⟨e, n⟩ := c
    simp only [Silmaril.Wasm.Component.Reference.callMoves] at hp
    cases hp with
    | cons h₁ hp =>
      cases h₁ with
      | ucall run callout op =>
        cases hp with
        | cons h₂ hp =>
          cases h₂ with
          | uret _ =>
            rcases hsh with hn | ⟨y, hy, htr⟩
            · rw [hn, List.nil_append] at hH
              exact calls_refuse_trapped cs dss' _ _ s' t' H₁ H₂ m hr' hp hH
            · rw [hy, List.singleton_append] at hH
              rcases H₁ with _ | ⟨y', H₁'⟩
              · simp only [List.nil_append, List.cons.injEq] at hH
                obtain ⟨rfl, hrest⟩ := hH
                have hn : n = .trap := htr rfl
                subst hn
                have ht := trapped_resume callout
                rcases cs with _ | ⟨c', cs'⟩
                · cases hr'
                  cases hp
                  exact ⟨by simpa [HLinked2.hostCalls] using hrest.symm, ht⟩
                · obtain ⟨e', n'⟩ := c'
                  simp only [Silmaril.Wasm.Component.Reference.callMoves] at hp
                  have := path_trapped ht hp
                  cases this
              · simp only [List.cons_append, List.cons.injEq] at hH
                exact calls_refuse_trapped cs dss' _ _ s' t' H₁' H₂ m hr' hp hH.2

/-- **A trapped thread does not diverge host-free.** -/
theorem not_divB_trapped {P : Profile} {s : Store Nat} {t : Thread} (ht : Trapped t) :
    ¬ Linked2.DivB P s t := by
  rintro ⟨g, hg0, hg⟩
  obtain ⟨fr₀, E₀, he₀⟩ := ht
  have key : ∀ k, ∃ (fr : Silmaril.Wasm.Execution.Core.Frame) (E : Ctx),
      (g k).2 = .active fr (E.fill [.trap]) ∧ sizeOf (E.fill [.trap]) + k ≤ sizeOf (E₀.fill [.trap]) := by
    intro k
    induction k with
    | zero => exact ⟨fr₀, E₀, by rw [hg0]; exact he₀, by simp⟩
    | succ k ih =>
      obtain ⟨fr, E, he, hle⟩ := ih
      obtain ⟨f', code', hy, hs⟩ := hg k
      rw [he] at hs
      obtain ⟨-, -, E', hc⟩ := Silmaril.Wasm.Game.trapped_step hs
      have hlt := Silmaril.Wasm.Game.trapped_step_lt hs
      simp only at hc hlt
      refine ⟨f', E', by rw [hy, ← hc], ?_⟩
      rw [← hc]
      omega
  obtain ⟨_, _, _, hle⟩ := key (sizeOf (E₀.fill [.trap]) + 1)
  omega

/-- **A diverging round makes no refused host call.** -/
theorem roundDivC_no_refuse {P : Profile} {u π : Store Nat} {j : Fin l.imp.exports.length}
    {vs : List IVal} {c : List (Call (sigN l.host.length))}
    (h : HLinked2.RoundDivC P l Ie Ii u π j vs c) {H₁ H₂ : List (Call (sigN l.host.length))}
    {m : (sigN l.host.length).Op} (hc : c = H₁ ++ ⟨m, none⟩ :: H₂) : False := by
  obtain ⟨⟨j₁, vs₁, f, cs, dss⟩, s, t, π₁, -, -, ⟨xs, -, -, -, hrel⟩, hp, -, hH, hdiv⟩ := h
  simp only [Linked2.DivRound.instMoves] at hp hrel hH hdiv
  subst hc
  cases hp with
  | cons h₁ hp =>
    cases h₁ with
    | call =>
      obtain ⟨-, ht⟩ := calls_refuse_trapped cs dss _ _ s t H₁ H₂ m hrel hp hH
      rcases hdiv with hd | ⟨e, _, _, _, _, _, _, hpe, _⟩ | ⟨q, c₀, _, _, hq0, _, hk⟩
      · exact not_divB_trapped ht hd
      · cases path_trapped ht hpe
      · have hp0 := (hk 0).1
        rw [hq0] at hp0
        obtain ⟨e, n⟩ := c₀ 0
        simp only [Silmaril.Wasm.Component.Reference.callMoves] at hp0
        cases path_trapped ht hp0

/-- **Every host call of host chatter is answered.** -/
theorem roundInfC_no_refuse {P : Profile} {u π : Store Nat} {j : Fin l.imp.exports.length}
    {vs : List IVal} {ω : ℕ → Call (sigN l.host.length)}
    (h : HLinked2.RoundInfC P l Ie Ii u π j vs ω) (i : ℕ) : (ω i).2 ≠ none := by
  obtain ⟨f, xs, q, c, ds, πs, N, -, -, -, -, -, hN0, hk, hunb⟩ := h
  have seg : ∀ k, ∀ x ∈ l.hostCalls (ds k), x.2 ≠ none := by
    intro k x hx hxn
    obtain ⟨hp, hd, -, -⟩ := hk k
    rcases impRel_hostCalls hd with hn | ⟨y, hy, htr⟩
    · rw [hn] at hx; cases hx
    · rw [hy, List.mem_singleton] at hx
      subst hx
      have htrap := htr hxn
      have hp' := (hk (k + 1)).1
      generalize c k = ck at hp htrap
      generalize c (k + 1) = ck' at hp'
      generalize q (k + 1 + 1) = q2 at hp'
      generalize q (k + 1) = q1 at hp hp'
      generalize q k = q0 at hp
      obtain ⟨e, n⟩ := ck
      simp only at htrap
      subst htrap
      simp only [Silmaril.Wasm.Component.Reference.callMoves] at hp
      cases hp with
      | cons h₁ hp =>
        cases h₁ with
        | ucall run callout op =>
          cases hp with
          | cons h₂ hp =>
            cases h₂ with
            | uret _ =>
              cases hp
              have ht := trapped_resume callout
              obtain ⟨e', n'⟩ := ck'
              simp only [Silmaril.Wasm.Component.Reference.callMoves] at hp'
              cases path_trapped ht hp'
  have pre : ∀ k, ∀ x ∈ streamTake ω (N k), x.2 ≠ none := by
    intro k
    induction k with
    | zero => rw [hN0]; simp [streamTake]
    | succ k ih =>
      rw [(hk k).2.2.2]
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact ih x hx
      · exact seg k x hx
  obtain ⟨k, hk'⟩ := hunb (i + 1)
  exact pre k (ω i) (List.mem_ofFn.2 ⟨⟨i, by omega⟩, rfl⟩)

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj
