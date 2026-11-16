module

public import Silmaril.Wasi.Component.Consequence.Signed.Spec.Defs
public import Silmaril.Wasi.Component.Consequence.Checkers.Thms

/-!
# Specification components for the signed protocols: proofs

* The batch emitter: the events of its generating plays (`evs_emitPlay`); a trace ending in a
  `done` request is a whole generating play, because `done` occurs only at the end (`done ∉`
  the earlier events), and the last move of a trace is in a generating play when it is a
  Proponent move (`Strategy.generatePlays`).
* The identity checker: its decoder inverts its encoding (`signedPairDec_iff`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasi.Component.Consequence.SignedSpec

open Silmaril.Games Silmaril.Wasi Silmaril.Wasi.Accept Silmaril.Wasi.Consequence
open Silmaril.Consequence (Signed)
open Silmaril.Wasm.Component (Val)

variable {V : Type} {enc : V → Val} {decV : List Val → Option V}

/-! ## The batch emitter -/

/-- The events of emitting one literal. -/
def litEvs (enc : V → Val) : Signed V → List WEv
  | .pos a => [.req posFn [enc a], .imp posFn [enc a] (some [])]
  | .neg a => [.req negFn [enc a], .imp negFn [enc a] (some [])]

theorem wtrace_litMoves (x : Signed V) : wtrace (litMoves enc x) = litEvs enc x := by
  cases x <;> rfl

theorem evs_emitPlay (l : List (Signed V)) :
    wtrace (emitPlay enc l) =
      (WEv.call runFn [] :: l.flatMap (litEvs enc)) ++ [WEv.req doneFn []] := by
  simp only [emitPlay, wtrace, List.map_cons, List.map_append, List.map_flatMap]
  congr 2
  exact List.flatMap_congr fun x _ => wtrace_litMoves x

theorem legal_emitPlay (l : List (Signed V)) : Legal (emitPlay enc l) := by
  refine ⟨Pos.wait (E := nsig batchImports) (F := nsig {runFn}) (⟨runFn, rfl⟩, [])
    (⟨doneFn, by simp⟩, []), .cons (.ask _) ?_⟩
  suffices h : ∀ l : List (Signed V),
      Path (Pos.run (E := nsig batchImports) (F := nsig {runFn}) (⟨runFn, rfl⟩, []))
      (l.flatMap (litMoves enc) ++ [.inl (.ask (⟨doneFn, by simp⟩, []))])
      (Pos.wait (⟨runFn, rfl⟩, []) (⟨doneFn, by simp⟩, [])) from h l
  intro l
  induction l with
  | nil => exact .cons (.call _ _) (.nil _)
  | cons x l ih =>
    rw [List.flatMap_cons, List.append_assoc]
    refine Path.append_iff.2 ⟨_, ?_, ih⟩
    cases x <;> exact .cons (.call _ _) (.cons (.reply _ _ _) (.nil _))

theorem done_not_mem_litEvs (l : List (Signed V)) :
    WEv.req doneFn [] ∉ l.flatMap (litEvs enc) := by
  simp only [List.mem_flatMap, not_exists, not_and]
  intro x _
  cases x <;> simp [litEvs, posFn, negFn, doneFn]

/-- The steps of emitting literals, observed at the call boundary. -/
theorem steps_litEvs (hdec : ∀ args a, decV args = some a ↔ args = [enc a]) (td : TrapDone)
    (l : List (Signed V)) :
    (l.flatMap (litEvs enc)).filterMap (batchStep .call specBatchFns decV td) = l.map .add := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.flatMap_cons, List.filterMap_append, ih, List.map_cons]
    cases x <;>
      simp [litEvs, batchStep, BatchFns.closes, BatchFns.literal, specBatchFns, posFn, negFn,
        doneFn, (hdec _ _).2 rfl]

theorem foldl_add (xs ys : List (Signed V)) :
    (xs.map Step.add).foldl Policy.list.apply ys = ys ++ xs := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [ih]
    simp [Policy.apply, Policy.list]

theorem state_emit (hdec : ∀ args a, decV args = some a ↔ args = [enc a]) (td : TrapDone)
    (l : List (Signed V)) :
    epochState Policy.list ((WEv.call runFn [] :: l.flatMap (litEvs enc)).filterMap
      (batchStep .call specBatchFns decV td)) = l := by
  rw [List.filterMap_cons]
  simp only [batchStep]
  rw [steps_litEvs hdec td l, epochState, foldl_add]
  rfl

/-- **The batches of the emitter, at the call boundary, are exactly `L`.** -/
theorem batches_batchEmitter (hdec : ∀ args a, decV args = some a ↔ args = [enc a])
    (td : TrapDone) (L : Set (List (Signed V))) (l : List (Signed V)) :
    batches (Traces (batchEmitter enc L)) (importBatch .call specBatchFns decV td) l ↔ l ∈ L := by
  constructor
  · rintro ⟨s, e, ⟨p, hp, hw⟩, hr⟩
    simp only [importBatch, stateful, Option.map_eq_some_iff, Prod.mk.injEq] at hr
    obtain ⟨⟨u, a⟩, hcl, hst, -, -⟩ := hr
    -- the claim is a `done` request
    have he : e = .req doneFn [] := by
      cases e with
      | req g args =>
        cases args with
        | nil =>
          simp only [batchClaim, true_and] at hcl
          split_ifs at hcl with hg
          · rw [hg]; rfl
        | cons _ _ => simp [batchClaim] at hcl
      | imp g args res => cases args <;> simp [batchClaim] at hcl
      | _ => simp [batchClaim] at hcl
    subst he
    obtain ⟨-, u', hu, hpu⟩ := hp
    have hpre : p <+: u' := by
      rcases hpu with hpu | ⟨p₀, o, rfl, -, hO⟩
      · exact hpu
      · exfalso
        have : wev o = WEv.req doneFn [] := by
          have := congrArg List.getLast? hw
          simpa [wtrace] using this
        rcases o with (_ | _) | (_ | _) <;> simp_all [wev, Move.IsO]
    rcases hu with rfl | ⟨⟨l', hl', rfl⟩, -⟩
    · obtain rfl := List.prefix_nil.1 hpre
      simp [wtrace] at hw
    have hpw : s ++ [WEv.req doneFn []] <+:
        (WEv.call runFn [] :: l'.flatMap (litEvs enc)) ++ [WEv.req doneFn []] := by
      rw [← hw, ← evs_emitPlay]
      exact hpre.map wev
    rcases List.prefix_concat_iff.1 hpw with h | h
    · have hs := List.append_inj_left' h rfl
      subst hs
      rw [state_emit hdec td l'] at hst
      exact hst ▸ hl'
    · exfalso
      have hm : WEv.req doneFn [] ∈ WEv.call runFn [] :: l'.flatMap (litEvs enc) :=
        h.subset (List.mem_append_right _ (List.mem_singleton_self _))
      rcases List.mem_cons.1 hm with h' | h'
      · cases h'
      · exact done_not_mem_litEvs l' h'
  · intro hl
    refine ⟨WEv.call runFn [] :: l.flatMap (litEvs enc), .req doneFn [],
      ⟨_, Strategy.subset_generate ⟨l, hl, rfl⟩ (legal_emitPlay l), evs_emitPlay l⟩, ?_⟩
    simp only [importBatch, stateful, state_emit hdec td l]
    simp [batchClaim, specBatchFns]

/-! ## The identity checker -/

theorem mapM_eq_some_iff_of_inverse {α : Type} {d : Val → Option α} {e : α → Val}
    (h : ∀ v a, d v = some a ↔ v = e a) (vs : List Val) (xs : List α) :
    vs.mapM d = some xs ↔ vs = xs.map e := by
  induction vs generalizing xs with
  | nil => cases xs <;> simp
  | cons v vs ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq]
    constructor
    · rintro ⟨y, hy, ys, hys, rfl⟩
      simp [(h _ _).1 hy, (ih ys).1 hys]
    · intro hv
      cases xs with
      | nil => cases hv
      | cons y ys =>
        simp only [List.map_cons, List.cons.injEq] at hv
        exact ⟨y, (h _ _).2 hv.1, ys, (ih ys).2 hv.2, rfl⟩

theorem signedU32?_iff (v : Val) (a : Signed (BitVec 32)) :
    signedU32? v = some a ↔ v = signedU32 a := by
  constructor
  · intro h
    unfold signedU32? at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl
  · rintro rfl; cases a <;> rfl

theorem signedList?_iff (v : Val) (xs : List (Signed (BitVec 32))) :
    signedList? v = some xs ↔ v = .record (xs.map signedU32) := by
  have hr : ∀ {v : Val} {vs : List Val}, ofRecord? v = some vs ↔ v = .record vs := by
    intro v vs; cases v <;> simp [ofRecord?]
  simp only [signedList?, Option.bind_eq_some_iff, hr, mapM_eq_some_iff_of_inverse signedU32?_iff]
  constructor
  · rintro ⟨vs, rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨_, rfl, rfl⟩

theorem signedPairDec_iff (args : List Val)
    (q : List (Signed (BitVec 32)) × List (Signed (BitVec 32))) :
    args2 signedList? signedList? args = some q ↔ args = signedPairEnc q := by
  obtain ⟨xs, ys⟩ := q
  rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;>
    simp [args2, signedPairEnc, Option.bind_eq_some_iff, signedList?_iff]

end Silmaril.Proofs.Wasi.Component.Consequence.SignedSpec
