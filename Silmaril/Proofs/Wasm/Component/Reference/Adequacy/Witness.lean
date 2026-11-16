module

public import Silmaril.Proofs.Wasm.Component.Reference.Adequacy.WitnessRun
public import Silmaril.Proofs.Wasm.Component.Reference.Adequacy.Adequate

/-!
# The trap witnesses: same public observations, different IR strategies

At every deterministic profile `profile o` and component choice profile `prof`:

* `witness_equiv`: `RefPubEquiv (profile o) prof pokePeekS zeroS`. Both components have the
  same terminating public observations (`seqObs_char`): every resolved call is a call of `peek`
  returning `0`, a last call of `poke` traps and a last call of `peek` returns `0`. A call of
  `poke` never resolves (its lift traps), so a call of `peek` always runs at the instance's
  store, where its run is unique.
* `witness_play`: the IR denotation of `pokePeekS` plays `poke · trap · peek · 1` (the store
  persists after the trap of `poke`, whose core function has set the global), and that of
  `zeroS` does not (its `peek` returns `0` at every store).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.Adequacy

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Game (Reach ResultAt ScalarInstance)
open Silmaril.Wasm.Execution.Core (Store Steps invoke vals Result)
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "CVal" => Silmaril.Wasm.Execution.Core.Val
local notation "ROutcome" => Silmaril.Wasm.Component.Reference.Outcome

/-! ## Lifting at the witnesses' types -/

theorem liftArgs_variant_nil (ys : List Flat) : liftArgs [.variant []] ys = none := by
  unfold liftArgs ValTy.liftList
  cases ys with
  | nil => rfl
  | cons y r =>
    obtain ⟨t, b⟩ := y
    cases t with
    | int it =>
      cases it with
      | i32 => simp [ValTy.lift, Flat.take, ValTy.flatCases, ValTy.liftCase]
      | i64 => rfl
    | float ft => cases ft <;> rfl

theorem liftOutcome_poke (r : Option (List Flat)) :
    liftOutcome ⟨[], [.variant []]⟩ r = .traps := by
  cases r with
  | none => rfl
  | some ys => simp only [liftOutcome, liftArgs_variant_nil]

/-- The flat view of `i32 v` and its lift at `u32`. -/
theorem lift_u32 (v : BitVec 32) :
    ([Silmaril.Wasm.Execution.Core.Val.i32 v].mapM Silmaril.Wasm.SingleThreaded.toFlat? = some [⟨.int .i32, v⟩]) ∧
      liftArgs [.u32] [⟨.int .i32, v⟩] = some [.u32 v] :=
  ⟨rfl, rfl⟩

/-! ## Components like the witnesses -/

variable {P : Profile} {prof : ProfileKind}

/-- `X` has an export `poke` (index `jk`) of type `() -> variant {}` and an export `peek`
(index `jp`) of type `() -> u32` returning `0` at the instance's store, and no other export. -/
structure PPLike (P : Profile) (X : Simple) (I : ScalarInstance) (jk jp : Fin X.exports.length) :
    Prop where
  adequate : X.Adequate
  inst : X.mod.IsInst I
  cover : ∀ j, j = jk ∨ j = jp
  ne : jk ≠ jp
  tyk : X.exports[jk].ty = ⟨[], [.variant []]⟩
  typ : X.exports[jp].ty = ⟨[], [.u32]⟩
  peekRet : ∀ vs ws s', RetAt P X I X.exports[jp] vs I.store ws s' → ws = [.u32 0] ∧ s' = I.store
  peekRet' : RetAt P X I X.exports[jp] [] I.store [.u32 0] I.store
  pokeTrap : Silmaril.Wasm.Component.Reference.Outcome.traps ∈ specAt P X I X.exports[jk] [] I.store
  peekSpec : ∀ b, b ∈ specAt P X I X.exports[jp] [] I.store → b.Term →
    b = .returns (some [toRefVal (.u32 0)])

namespace PPLike

variable {X : Simple} {I : ScalarInstance} {jk jp : Fin X.exports.length}

theorem params (F : PPLike P X I jk jp) (j : Fin X.exports.length) : X.exports[j].ty.params = [] := by
  rcases F.cover j with rfl | rfl
  · rw [F.tyk]
  · rw [F.typ]

theorem args_nil (F : PPLike P X I jk jp) {j : Fin X.exports.length} {vs : List IVal}
    (h : ValTy.checkList X.exports[j].ty.params vs = true) : vs = [] := by
  rw [F.params j] at h
  cases vs with
  | nil => rfl
  | cons _ _ => simp [ValTy.checkList] at h

theorem pokeNoRet (F : PPLike P X I jk jp) {vs ws : List IVal} {s s' : Store Nat}
    (h : RetAt P X I X.exports[jk] vs s ws s') : False := by
  obtain ⟨-, -, ys, -, -, -, hws⟩ := h.run
  rw [F.tyk, liftArgs_variant_nil] at hws
  cases hws

theorem pokeSpec (F : PPLike P X I jk jp) {b : ROutcome} {s : Store Nat}
    (hb : b ∈ specAt P X I X.exports[jk] [] s) (hterm : b.Term) : b = .traps := by
  unfold specAt at hb
  rw [checkLower_of_check (by rw [F.tyk]; rfl)] at hb
  rcases hb with ⟨r, -, rfl⟩ | ⟨rfl, -⟩
  · rw [F.tyk]
    exact liftOutcome_poke r
  · exact hterm.elim

/-- **Chains of returned calls** are calls of `peek` returning `0` at the instance's store. -/
theorem chain (F : PPLike P X I jk jp) :
    ∀ (calls : List (Fin X.exports.length × List IVal)) (wss : List (List IVal)) (s : Store Nat),
      SeqSpec P X I I.store (specCalls X calls) wss s →
      (∀ q ∈ calls, q.1 = jp) ∧ wss = calls.map (fun _ => [.u32 0]) ∧ s = I.store
  | [], wss, s, h => by
    cases h
    exact ⟨(fun _ h => nomatch h), rfl, rfl⟩
  | (j, vs) :: calls, wss, s, h => by
    have h' : SeqSpec P X I I.store ((X.exports[j], vs) :: specCalls X calls) wss s := h
    cases h' with
    | cons hret hseq =>
      rcases F.cover j with hj | hj
      · subst j
        exact (F.pokeNoRet hret).elim
      · subst j
        obtain ⟨rfl, rfl⟩ := F.peekRet _ _ _ hret
        obtain ⟨hc, rfl, rfl⟩ := chain F calls _ s hseq
        refine ⟨fun q hq => ?_, rfl, rfl⟩
        rcases List.mem_cons.mp hq with rfl | hq
        · rfl
        · exact hc q hq

/-- Calls of `peek` are a chain of returned calls. -/
theorem chain' (F : PPLike P X I jk jp) :
    ∀ (calls : List (Fin X.exports.length × List IVal)), (∀ q ∈ calls, q.1 = jp ∧ q.2 = []) →
      SeqSpec P X I I.store (specCalls X calls) (calls.map fun _ => [.u32 0]) I.store
  | [], _ => .nil _
  | (j, vs) :: calls, h => by
    obtain ⟨hj, rfl⟩ := h _ List.mem_cons_self
    have hj' : j = jp := hj
    subst j
    exact .cons F.peekRet' (chain' F calls fun q hq => h q (List.mem_cons_of_mem _ hq))

/-- The observation of calls of `peek` and a last call `j`. -/
def obs {n : Nat} (k : Nat) (calls : List (Fin n × List IVal)) (j : Fin n) :
    List (List Silmaril.Wasm.Component.Value.Val) × ROutcome :=
  (calls.map fun _ => [toRefVal (.u32 0)],
    if j.val = k then .traps else .returns (some [toRefVal (.u32 0)]))

/-- **The terminating public observations** of a component like the witnesses. -/
theorem seqObs_char (F : PPLike P X I jk jp) (calls : List (Fin X.exports.length × List IVal))
    (j : Fin X.exports.length) (vs : List IVal) (ht : TypedCalls X calls)
    (hvs : ValTy.checkList X.exports[j].ty.params vs = true) :
    seqObs P prof X calls j vs = {p | (∀ q ∈ calls, q.1.val = jp.val) ∧ p = obs jk.val calls j} := by
  obtain rfl := F.args_nil hvs
  have hargs : ∀ q ∈ calls, q.2 = [] := fun q hq => F.args_nil (ht q hq)
  ext p
  constructor
  · rintro ⟨hp, hterm⟩
    obtain ⟨I', wss, s, hI', hseq, hp1, hb⟩ := seq_refToSpec P prof X F.adequate.good
      F.adequate.floatFree F.adequate.inst F.adequate.arity calls j [] ht hvs p hp
    obtain rfl := NumModule.IsInst.unique hI' F.inst
    obtain ⟨hc, rfl, rfl⟩ := chain F calls wss s hseq
    refine ⟨fun q hq => congrArg Fin.val (hc q hq), ?_⟩
    obtain ⟨p1, b⟩ := p
    simp only at hp1 hb hterm
    subst hp1
    simp only [obs, List.map_map, Prod.mk.injEq]
    refine ⟨by rfl, ?_⟩
    rcases F.cover j with hj | hj
    · subst j
      simp only [↓reduceIte]
      exact F.pokeSpec hb hterm
    · subst j
      have hne : jp.val ≠ jk.val := fun h => F.ne (Fin.ext h).symm
      simp only [hne, ↓reduceIte]
      exact F.peekSpec b hb hterm
  · rintro ⟨hc, rfl⟩
    have hseq := chain' F calls fun q hq => ⟨Fin.ext (hc q hq), hargs q hq⟩
    have hb : (obs jk calls j).2 ∈ specAt P X I X.exports[j] [] I.store ∧ (obs jk calls j).2.Term := by
      rcases F.cover j with hj | hj
      · subst j
        simp only [obs, ↓reduceIte]
        exact ⟨F.pokeTrap, trivial⟩
      · subst j
        have hne : jp.val ≠ jk.val := fun h => F.ne (Fin.ext h).symm
        simp only [obs, hne, ↓reduceIte]
        refine ⟨?_, trivial⟩
        have h := specAt_of_retAt F.peekRet'
        simpa using h
    have href := seq_specToRef P prof X F.adequate.good F.adequate.floatFree F.adequate.inst
      F.adequate.arity F.inst calls _ I.store j [] ht hvs hseq hb.1 hb.2
    refine ⟨?_, hb.2⟩
    simpa [obs, List.map_map] using href

end PPLike

/-! ## The two witnesses -/

variable {o : Silmaril.Wasm.SingleThreaded.GrowOracle}

local notation "Pd" => Silmaril.Wasm.SingleThreaded.profile o

theorem coreAt_reach {I : ScalarInstance} {k : Nat} {s : Store Nat} {r : Option (List Flat)}
    (hr : r ∈ coreAt Pd I k [] s) :
    ∃ s' t' res, Reach Pd (s, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (I.addrs.getD k 0) [])
      (s', t') ∧ ResultAt s' t' res ∧
      r = (match res with
        | .values vs => vs.mapM Silmaril.Wasm.SingleThreaded.toFlat?
        | _ => none) := by
  obtain ⟨c', res, steps, final, rfl⟩ := hr
  obtain ⟨s', t', run, final'⟩ := (Silmaril.Wasm.Game.ret_iff_core (s := s)
    (t := Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (I.addrs.getD k 0) [])).mpr
    ⟨c', steps, final⟩
  exact ⟨s', t', res, run, final', rfl⟩

theorem coreAt_of_reach {I : ScalarInstance} {k : Nat} {s s' : Store Nat} {v : BitVec 32}
    (h : Reach Pd (s, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (I.addrs.getD k 0) [])
      (s', .active {} (vals [Silmaril.Wasm.Execution.Core.Val.i32 v]))) :
    some [⟨.int .i32, v⟩] ∈ coreAt Pd I k [] s :=
  ⟨_, .values [Silmaril.Wasm.Execution.Core.Val.i32 v], Silmaril.Wasm.Game.Reach.steps h, rfl, rfl⟩

theorem pp_peekRet {vs ws : List IVal} {s' : Store Nat}
    (h : RetAt Pd pokePeekS ppInst pokePeekS.exports[(1 : Fin 2)] vs ppStore ws s') :
    ws = [.u32 0] ∧ s' = ppStore := by
  obtain ⟨g, hg, hv⟩ := ppStore_global
  have hvs : vs = [] := by
    have := h.typed
    cases vs with
    | nil => rfl
    | cons _ _ => simp [pokePeekS, ValTy.checkList] at this
  subst hvs
  obtain ⟨t', cvs, ys, run, final, hys, hws⟩ := h.run
  have mine := get_reach (P := Pd) (s := ppStore) rfl hg
  obtain ⟨rfl, rfl, hres⟩ := result_unique (x := (ppStore, _)) (r₁ := .values [g.value]) mine rfl
    run final
  simp only [Result.values.injEq] at hres
  subst hres
  rw [hv] at hys
  obtain ⟨hy, -⟩ := lift_u32 0
  rw [hy] at hys
  cases hys
  have hl : liftArgs [.u32] [⟨.int .i32, (0 : BitVec 32)⟩] = some [.u32 0] := rfl
  have hws' : liftArgs [.u32] [⟨.int .i32, (0 : BitVec 32)⟩] = some ws := hws
  rw [hl] at hws'
  cases hws'
  exact ⟨rfl, rfl⟩

theorem pp_peekSpec (b : ROutcome)
    (hb : b ∈ specAt Pd pokePeekS ppInst pokePeekS.exports[(1 : Fin 2)] [] ppStore)
    (hterm : b.Term) : b = .returns (some [toRefVal (.u32 0)]) := by
  obtain ⟨g, hg, hv⟩ := ppStore_global
  unfold specAt at hb
  rw [checkLower_of_check rfl] at hb
  rcases hb with ⟨r, hr, rfl⟩ | ⟨rfl, -⟩
  · obtain ⟨s', t', res, run, final, rfl⟩ := coreAt_reach hr
    have mine := get_reach (P := Pd) (s := ppStore) rfl hg
    obtain ⟨-, -, rfl⟩ := result_unique (x := (ppStore, _)) (r₁ := .values [g.value]) mine rfl
      run final
    rw [hv]
    rfl
  · exact hterm.elim

theorem pp_like : PPLike Pd pokePeekS ppInst ⟨0, by decide⟩ ⟨1, by decide⟩ where
  adequate := pokePeekS_adequate
  inst := pp_isInst
  cover j := by
    match j with
    | ⟨0, _⟩ => exact .inl rfl
    | ⟨1, _⟩ => exact .inr rfl
  ne := by decide
  tyk := rfl
  typ := rfl
  peekRet _ _ _ h := pp_peekRet h
  peekRet' := by
    obtain ⟨g, hg, hv⟩ := ppStore_global
    have mine := get_reach (P := Pd) (s := ppStore) rfl hg
    rw [hv] at mine
    exact ⟨rfl, .active {} (vals [Silmaril.Wasm.Execution.Core.Val.i32 0]),
      [Silmaril.Wasm.Execution.Core.Val.i32 0], [⟨.int .i32, 0⟩], mine, rfl, rfl, rfl⟩
  pokeTrap := by
    unfold specAt
    rw [checkLower_of_check rfl]
    exact .inl ⟨_, coreAt_of_reach (I := ppInst) (k := 0) set_reach, (liftOutcome_poke _).symm⟩
  peekSpec := pp_peekSpec

theorem z_peekRet {vs ws : List IVal} {s' : Store Nat}
    (h : RetAt Pd zeroS zInst zeroS.exports[(1 : Fin 2)] vs zStore ws s') :
    ws = [.u32 0] ∧ s' = zStore := by
  have hvs : vs = [] := by
    have := h.typed
    cases vs with
    | nil => rfl
    | cons _ _ => simp [zeroS, ValTy.checkList] at this
  subst hvs
  obtain ⟨t', cvs, ys, run, final, hys, hws⟩ := h.run
  have mine := zero_reach (P := Pd) (s := zStore) rfl
  obtain ⟨rfl, rfl, hres⟩ := result_unique (x := (zStore, _))
    (r₁ := .values [Silmaril.Wasm.Execution.Core.Val.i32 0]) mine rfl run final
  simp only [Result.values.injEq] at hres
  subst hres
  obtain ⟨hy, -⟩ := lift_u32 0
  rw [hy] at hys
  cases hys
  have hl : liftArgs [.u32] [⟨.int .i32, (0 : BitVec 32)⟩] = some [.u32 0] := rfl
  have hws' : liftArgs [.u32] [⟨.int .i32, (0 : BitVec 32)⟩] = some ws := hws
  rw [hl] at hws'
  cases hws'
  exact ⟨rfl, rfl⟩

/-- At every store with the instance's functions, `peek` of `zeroS` returns `0`. -/
theorem z_peekSpec_at {s : Store Nat} (hs : s.funcs = zStore.funcs) {r : Option (List Flat)}
    (hr : r ∈ coreAt Pd zInst 0 [] s) : r = some [⟨.int .i32, 0⟩] := by
  obtain ⟨s', t', res, run, final, rfl⟩ := coreAt_reach hr
  have mine := zero_reach (P := Pd) hs
  obtain ⟨-, -, rfl⟩ := result_unique (x := (s, _))
    (r₁ := .values [Silmaril.Wasm.Execution.Core.Val.i32 0]) mine rfl run final
  rfl

theorem z_like : PPLike Pd zeroS zInst ⟨0, by decide⟩ ⟨1, by decide⟩ where
  adequate := zeroS_adequate
  inst := z_isInst
  cover j := by
    match j with
    | ⟨0, _⟩ => exact .inl rfl
    | ⟨1, _⟩ => exact .inr rfl
  ne := by decide
  tyk := rfl
  typ := rfl
  peekRet _ _ _ h := z_peekRet h
  peekRet' := ⟨rfl, .active {} (vals [Silmaril.Wasm.Execution.Core.Val.i32 0]),
    [Silmaril.Wasm.Execution.Core.Val.i32 0], [⟨.int .i32, 0⟩], zero_reach (P := Pd) rfl, rfl, rfl,
    rfl⟩
  pokeTrap := by
    unfold specAt
    rw [checkLower_of_check rfl]
    exact .inl ⟨_, coreAt_of_reach (I := zInst) (k := 0) (zero_reach rfl), (liftOutcome_poke _).symm⟩
  peekSpec b hb hterm := by
    unfold specAt at hb
    rw [checkLower_of_check rfl] at hb
    rcases hb with ⟨r, hr, rfl⟩ | ⟨rfl, -⟩
    · rw [z_peekSpec_at rfl hr]
      rfl
    · exact hterm.elim

/-- **The witnesses are publicly equivalent on the reference machine.** -/
theorem witness_equiv (o : Silmaril.Wasm.SingleThreaded.GrowOracle) (prof : ProfileKind) :
    RefPubEquiv (Silmaril.Wasm.SingleThreaded.profile o) prof pokePeekS zeroS where
  len := rfl
  ty j := by
    match j with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  obs calls j vs ht hvs := by
    have hP := pp_like (o := o)
    have hZ := z_like (o := o)
    have ht' : TypedCalls zeroS (castCalls rfl calls) := by
      intro q hq
      obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.mp hq
      have h := ht q₀ hq₀
      obtain ⟨⟨_ | _ | n, hn⟩, a⟩ := q₀
      · exact h
      · exact h
      · exfalso
        have h2 : n + 1 + 1 < 2 := hn
        omega
    have hvs' : ValTy.checkList zeroS.exports[Fin.cast (rfl : pokePeekS.exports.length =
        zeroS.exports.length) j].ty.params vs = true := by
      obtain ⟨_ | _ | n, hn⟩ := j
      · exact hvs
      · exact hvs
      · exfalso
        have h2 : n + 1 + 1 < 2 := hn
        omega
    refine (hP.seqObs_char (prof := prof) calls j vs ht hvs).trans
      (Eq.trans ?_ (hZ.seqObs_char (prof := prof) _ _ vs ht' hvs').symm)
    have hobs : PPLike.obs 0 (castCalls (c := pokePeekS) (c' := zeroS) rfl calls)
        (Fin.cast (rfl : pokePeekS.exports.length = zeroS.exports.length) j) =
        PPLike.obs 0 calls j := by
      simp only [PPLike.obs, castCalls, List.map_map]
      rfl
    have hall : (∀ q ∈ castCalls (c := pokePeekS) (c' := zeroS) rfl calls, q.1.val = 1) ↔
        ∀ q ∈ calls, q.1.val = 1 := by
      constructor
      · intro h q hq
        exact h _ (List.mem_map_of_mem hq)
      · intro h q hq
        obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.mp hq
        exact h q₀ hq₀
    ext p
    exact and_congr hall.symm (Iff.of_eq (congrArg (p = ·) hobs.symm))

/-! ## The play after a trap -/

/-- The rounds `poke · trap · peek · 1`. -/
def trapRounds (c : Simple) (h₀ : 0 < c.toComp.exports.length) (h₁ : 1 < c.toComp.exports.length) :
    List (Round (sigN c.toComp.exports.length)) :=
  [⟨(⟨0, h₀⟩, .vals []), none⟩, ⟨(⟨1, h₁⟩, .vals []), some (.vals [.u32 1])⟩]

theorem answer_i32 (v : BitVec 32) :
    ∃ w, Silmaril.Wasm.Game.Answer.ofResult? fnI32 (.values [Silmaril.Wasm.Execution.Core.Val.i32 v]) = some w ∧
      answerPayload w = some (.flat [⟨.int .i32, v⟩]) := by
  have h : List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal fnI32.results [Silmaril.Wasm.Execution.Core.Val.i32 v] :=
    .cons ⟨v, rfl⟩ .nil
  refine ⟨.values ⟨[Silmaril.Wasm.Execution.Core.Val.i32 v], h⟩, ?_, rfl⟩
  simp [Silmaril.Wasm.Game.Answer.ofResult?, h]

/-- **`pokePeekS` plays `poke · trap · peek · 1`.** -/
theorem pp_trapRounds :
    twos (E := sigN 0) (trapRounds pokePeekS (by decide) (by decide)) ∈
      pokePeekS.toComp.den (modSem Pd) := by
  have hk₀ : 0 < pokePeekS.mod.exports.length := by decide
  have hk₁ : 1 < pokePeekS.mod.exports.length := by decide
  have hx : ([] : List Flat).map (·.type) = pokePeekS.mod.exports[0].2.params := rfl
  have hx₁ : ([] : List Flat).map (·.type) = pokePeekS.mod.exports[1].2.params := rfl
  obtain ⟨w₀, hw₀, hp₀⟩ := answer_i32 0
  obtain ⟨w₁, hw₁, hp₁⟩ := answer_i32 1
  obtain ⟨g, hg, hv⟩ := ppStore₁_global
  have run₁ := get_reach (P := Pd) (s := ppStore₁) rfl hg
  rw [hv] at run₁
  have hli : twos (E := ppInst.E) [⟨opAt pp_isInst hk₀ hx, w₀⟩, ⟨opAt pp_isInst hk₁ hx₁, w₁⟩] ∈
      ppInst.strategy Pd ppStore := by
    refine Silmaril.Wasm.Game.ScalarInstance.mem_strategy_iff.mpr ⟨.idle ppStore₁, ?_⟩
    exact .cons (.call _ _)
      (.cons (.oret (r := .values [Silmaril.Wasm.Execution.Core.Val.i32 0]) set_reach rfl hw₀)
      (.cons (.call _ _)
        (.cons (.oret (r := .values [Silmaril.Wasm.Execution.Core.Val.i32 1]) run₁ rfl hw₁)
          (.nil _))))
  have H : HRounds (exportH (instNum pp_isInst))
      [⟨(⟨0, hk₀⟩, .flat []), answerPayload w₀⟩, ⟨(⟨1, hk₁⟩, .flat []), answerPayload w₁⟩]
      [⟨opAt pp_isInst hk₀ hx, w₀⟩, ⟨opAt pp_isInst hk₁ hx₁, w₁⟩] :=
    .call (exportH_round pp_isInst hk₀ hx) rfl (.call (exportH_round pp_isInst hk₁ hx₁) rfl .nil)
  have X₁ := exportsH_call pokePeekS (j := 0) (by decide) [] hk₀ rfl (answerPayload w₀) none (by
    rw [hp₀]
    simp only [Option.bind_some, Adapter.up]
    rfl)
  have X₂ := exportsH_call pokePeekS (j := 1) (by decide) [] hk₁ rfl (answerPayload w₁)
    (some (.vals [.u32 1])) (by rw [hp₁]; rfl)
  have hden := seq_den (P := Pd) (calls := []) (wss := []) (li₀ := []) (lc₀ := [])
    (U := trapRounds pokePeekS (by decide) (by decide)) pp_isInst (.nil _) hli .nil H .nil
    (X₁.append X₂)
  exact hden

/-- **`zeroS` does not play `poke · trap · peek · 1`**, at any deterministic profile. -/
theorem z_not_trapRounds {L : List (Round (sigN zeroS.toComp.exports.length))}
    (hL : twos (E := sigN 0) L ∈ zeroS.toComp.den (modSem Pd))
    (he : L.map Round.forget =
      [⟨(0, .vals []), none⟩, ⟨(1, .vals []), some (.vals [.u32 1])⟩]) : False := by
  have hS := specRounds_of_den zeroS_adequate.good z_isInst hL
  rw [he] at hS
  cases hS with
  | @cons _ s₁ _ _ hr₁ hS' =>
    have hf₁ : s₁.funcs = zStore.funcs := by
      rcases hr₁ with ⟨_, rfl, _⟩ | ⟨_, _, _, _, _, _, _, _, _, hf⟩
      · rfl
      · exact hf
    cases hS' with
    | cons hr₂ _ =>
      rcases hr₂ with ⟨h, -, -⟩ | ⟨hj, vs, xs, r, hp, hl, hr, hA, -⟩
      · cases h
      · cases hp
        have hxs : xs = [] := by
          simp [zeroS, checkLower, lowerArgs, ValTy.checkList, ValTy.lowerList] at hl
          exact hl
        subst hxs
        have hr' : r ∈ coreAt Pd zInst 0 [] s₁ := hr
        rw [z_peekSpec_at hf₁ hr'] at hA
        have h₂ : some (Payload.vals [.u32 1]) = some (Payload.vals [.u32 0]) := hA.trans rfl
        injection h₂ with h₃
        injection h₃ with h₄
        injection h₄ with h₅
        injection h₅ with h₆
        exact absurd h₆ (by decide)

/-- **The IR denotations of the witnesses differ**, at every deterministic profile: the play
`poke · trap · peek · 1` of `pokePeekS`, read at `sigU`, is not a play of `zeroS`. -/
theorem witness_play (o : Silmaril.Wasm.SingleThreaded.GrowOracle) :
    ∃ p, p ∈ pubPlays (pokePeekS.toComp.den (modSem (Silmaril.Wasm.SingleThreaded.profile o))) ∧
      p ∉ pubPlays (zeroS.toComp.den (modSem (Silmaril.Wasm.SingleThreaded.profile o))) := by
  refine ⟨_, ⟨_, pp_trapRounds, rfl⟩, ?_⟩
  rintro ⟨p', hp', he⟩
  rw [map_forgetMove_twos] at he
  rcases den_shape _ zeroS hp' with ⟨L, rfl⟩ | ⟨q, L, rfl⟩
  · rw [map_forgetMove_twos] at he
    exact z_not_trapRounds hp' (twos_inj he)
  · rw [List.map_append, map_forgetMove_twos] at he
    exact twos_ne_twos_ask _ _ _ he.symm

/-- **The IR strategies of the witnesses differ.** -/
theorem witness_ne (o : Silmaril.Wasm.SingleThreaded.GrowOracle) :
    pokePeekS.toComp.den (modSem (Silmaril.Wasm.SingleThreaded.profile o)) ≠
      zeroS.toComp.den (modSem (Silmaril.Wasm.SingleThreaded.profile o)) := by
  intro h
  obtain ⟨p, hp, hp'⟩ := witness_play o
  exact hp' (h ▸ hp)

/-- **`RefPubEquiv` does not determine the IR plays.** -/
theorem refPubEquiv_not_den_eq (o : Silmaril.Wasm.SingleThreaded.GrowOracle)
    (prof : ProfileKind) :
    ¬ ∀ c c' : Simple, c.Adequate → c'.Adequate →
      RefPubEquiv (Silmaril.Wasm.SingleThreaded.profile o) prof c c' →
      pubPlays (c.toComp.den (modSem (Silmaril.Wasm.SingleThreaded.profile o))) =
        pubPlays (c'.toComp.den (modSem (Silmaril.Wasm.SingleThreaded.profile o))) := by
  intro h
  obtain ⟨p, hp, hp'⟩ := witness_play o
  exact hp' (h _ _ pokePeekS_adequate zeroS_adequate (witness_equiv o prof) ▸ hp)

end Silmaril.Proofs.Wasm.Component.Reference.Adequacy
