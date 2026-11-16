module

public import Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy.IRSess
public import Silmaril.Proofs.Wasm.Component.Reference.Adequacy.Adequate

/-!
# Resumable-session adequacy of the component IR

* `sess_complete`, `sess_sound`: the IR play of a typed session (`sessMoves`) is a play of
  `c.toComp.den (modSem P)` exactly when its outcomes are a reference session behaviour;
* `sessAdequacy`: for adequate simple components, `RefSessEquiv P prof c c'` holds exactly when
  the export types and the IR plays (at `sigU`) are the same;
* `refPubEquiv_of_sess`: hence `RefSessEquiv` implies #669's `RefPubEquiv`.

The plays of the IR may contain ill-typed questions, answered by a trap at once with the
store unchanged; a reference session only makes typed calls. `sessCalls` and `sessOuts` pick
the typed calls of a play and their answers (`typedQ`); the ill-typed rounds depend on the
export types only, so they move between components with the same types (`Shaped`,
`shaped_cast`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core (Store)

local notation "IVal" => Silmaril.Wasm.Component.Val

variable {P : Profile} {prof : ProfileKind}

/-! ## Typed calls of rounds -/

/-- The typed export call of a question of `c`, if it is one. -/
def typedQ (c : Simple) : Nat × Payload → Option (Fin c.exports.length × List IVal)
  | (j, .vals vs) =>
    if h : j < c.exports.length then
      if ValTy.checkList c.exports[j].ty.params vs then some (⟨j, h⟩, vs) else none
    else none
  | (_, .flat _) => none

/-- The session outcome of an IR answer. -/
def ansOut : Option Payload → Option (List IVal)
  | some (.vals ws) => some ws
  | _ => none

/-- The typed calls of rounds. -/
def sessCalls (c : Simple) : List (Round sigU) → List (Fin c.exports.length × List IVal)
  | [] => []
  | x :: L =>
    match typedQ c x.1 with
    | some q => q :: sessCalls c L
    | none => sessCalls c L

/-- The outcomes of the typed calls of rounds. -/
def sessOuts (c : Simple) : List (Round sigU) → List (Option (List IVal))
  | [] => []
  | x :: L =>
    match typedQ c x.1 with
    | some _ => ansOut x.2 :: sessOuts c L
    | none => sessOuts c L

theorem sessCalls_none {c : Simple} {x : Round sigU} {L : List (Round sigU)}
    (h : typedQ c x.1 = none) : sessCalls c (x :: L) = sessCalls c L := by
  simp [sessCalls, h]

theorem sessCalls_some {c : Simple} {x : Round sigU} {L : List (Round sigU)}
    {q : Fin c.exports.length × List IVal} (h : typedQ c x.1 = some q) :
    sessCalls c (x :: L) = q :: sessCalls c L := by
  simp [sessCalls, h]

theorem sessOuts_none {c : Simple} {x : Round sigU} {L : List (Round sigU)}
    (h : typedQ c x.1 = none) : sessOuts c (x :: L) = sessOuts c L := by
  simp [sessOuts, h]

theorem sessOuts_some {c : Simple} {x : Round sigU} {L : List (Round sigU)}
    {q : Fin c.exports.length × List IVal} (h : typedQ c x.1 = some q) :
    sessOuts c (x :: L) = ansOut x.2 :: sessOuts c L := by
  simp [sessOuts, h]

theorem typedQ_typed {c : Simple} {j : Nat} (hj : j < c.exports.length) {vs : List IVal}
    (h : ValTy.checkList c.exports[j].ty.params vs = true) :
    typedQ c (j, .vals vs) = some (⟨j, hj⟩, vs) := by
  simp [typedQ, hj, h]

theorem typedQ_bad {c : Simple} {j : Nat} {p : Payload}
    (hn : ∀ (hj : j < c.exports.length) (vs : List IVal), p = .vals vs →
      ValTy.checkList c.exports[j].ty.params vs = false) : typedQ c (j, p) = none := by
  cases p with
  | flat _ => rfl
  | vals vs =>
    by_cases hj : j < c.exports.length
    · simp [typedQ, hj, hn hj vs rfl]
    · simp [typedQ, hj]

theorem typedQ_some {c : Simple} {j : Nat} {p : Payload} {q : Fin c.exports.length × List IVal}
    (h : typedQ c (j, p) = some q) :
    ∃ (hj : j < c.exports.length) (vs : List IVal), p = .vals vs ∧
      ValTy.checkList c.exports[j].ty.params vs = true ∧ q = (⟨j, hj⟩, vs) := by
  cases p with
  | flat _ => cases h
  | vals vs =>
    by_cases hj : j < c.exports.length
    · cases hc : ValTy.checkList c.exports[j].ty.params vs with
      | false => simp [typedQ, hj, hc] at h
      | true =>
        rw [typedQ_typed hj hc] at h
        exact ⟨hj, vs, rfl, hc, (Option.some.inj h).symm⟩
    · simp [typedQ, hj] at h

/-! ## Sessions of rounds and of the specification -/

theorem sessSpec_cons_inv {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance} {s s' : Store Nat}
    {x : SimpleExport} {vs : List IVal} {cs : List (SimpleExport × List IVal)}
    {o : Option (List IVal)} {outs : List (Option (List IVal))}
    (h : SessSpec P c I s ((x, vs) :: cs) (o :: outs) s') :
    (∃ ws s₁, o = some ws ∧ RetAt P c I x vs s ws s₁ ∧ SessSpec P c I s₁ cs outs s') ∨
      (∃ s₁, o = none ∧ TrapAt P c I x vs s s₁ ∧ SessSpec P c I s₁ cs outs s') := by
  cases h with
  | ret hr h' => exact .inl ⟨_, _, rfl, hr, h'⟩
  | trap hr h' => exact .inr ⟨_, rfl, hr, h'⟩

theorem sessSpec_length {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance} :
    ∀ {s s' : Store Nat} {cs : List (SimpleExport × List IVal)}
      {outs : List (Option (List IVal))}, SessSpec P c I s cs outs s' → cs.length = outs.length
  | _, _, _, _, .nil _ => rfl
  | _, _, _, _, .ret _ h => by simp [sessSpec_length h]
  | _, _, _, _, .trap _ h => by simp [sessSpec_length h]

/-- **A session of rounds is a session of the specification**, on its typed calls. -/
theorem spec_of_sessRounds {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance} :
    ∀ {s s' : Store Nat} {Lu : List (Round sigU)}, SessRounds P c I s Lu s' →
      SessSpec P c I s (specCalls c (sessCalls c Lu)) (sessOuts c Lu) s' ∧
        TypedCalls c (sessCalls c Lu)
  | _, _, _, .nil s => ⟨.nil s, fun _ h => nomatch h⟩
  | _, _, _, .bad (j := j) (p := p) _ hn h => by
    rw [sessCalls_none (typedQ_bad hn), sessOuts_none (typedQ_bad hn)]
    exact spec_of_sessRounds h
  | _, _, _, .ret (j := j) (vs := vs) hj hret h => by
    rw [sessCalls_some (typedQ_typed hj hret.typed), sessOuts_some (typedQ_typed hj hret.typed)]
    obtain ⟨hs, ht⟩ := spec_of_sessRounds h
    refine ⟨.ret hret hs, fun q hq => ?_⟩
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hret.typed
    · exact ht q hq
  | _, _, _, .trap (j := j) (vs := vs) hj htrap h => by
    rw [sessCalls_some (typedQ_typed hj htrap.typed),
      sessOuts_some (typedQ_typed hj htrap.typed)]
    obtain ⟨hs, ht⟩ := spec_of_sessRounds h
    refine ⟨.trap htrap hs, fun q hq => ?_⟩
    rcases List.mem_cons.mp hq with rfl | hq
    · exact htrap.typed
    · exact ht q hq

/-- Rounds that can be a session of `c`: small indices, ill-typed questions answered by a
trap, typed calls answered by results or a trap. -/
def Shaped (c : Simple) (Lu : List (Round sigU)) : Prop :=
  ∀ x ∈ Lu, x.1.1 < c.exports.length ∧ (typedQ c x.1 = none → x.2 = none) ∧
    (∀ q, typedQ c x.1 = some q → x.2 = none ∨ ∃ ws, x.2 = some (.vals ws))

theorem sessRounds_shaped {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance} :
    ∀ {s s' : Store Nat} {Lu : List (Round sigU)}, SessRounds P c I s Lu s' → Shaped c Lu
  | _, _, _, .nil _, _, hx => nomatch hx
  | _, _, _, .bad hj _ h, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨hj, fun _ => rfl, fun _ _ => .inl rfl⟩
    · exact sessRounds_shaped h x hx
  | _, _, _, .ret hj hret h, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · refine ⟨hj, fun hn => ?_, fun _ _ => .inr ⟨_, rfl⟩⟩
      rw [typedQ_typed hj hret.typed] at hn
      cases hn
    · exact sessRounds_shaped h x hx
  | _, _, _, .trap hj _ h, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨hj, fun _ => rfl, fun _ _ => .inl rfl⟩
    · exact sessRounds_shaped h x hx

/-- **A session of the specification on the typed calls of shaped rounds is a session of the
rounds.** -/
theorem sessRounds_of_spec {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance} :
    ∀ {Lu : List (Round sigU)} {s s' : Store Nat}, Shaped c Lu →
      SessSpec P c I s (specCalls c (sessCalls c Lu)) (sessOuts c Lu) s' →
      SessRounds P c I s Lu s'
  | [], s, s', _, h => by
    cases h
    exact .nil s
  | ⟨(j, p), A⟩ :: Lu, s, s', hsh, h => by
    have hsh' : Shaped c Lu := fun x hx => hsh x (List.mem_cons_of_mem _ hx)
    obtain ⟨hj₀, hnone, hsome⟩ := hsh _ List.mem_cons_self
    cases hq : typedQ c (j, p) with
    | none =>
      rw [sessCalls_none hq, sessOuts_none hq] at h
      have hA : A = none := hnone hq
      subst hA
      refine .bad hj₀ (fun hj vs hp => ?_) (sessRounds_of_spec hsh' h)
      cases hc : ValTy.checkList c.exports[j].ty.params vs with
      | false => rfl
      | true => rw [hp, typedQ_typed hj hc] at hq; cases hq
    | some q =>
      obtain ⟨hj, vs, rfl, hck, rfl⟩ := typedQ_some hq
      rw [sessCalls_some hq, sessOuts_some hq] at h
      rcases sessSpec_cons_inv h with ⟨ws, s₁, ho, hret, h'⟩ | ⟨s₁, ho, htrap, h'⟩
      · rcases hsome _ hq with hA | ⟨ws', hA⟩
        · subst hA
          cases ho
        · subst hA
          cases ho
          exact .ret hj hret (sessRounds_of_spec hsh' h')
      · rcases hsome _ hq with hA | ⟨ws', hA⟩
        · subst hA
          exact .trap hj htrap (sessRounds_of_spec hsh' h')
        · subst hA
          cases ho

/-! ## Two components with the same export types -/

theorem typedQ_cast {c c' : Simple} {len : c.exports.length = c'.exports.length}
    (hty : SameTy c c' len) (q : Nat × Payload) :
    typedQ c' q = (typedQ c q).map fun r => (Fin.cast len r.1, r.2) := by
  obtain ⟨j, p⟩ := q
  cases p with
  | flat _ => rfl
  | vals vs =>
    by_cases hj : j < c.exports.length
    · have hj' : j < c'.exports.length := len ▸ hj
      have e : c'.exports[j].ty = c.exports[j].ty := hty ⟨j, hj⟩
      cases hc : ValTy.checkList c.exports[j].ty.params vs with
      | false =>
        have hc' : ValTy.checkList c'.exports[j].ty.params vs = false := by rw [e]; exact hc
        simp [typedQ, hj, hj', hc, hc']
      | true =>
        have hc' : ValTy.checkList c'.exports[j].ty.params vs = true := by rw [e]; exact hc
        rw [typedQ_typed hj hc, typedQ_typed hj' hc']
        rfl
    · have hj' : ¬ j < c'.exports.length := len ▸ hj
      simp [typedQ, hj, hj']

theorem sessCalls_cast {c c' : Simple} {len : c.exports.length = c'.exports.length}
    (hty : SameTy c c' len) :
    ∀ Lu : List (Round sigU), sessCalls c' Lu = castCalls len (sessCalls c Lu)
  | [] => rfl
  | x :: Lu => by
    cases hq : typedQ c x.1 with
    | none =>
      have hq' : typedQ c' x.1 = none := by rw [typedQ_cast hty, hq]; rfl
      rw [sessCalls_none hq, sessCalls_none hq', sessCalls_cast hty Lu]
    | some q =>
      have hq' : typedQ c' x.1 = some (Fin.cast len q.1, q.2) := by rw [typedQ_cast hty, hq]; rfl
      rw [sessCalls_some hq, sessCalls_some hq', sessCalls_cast hty Lu]
      rfl

theorem sessOuts_cast {c c' : Simple} {len : c.exports.length = c'.exports.length}
    (hty : SameTy c c' len) : ∀ Lu : List (Round sigU), sessOuts c' Lu = sessOuts c Lu
  | [] => rfl
  | x :: Lu => by
    cases hq : typedQ c x.1 with
    | none =>
      have hq' : typedQ c' x.1 = none := by rw [typedQ_cast hty, hq]; rfl
      rw [sessOuts_none hq, sessOuts_none hq', sessOuts_cast hty Lu]
    | some q =>
      have hq' : typedQ c' x.1 = some (Fin.cast len q.1, q.2) := by rw [typedQ_cast hty, hq]; rfl
      rw [sessOuts_some hq, sessOuts_some hq', sessOuts_cast hty Lu]

theorem shaped_cast {c c' : Simple} {len : c.exports.length = c'.exports.length}
    (hty : SameTy c c' len) {Lu : List (Round sigU)} (h : Shaped c Lu) : Shaped c' Lu := by
  intro x hx
  obtain ⟨hlt, hn, hs⟩ := h x hx
  refine ⟨len ▸ hlt, fun hq => hn ?_, fun q hq => ?_⟩
  · rw [typedQ_cast hty] at hq
    cases hq' : typedQ c x.1 with
    | none => rfl
    | some _ => rw [hq'] at hq; cases hq
  · rw [typedQ_cast hty] at hq
    cases hq' : typedQ c x.1 with
    | none => rw [hq'] at hq; cases hq
    | some r => exact hs r hq'

/-! ## Typed sessions -/

/-- The rounds of a typed session, at `sigU`. -/
def sessLu {n : Nat} : List (Fin n × List IVal) → List (Option (List IVal)) → List (Round sigU)
  | (j, vs) :: cs, o :: os => ⟨(j.val, .vals vs), o.map .vals⟩ :: sessLu cs os
  | _, _ => []

/-- The rounds of a typed session, at the export interface. -/
def sessRoundsN (c : Simple) :
    List (Fin c.exports.length × List IVal) → List (Option (List IVal)) →
    List (Round (sigN c.toComp.exports.length))
  | (j, vs) :: cs, o :: os =>
    ⟨(⟨j, by simp [Simple.toComp]⟩, .vals vs), o.map .vals⟩ :: sessRoundsN c cs os
  | _, _ => []

theorem sessMoves_eq (c : Simple) :
    ∀ (cs : List (Fin c.exports.length × List IVal)) (os : List (Option (List IVal))),
      sessMoves c cs os = twos (sessRoundsN c cs os)
  | [], _ => rfl
  | (_, _) :: _, [] => rfl
  | (j, vs) :: cs, o :: os => by
    show _ :: _ :: sessMoves c cs os = _ :: _ :: twos (sessRoundsN c cs os)
    rw [sessMoves_eq c cs os]

theorem sessRoundsN_forget (c : Simple) :
    ∀ (cs : List (Fin c.exports.length × List IVal)) (os : List (Option (List IVal))),
      (sessRoundsN c cs os).map Round.forget = sessLu cs os
  | [], _ => rfl
  | (_, _) :: _, [] => rfl
  | (j, vs) :: cs, o :: os => by
    show _ :: (sessRoundsN c cs os).map Round.forget = _
    rw [sessRoundsN_forget c cs os]
    rfl

theorem sessRounds_of_sessSpec {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance} :
    ∀ {calls : List (Fin c.exports.length × List IVal)} {outs : List (Option (List IVal))}
      {s s' : Store Nat}, SessSpec P c I s (specCalls c calls) outs s' →
      SessRounds P c I s (sessLu calls outs) s'
  | [], _, s, _, h => by
    cases h
    exact .nil s
  | (j, vs) :: calls, outs, s, s', h => by
    cases outs with
    | nil => cases h
    | cons o outs =>
      have h' : SessSpec P c I s ((c.exports[j], vs) :: specCalls c calls) (o :: outs) s' := h
      rcases sessSpec_cons_inv h' with ⟨ws, s₁, rfl, hret, h''⟩ | ⟨s₁, rfl, htrap, h''⟩
      · exact .ret j.isLt hret (sessRounds_of_sessSpec h'')
      · exact .trap j.isLt htrap (sessRounds_of_sessSpec h'')

theorem sessCalls_sessLu {c : Simple} :
    ∀ {calls : List (Fin c.exports.length × List IVal)} {outs : List (Option (List IVal))},
      TypedCalls c calls → calls.length = outs.length →
      sessCalls c (sessLu calls outs) = calls ∧ sessOuts c (sessLu calls outs) = outs
  | [], [], _, _ => ⟨rfl, rfl⟩
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h
  | (j, vs) :: calls, o :: outs, ht, hlen => by
    have hq : typedQ c (j.val, .vals vs) = some (j, vs) :=
      typedQ_typed j.isLt (ht _ List.mem_cons_self)
    obtain ⟨e₁, e₂⟩ := sessCalls_sessLu (calls := calls) (outs := outs)
      (fun q hq => ht q (List.mem_cons_of_mem _ hq)) (by simpa using hlen)
    refine ⟨?_, ?_⟩
    · show sessCalls c (⟨(j.val, .vals vs), o.map .vals⟩ :: sessLu calls outs) = _
      rw [sessCalls_some hq, e₁]
    · show sessOuts c (⟨(j.val, .vals vs), o.map .vals⟩ :: sessLu calls outs) = _
      rw [sessOuts_some hq, e₂]
      cases o <;> rfl

/-- **Completeness for sessions**: the IR play of a typed session is a reference session
behaviour. -/
theorem sess_complete (P : Profile) (prof : ProfileKind) (c : Simple) (hc : c.Adequate)
    (calls : List (Fin c.exports.length × List IVal)) (outs : List (Option (List IVal)))
    (ht : TypedCalls c calls) (hlen : calls.length = outs.length)
    (h : sessMoves c calls outs ∈ c.toComp.den (modSem P)) :
    refOuts outs ∈ sessObs P prof c calls := by
  obtain ⟨I, hI⟩ := hc.inst.inst
  rw [sessMoves_eq] at h
  obtain ⟨s, hS⟩ := sessRounds_of_den hc.good hI h
  rw [sessRoundsN_forget] at hS
  obtain ⟨hspec, -⟩ := spec_of_sessRounds hS
  obtain ⟨e₁, e₂⟩ := sessCalls_sessLu ht hlen
  rw [e₁, e₂] at hspec
  exact sess_specToRef P prof c hc hI calls outs s ht hspec

/-- **Soundness for sessions**: every reference session behaviour of typed calls is the IR play
of the session. -/
theorem sess_sound (P : Profile) (prof : ProfileKind) (c : Simple) (hc : c.Adequate)
    (calls : List (Fin c.exports.length × List IVal)) (ht : TypedCalls c calls)
    {o : List (Option (List Silmaril.Wasm.Component.Value.Val))}
    (ho : o ∈ sessObs P prof c calls) :
    ∃ outs, o = refOuts outs ∧ calls.length = outs.length ∧
      sessMoves c calls outs ∈ c.toComp.den (modSem P) := by
  obtain ⟨I, outs, s, hI, hspec, rfl⟩ := sess_refToSpec P prof c hc calls ht ho
  obtain ⟨L, hL, he⟩ := den_of_sessRounds hc.good hI (sessRounds_of_sessSpec hspec)
  rw [← sessRoundsN_forget] at he
  obtain rfl := forget_map_inj he
  refine ⟨outs, rfl, by simpa [specCalls] using sessSpec_length hspec, ?_⟩
  rw [sessMoves_eq]
  exact hL

/-! ## Adequacy -/

/-- **IR plays move along session observations.** -/
theorem pubPlays_subset {c c' : Simple} (hc : c.Adequate) (hc' : c'.Adequate)
    {len : c.exports.length = c'.exports.length} (hty : SameTy c c' len)
    (hsub : ∀ calls, TypedCalls c calls →
      sessObs P prof c calls ⊆ sessObs P prof c' (castCalls len calls)) :
    pubPlays (c.toComp.den (modSem P)) ⊆ pubPlays (c'.toComp.den (modSem P)) := by
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨I, hI⟩ := hc.inst.inst
  have key : ∀ L : List (Round (sigN c.toComp.exports.length)), twos L ∈ c.toComp.den (modSem P) →
      ∃ L' : List (Round (sigN c'.toComp.exports.length)),
        twos L' ∈ c'.toComp.den (modSem P) ∧ L'.map Round.forget = L.map Round.forget := by
    intro L hL
    obtain ⟨s, hS⟩ := sessRounds_of_den hc.good hI hL
    obtain ⟨hspec, ht⟩ := spec_of_sessRounds hS
    have href := hsub _ ht (sess_specToRef P prof c hc hI _ _ s ht hspec)
    obtain ⟨I', outs', s', hI', hspec', heq⟩ :=
      sess_refToSpec P prof c' hc' _ (typedCalls_cast hty ht) href
    obtain rfl := refOuts_inj heq
    rw [← sessCalls_cast hty, ← sessOuts_cast hty] at hspec'
    exact den_of_sessRounds hc'.good hI' (sessRounds_of_spec (shaped_cast hty (sessRounds_shaped hS))
      hspec')
  have hk : c.toComp.exports.length = c'.toComp.exports.length := by
    rw [toComp_length, toComp_length, len]
  rcases den_shape _ c hp with ⟨L, rfl⟩ | ⟨q, L, rfl⟩
  · obtain ⟨L', hL', he⟩ := key L hp
    exact ⟨twos L', hL', by rw [map_forgetMove_twos, map_forgetMove_twos, he]⟩
  · have hp₀ : twos L ∈ c.toComp.den (modSem P) := (c.toComp.den (modSem P)).of_prefix hp
      (List.prefix_append _ _)
    obtain ⟨L', hL', he⟩ := key L hp₀
    let q' : (sigN c'.toComp.exports.length).Op := (⟨q.1.val, hk ▸ q.1.isLt⟩, q.2)
    refine ⟨twos L' ++ [.inr (.ask q')], ?_, ?_⟩
    · exact (c'.toComp.den (modSem P)).receptive hL' (path_twos _) (Step.ask q') trivial
    · rw [List.map_append, List.map_append, map_forgetMove_twos, map_forgetMove_twos, he]
      rfl

/-- **Session observations move along IR plays.** -/
theorem sessObs_subset {c c' : Simple} (hc : c.Adequate) (hc' : c'.Adequate)
    {len : c.exports.length = c'.exports.length} (hty : SameTy c c' len)
    (hpl : pubPlays (c.toComp.den (modSem P)) ⊆ pubPlays (c'.toComp.den (modSem P)))
    (calls : List (Fin c.exports.length × List IVal)) (ht : TypedCalls c calls) :
    sessObs P prof c calls ⊆ sessObs P prof c' (castCalls len calls) := by
  intro o ho
  obtain ⟨outs, rfl, hlen, hmv⟩ := sess_sound P prof c hc calls ht ho
  rw [sessMoves_eq] at hmv
  obtain ⟨p', hp', hpe⟩ := hpl ⟨_, hmv, rfl⟩
  obtain ⟨I', hI'⟩ := hc'.inst.inst
  rcases den_shape _ c' hp' with ⟨L', rfl⟩ | ⟨q, L', rfl⟩
  · rw [map_forgetMove_twos, map_forgetMove_twos, sessRoundsN_forget] at hpe
    obtain ⟨s', hS'⟩ := sessRounds_of_den hc'.good hI' hp'
    rw [twos_inj hpe] at hS'
    obtain ⟨hspec', -⟩ := spec_of_sessRounds hS'
    obtain ⟨e₁, e₂⟩ := sessCalls_sessLu ht hlen
    rw [sessCalls_cast hty, sessOuts_cast hty, e₁, e₂] at hspec'
    exact sess_specToRef P prof c' hc' hI' _ outs s' (typedCalls_cast hty ht) hspec'
  · exfalso
    rw [List.map_append, map_forgetMove_twos, map_forgetMove_twos] at hpe
    exact twos_ne_twos_ask _ _ _ hpe.symm

theorem obs_right {c c' : Simple} (h : RefSessEquiv P prof c c') :
    ∀ calls', TypedCalls c' calls' →
      sessObs P prof c' calls' ⊆ sessObs P prof c (castCalls h.len.symm calls') := by
  intro calls' ht'
  have e := h.obs (castCalls h.len.symm calls') (typedCalls_cast (sameTy_symm h.ty) ht')
  rw [castCalls_cast h.len.symm calls'] at e
  exact e.symm.le

/-- **Resumable-session adequacy**: for adequate simple components, the resumable-session
equivalence on the reference machine is equality of export types and of IR plays at `sigU`. -/
theorem sessAdequacy (P : Profile) (prof : ProfileKind) {c c' : Simple} (hc : c.Adequate)
    (hc' : c'.Adequate) :
    RefSessEquiv P prof c c' ↔ SameTypes c c' ∧
      pubPlays (c.toComp.den (modSem P)) = pubPlays (c'.toComp.den (modSem P)) := by
  constructor
  · intro h
    refine ⟨sameTypes_iff.mpr ⟨h.len, h.ty⟩, Set.Subset.antisymm ?_ ?_⟩
    · exact pubPlays_subset hc hc' h.ty fun calls ht => (h.obs calls ht).le
    · exact pubPlays_subset hc' hc (sameTy_symm h.ty) (obs_right h)
  · rintro ⟨hst, heq⟩
    obtain ⟨len, hty⟩ := sameTypes_iff.mp hst
    refine ⟨len, hty, fun calls ht => Set.Subset.antisymm
      (sessObs_subset hc hc' hty heq.le calls ht) ?_⟩
    have h := sessObs_subset (prof := prof) hc' hc (sameTy_symm hty) heq.ge (castCalls len calls)
      (typedCalls_cast hty ht)
    rwa [castCalls_cast] at h

/-- **The session equivalence refines the public equivalence** of #669. -/
theorem refPubEquiv_of_sess {c c' : Simple} (hc : c.Adequate) (hc' : c'.Adequate)
    (h : RefSessEquiv P prof c c') : RefPubEquiv P prof c c' := by
  obtain ⟨hst, he⟩ := (sessAdequacy P prof hc hc').mp h
  refine (adequacy P prof hc hc').mpr ⟨hst, ?_⟩
  simp only [trapLastPlays, he]

end Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy
