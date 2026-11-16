module

public import Silmaril.Proofs.Wasm.Component.Reference.Adequacy.RefSeq
public import Silmaril.Proofs.Wasm.Component.Reference.Adequacy.IRPlays
public import Silmaril.Proofs.Wasm.Component.Reference.FloatSound

/-!
# Moving specification chains between components with the same public observations

`ObsSub P prof c c'`: every terminating public observation of `c` (`seqObs`) is one of `c'`.
Through the reference machine (`seq_specToRef` for `c`, then `seq_refToSpec` for `c'`):

* `transfer_last`: a chain of returned calls of `c` from its instance's store with a
  terminating outcome of a last call is a chain of `c'` with the same results and the same
  outcome of the last call;
* `chain_transfer`: a chain of returned calls of `c` alone is one of `c'` (the last returned call
  is a terminating outcome).

Also: returned calls are `returns` outcomes of the specification and conversely
(`specAt_of_retAt`, `retAt_of_specAt`), chains split at an append (`seqSpec_append_inv`), and the
specification rounds of complete IR rounds whose answers are all results are a chain
(`chain_of_specRounds`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.Adequacy

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core (Store)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "ROutcome" => Silmaril.Wasm.Component.Reference.Outcome

variable {P : Profile} {prof : ProfileKind}

/-! ## Returned calls and `returns` outcomes -/

theorem specAt_of_retAt {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance} {x : SimpleExport}
    {vs ws : List IVal} {s s' : Store Nat} (h : RetAt P c I x vs s ws s') :
    Silmaril.Wasm.Component.Reference.Outcome.returns (some (ws.map toRefVal)) ∈ specAt P c I x vs s := by
  obtain ⟨t', cvs, ys, run, final, hys, hws⟩ := h.run
  unfold specAt
  rw [checkLower_of_check h.typed]
  refine .inl ⟨some ys, ⟨_, .values cvs, internalP_steps (H := Nat) run, final, hys.symm⟩, ?_⟩
  simp only [liftOutcome, hws]

theorem retAt_of_specAt {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance} {x : SimpleExport}
    {vs : List IVal} {s : Store Nat} {rs : List Silmaril.Wasm.Component.Value.Val}
    (hvs : ValTy.checkList x.ty.params vs = true)
    (h : Silmaril.Wasm.Component.Reference.Outcome.returns (some rs) ∈ specAt P c I x vs s) :
    ∃ ws s', rs = ws.map toRefVal ∧ RetAt P c I x vs s ws s' := by
  unfold specAt at h
  rw [checkLower_of_check hvs] at h
  rcases h with ⟨r, ⟨c', res, steps, final, rfl⟩, hb⟩ | ⟨h, -⟩
  · obtain ⟨s', t', run, final'⟩ := (Silmaril.Wasm.Game.ret_iff_core (s := s)
      (t := Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (I.addrs.getD x.core 0)
        (lowerArgs x.ty.params vs))).mpr ⟨c', steps, final⟩
    cases res with
    | values cvs =>
      cases hys : cvs.mapM Silmaril.Wasm.SingleThreaded.toFlat? with
      | none => simp only [hys, liftOutcome] at hb; cases hb
      | some ys =>
        cases hws : liftArgs x.ty.results ys with
        | none => simp only [hys, liftOutcome, hws] at hb; cases hb
        | some ws =>
          have hrs : rs = ws.map toRefVal := by simpa [hys, liftOutcome, hws] using hb
          exact ⟨ws, s', hrs, hvs, t', cvs, ys, run, final', hys, hws⟩
    | trap => simp only [liftOutcome] at hb; cases hb
    | throw a => simp only [liftOutcome] at hb; cases hb
  · cases h

/-! ## Chains -/

theorem seqSpec_append {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance} :
    ∀ {s₁ s₂ s₃ : Store Nat} {cs₁ cs₂ : List (SimpleExport × List IVal)}
      {wss₁ wss₂ : List (List IVal)}, SeqSpec P c I s₁ cs₁ wss₁ s₂ → SeqSpec P c I s₂ cs₂ wss₂ s₃ →
      SeqSpec P c I s₁ (cs₁ ++ cs₂) (wss₁ ++ wss₂) s₃
  | _, _, _, _, _, _, _, .nil _, h₂ => h₂
  | _, _, _, _, _, _, _, .cons h h₁, h₂ => .cons h (seqSpec_append h₁ h₂)

theorem seqSpec_append_inv {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance} :
    ∀ {s₁ s₃ : Store Nat} (cs₁ : List (SimpleExport × List IVal))
      {cs₂ : List (SimpleExport × List IVal)} {wss : List (List IVal)},
      SeqSpec P c I s₁ (cs₁ ++ cs₂) wss s₃ →
      ∃ wss₁ wss₂ s₂, wss = wss₁ ++ wss₂ ∧ SeqSpec P c I s₁ cs₁ wss₁ s₂ ∧
        SeqSpec P c I s₂ cs₂ wss₂ s₃
  | s₁, _, [], _, wss, h => ⟨[], wss, s₁, rfl, .nil _, h⟩
  | _, _, x :: cs₁, _, _, h => by
    cases h with
    | cons hr h' =>
      obtain ⟨wss₁, wss₂, s₂, rfl, h₁, h₂⟩ := seqSpec_append_inv cs₁ h'
      exact ⟨_ :: wss₁, wss₂, s₂, rfl, .cons hr h₁, h₂⟩

/-! ## Observations of two components -/

/-- Every terminating public observation of `c` is one of `c'`. -/
def ObsSub (P : Profile) (prof : ProfileKind) (c c' : Simple)
    (len : c.exports.length = c'.exports.length) : Prop :=
  ∀ (calls : List (Fin c.exports.length × List IVal)) (j : Fin c.exports.length) (vs : List IVal),
    TypedCalls c calls → ValTy.checkList c.exports[j].ty.params vs = true →
    seqObs P prof c calls j vs ⊆ seqObs P prof c' (castCalls len calls) (Fin.cast len j) vs

/-- The same export types, index by index. -/
def SameTy (c c' : Simple) (len : c.exports.length = c'.exports.length) : Prop :=
  ∀ j : Fin c.exports.length, c'.exports[Fin.cast len j].ty = c.exports[j].ty

theorem typedCalls_cast {c c' : Simple} {len : c.exports.length = c'.exports.length}
    (hty : SameTy c c' len) {calls : List (Fin c.exports.length × List IVal)}
    (ht : TypedCalls c calls) : TypedCalls c' (castCalls len calls) := by
  intro q hq
  obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.mp hq
  show ValTy.checkList c'.exports[Fin.cast len q₀.1].ty.params q₀.2 = true
  rw [hty]
  exact ht q₀ hq₀

theorem map_map_toRefVal_inj {wss wss' : List (List IVal)}
    (h : wss.map (·.map toRefVal) = wss'.map (·.map toRefVal)) : wss = wss' := by
  induction wss generalizing wss' with
  | nil => cases wss' with
    | nil => rfl
    | cons _ _ => cases h
  | cons ws wss ih => cases wss' with
    | nil => cases h
    | cons ws' wss' =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [map_toRefVal_inj h.1, ih h.2]

/-- **A chain with a terminating last outcome moves to `c'`.** -/
theorem transfer_last {c c' : Simple} (hc : c.Adequate) (hc' : c'.Adequate)
    {len : c.exports.length = c'.exports.length} (hty : SameTy c c' len)
    (hsub : ObsSub P prof c c' len) {I : Silmaril.Wasm.Game.ScalarInstance} (hI : c.mod.IsInst I)
    {calls : List (Fin c.exports.length × List IVal)} {wss : List (List IVal)} {s : Store Nat}
    (ht : TypedCalls c calls) (hseq : SeqSpec P c I I.store (specCalls c calls) wss s)
    {j : Fin c.exports.length} {vs : List IVal}
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) {b : ROutcome}
    (hb : b ∈ specAt P c I c.exports[j] vs s) (hterm : b.Term) :
    ∃ (I' : Silmaril.Wasm.Game.ScalarInstance) (s' : Store Nat), c'.mod.IsInst I' ∧
      SeqSpec P c' I' I'.store (specCalls c' (castCalls len calls)) wss s' ∧
      b ∈ specAt P c' I' c'.exports[Fin.cast len j] vs s' := by
  have href := seq_specToRef P prof c hc.good hc.floatFree hc.inst hc.arity hI calls wss s j vs ht
    hvs hseq hb hterm
  obtain ⟨href', -⟩ := hsub calls j vs ht hvs ⟨href, hterm⟩
  have hvs' : ValTy.checkList c'.exports[Fin.cast len j].ty.params vs = true := by
    rw [hty]; exact hvs
  obtain ⟨I', wss', s', hI', hseq', hw, hb'⟩ := seq_refToSpec P prof c' hc'.good hc'.floatFree
    hc'.inst hc'.arity (castCalls len calls) (Fin.cast len j) vs (typedCalls_cast hty ht) hvs' _ href'
  obtain rfl := map_map_toRefVal_inj hw
  exact ⟨I', s', hI', hseq', hb'⟩

/-- **A chain of returned calls moves to `c'`.** -/
theorem chain_transfer {c c' : Simple} (hc : c.Adequate) (hc' : c'.Adequate)
    {len : c.exports.length = c'.exports.length} (hty : SameTy c c' len)
    (hsub : ObsSub P prof c c' len) {I : Silmaril.Wasm.Game.ScalarInstance} (hI : c.mod.IsInst I) :
    ∀ (calls : List (Fin c.exports.length × List IVal)) (wss : List (List IVal)) (s : Store Nat),
      TypedCalls c calls → SeqSpec P c I I.store (specCalls c calls) wss s →
      ∃ (I' : Silmaril.Wasm.Game.ScalarInstance) (s' : Store Nat), c'.mod.IsInst I' ∧
        SeqSpec P c' I' I'.store (specCalls c' (castCalls len calls)) wss s' := by
  intro calls
  induction calls using List.reverseRecOn with
  | nil =>
    intro wss s _ h
    cases h
    obtain ⟨I', hI'⟩ := hc'.inst.inst
    exact ⟨I', I'.store, hI', .nil _⟩
  | append_singleton calls₀ q _ =>
    intro wss s ht h
    obtain ⟨j, vs⟩ := q
    have h' : SeqSpec P c I I.store (specCalls c calls₀ ++ [(c.exports[j], vs)]) wss s := by
      simpa only [specCalls, List.map_append, List.map_cons, List.map_nil] using h
    obtain ⟨wss₀, wss₁, s₀, rfl, h₀, h₁⟩ := seqSpec_append_inv _ h'
    cases h₁ with
    | cons hret h₂ =>
      cases h₂
      have ht₀ : TypedCalls c calls₀ := fun q hq => ht q (List.mem_append_left _ hq)
      obtain ⟨I', s₀', hI', hseq', hb'⟩ := transfer_last (prof := prof) hc hc' hty hsub hI ht₀ h₀
        hret.typed (specAt_of_retAt hret) trivial
      have hvs' : ValTy.checkList c'.exports[Fin.cast len j].ty.params vs = true := by
        rw [hty]; exact hret.typed
      obtain ⟨ws', s', hws, hret'⟩ := retAt_of_specAt hvs' hb'
      obtain rfl := map_toRefVal_inj hws
      refine ⟨I', s', hI', ?_⟩
      have e : specCalls c' (castCalls len (calls₀ ++ [(j, vs)])) =
          specCalls c' (castCalls len calls₀) ++ [(c'.exports[Fin.cast len j], vs)] := by
        simp only [specCalls, castCalls, List.map_append, List.map_cons, List.map_nil]
      rw [e]
      exact seqSpec_append hseq' (.cons hret' (.nil _))

/-! ## Specification rounds of complete IR rounds -/

/-- Complete rounds whose answers are all results are a chain of returned calls, followed by
the rest. -/
theorem chain_of_specRounds {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance} :
    ∀ (M₀ : List (Round sigU)) {T : List (Round sigU)} {s : Store Nat},
      (∀ x ∈ M₀, x.2.isSome) → SpecRounds P c I s (M₀ ++ T) →
      ∃ (calls : List (Fin c.exports.length × List IVal)) (wss : List (List IVal)) (s₁ : Store Nat),
        M₀ = (seqRounds c calls wss).map Round.forget ∧ calls.length = wss.length ∧
        TypedCalls c calls ∧ SeqSpec P c I s (specCalls c calls) wss s₁ ∧ SpecRounds P c I s₁ T
  | [], _, s, _, h => ⟨[], [], s, rfl, rfl, (fun _ h => nomatch h), .nil _, h⟩
  | ⟨(j, p), A⟩ :: M₀, T, s, hs, h => by
    cases h with
    | @cons _ s₁ _ _ hr h' =>
      have hA : A.isSome := hs _ List.mem_cons_self
      rcases hr with ⟨rfl, -, -⟩ | ⟨hj, vs, xs, r, rfl, hl, hr, rfl, hret, -⟩
      · cases hA
      cases r with
      | none => cases hA
      | some ys =>
        cases hws : liftArgs c.exports[j].ty.results ys with
        | none => simp [Adapter.up, hws] at hA
        | some ws =>
          have hret' := hret ys ws rfl hws
          obtain ⟨calls, wss, s₂, hM, hlen, ht, hseq, hT⟩ := chain_of_specRounds M₀
            (fun x hx => hs x (List.mem_cons_of_mem _ hx)) h'
          refine ⟨(⟨j, hj⟩, vs) :: calls, ws :: wss, s₂, ?_, by simp [hlen], ?_, .cons hret' hseq, hT⟩
          · simp only [Option.map_some, Option.bind_some, Adapter.up, hws]
            rw [hM]
            rfl
          · intro q hq
            rcases List.mem_cons.mp hq with rfl | hq
            · exact hret'.typed
            · exact ht q hq

end Silmaril.Proofs.Wasm.Component.Reference.Adequacy
