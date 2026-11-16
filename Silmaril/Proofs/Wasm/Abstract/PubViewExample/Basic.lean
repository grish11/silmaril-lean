module

public import Silmaril.Wasm.Abstract.PubViewExample.Defs
public import Silmaril.Proofs.Wasm.Abstract.PubViewExample.Run
public import Silmaril.Proofs.Wasm.Abstract.PubViewExample.Store

/-!
# A store view that identifies an internal call with its inlining (proofs)

With host function type `Empty` there are no host calls: every host is the empty one
(`host_eq`), every log is empty (`log_nil`), and a labelled run is a host-free Core run
(`evRun_iff`). An export satisfying `Spec` is admitted exactly on the empty argument list and
runs deterministically (`DetRun`) to the values `ws₀` in its own store. Two such exports with
the same values and stores of the same view are `PubEquivV` (`pubEquivV_of_spec`), and with
different stores they are not `PubEquiv` (`not_pubEquiv_of_spec`). The two exports of the
example satisfy `Spec` (`callSpec`, `inlineSpec`), by the explicit Core runs of
`Silmaril.Proofs.Wasm.Abstract.PubViewExample.Run`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.PubViewExample

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Abstract.PubViewExample
open Silmaril.Wasm.Numerics (Profile)

variable {O : Type} {π : Store Empty → O} {P : Profile} {host : HostSemantics Empty}
  {Ok : Store Empty → Nat × List Val → Prop}

/-! ## No host calls -/

/-- With host function type `Empty`, every host is the empty one. -/
theorem host_eq (host : HostSemantics Empty) : host = fun _ _ _ _ => False :=
  funext fun h => h.elim

theorem log_nil : ∀ cs : List (Call (wasmHostSig Empty)), cs = []
  | [] => rfl
  | ⟨m, _⟩ :: _ => m.1.elim

/-- A labelled run is a host-free Core run with the empty log. -/
theorem evRun_iff {c d : Config Empty} {cs : List (Call (wasmHostSig Empty))} :
    EvRun P host c cs d ↔ cs = [] ∧ Steps P (fun _ _ _ _ => False) c d := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨rfl, .refl⟩
    | silent hst _ ih =>
      unfold HEvStep at hst
      rcases hst with hst | ⟨-, _, _, hh, _⟩
      · exact ⟨ih.1, .head hst ih.2⟩
      · exact hh.elim
    | @event _ _ _ e _ _ _ _ => exact e.1.1.elim
  · rintro ⟨rfl, h⟩
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact .refl _
    | head hst _ ih => exact .silent (Or.inl hst) ih

/-! ## Exports that run deterministically to values -/

/-- **The example's export shape**: admitted by `Ok` exactly on the empty argument list, where
the invocation runs deterministically to the values `ws₀` in the store `s`. -/
structure Spec (P : Profile) (Ok : Store Empty → Nat × List Val → Prop) (s : Store Empty)
    (a : Nat) (ws₀ : List Val) : Prop where
  ok : ∀ vs, Ok s (a, vs) ↔ vs = []
  run : DetRun P (fun _ _ _ _ => False) s (invoke s a []) ⟨s, {}, vals ws₀⟩

theorem Spec.reach {s : Store Empty} {a : Nat} {ws₀ vs : List Val} (h : Spec P Ok s a ws₀)
    (hok : Ok s (a, vs)) {cs : List (Call (wasmHostSig Empty))} {d : Config Empty}
    (hr : EvRun P host (invoke s a vs) cs d) :
    vs = [] ∧ cs = [] ∧ DetRun P (fun _ _ _ _ => False) s d ⟨s, {}, vals ws₀⟩ := by
  obtain rfl := (h.ok vs).mp hok
  obtain ⟨rfl, hs⟩ := evRun_iff.mp hr
  exact ⟨rfl, rfl, h.run.of_steps hs⟩

/-- The returns of a `Spec` export: the values `ws₀`, the empty log and the store `s`. -/
theorem Spec.ret_iff {s : Store Empty} {a : Nat} {ws₀ : List Val} (h : Spec P Ok s a ws₀)
    (vs : List Val) (l : List (Call (viewSig Empty O))) (ws : List Val) (o : O) :
    (Ok s (a, vs) ∧ ∃ (cs : List (Call (wasmHostSig Empty))) (s₂ : Store Empty),
        EvRun P host (invoke s a vs) cs ⟨s₂, {}, vals ws⟩ ∧ cs.map (viewCall π) = l ∧
        π s₂ = o) ↔
      vs = [] ∧ ws = ws₀ ∧ l = [] ∧ o = π s := by
  constructor
  · rintro ⟨hok, cs, s₂, hr, rfl, rfl⟩
    obtain ⟨rfl, rfl, hd⟩ := h.reach hok hr
    rcases hd.cases with he | ⟨-, hv, -⟩
    · simp only [Config.mk.injEq] at he
      obtain ⟨rfl, -, hc⟩ := he
      exact ⟨rfl, SingleThreaded.vals_injective hc, rfl, rfl⟩
    · exact (hv ws rfl).elim
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨(h.ok []).mpr rfl, [], s, evRun_iff.mpr ⟨rfl, h.run.steps⟩, rfl, rfl⟩

theorem Spec.no_trap {s : Store Empty} {a : Nat} {ws₀ : List Val} (h : Spec P Ok s a ws₀)
    (vs : List Val) (l : List (Call (viewSig Empty O))) :
    ¬ (Ok s (a, vs) ∧ ∃ (cs : List (Call (wasmHostSig Empty))) (s₂ : Store Empty),
        EvRun P host (invoke s a vs) cs ⟨s₂, {}, [.trap]⟩ ∧ cs.map (viewCall π) = l) := by
  rintro ⟨hok, cs, s₂, hr, -⟩
  obtain ⟨-, -, hd⟩ := h.reach hok hr
  rcases hd.cases with he | ⟨-, -, ht⟩
  · simp only [Config.mk.injEq] at he
    exact vals_ne_split (ws := ws₀) (us := []) (d := .trap) (r := []) (by rw [← he.2.2]; rfl)
  · exact ht rfl

theorem Spec.no_div {s : Store Empty} {a : Nat} {ws₀ : List Val} (h : Spec P Ok s a ws₀)
    (vs : List Val) (l : List (Call (viewSig Empty O))) :
    ¬ (Ok s (a, vs) ∧ ∃ (cs : List (Call (wasmHostSig Empty))) (c : Config Empty),
        EvRun P host (invoke s a vs) cs c ∧ Diverges P (fun _ _ _ _ => False) c ∧
        cs.map (viewCall π) = l) := by
  rintro ⟨hok, cs, c, hr, hdiv, -⟩
  obtain ⟨-, -, hd⟩ := h.reach hok hr
  exact hd.not_diverges hdiv

/-- **Two `Spec` exports with the same values and stores of the same view are `PubEquivV`.** -/
theorem pubEquivV_of_spec {s s' : Store Empty} {a a' : Nat} {ws₀ : List Val}
    (h : Spec P Ok s a ws₀) (h' : Spec P Ok s' a' ws₀) (hπ : π s = π s') :
    PubEquivV π P host Ok s a s' a' := by
  intro vs
  refine ⟨fun l ws o => ?_, fun l => iff_of_false (h.no_trap vs l) (h'.no_trap vs l),
    fun _ hh _ _ => hh.elim, fun l => iff_of_false (h.no_div vs l) (h'.no_div vs l),
    fun _ => iff_of_false (fun ⟨_, ω, _⟩ => (ω 0).1.1.elim)
      (fun ⟨_, ω, _⟩ => (ω 0).1.1.elim)⟩
  rw [h.ret_iff, h'.ret_iff, hπ]

/-- **Two `Spec` exports with different stores are not `PubEquiv`**: the final store of the
first export's return is not a final store of the second's. -/
theorem not_pubEquiv_of_spec {s s' : Store Empty} {a a' : Nat} {ws₀ ws₁ : List Val}
    (h : Spec P Ok s a ws₀) (h' : Spec P Ok s' a' ws₁) (hne : s ≠ s') :
    ¬ PubEquiv P host Ok s a s' a' := by
  intro hE
  obtain ⟨hok', hr'⟩ := ((hE []).1 [] ws₀ s).mp
    ⟨(h.ok []).mpr rfl, evRun_iff.mpr ⟨rfl, h.run.steps⟩⟩
  obtain ⟨-, -, hd⟩ := h'.reach hok' hr'
  rcases hd.cases with he | ⟨hs, -, -⟩
  · exact hne (congrArg Config.store he)
  · exact hne hs

/-! ## The two exports -/

theorem invoke_eq {s : Store Empty} {a : Nat} {fi : FuncInst Empty}
    (hf : s.funcs[a]? = some fi) :
    invoke s a [] = ⟨s, {}, [.ref (.func a), .callRefType fi.type]⟩ := by
  simp [invoke, hf]

/-- One `DetRun` step on a code whose first non-value is `Inert`. -/
theorem DetRun.step' {s : Store Empty} {c c' e : Config Empty} {us : List Val} {d : Admin}
    {r : List Admin} (hs : c.store = s) (hsp : splitVals c.code = (us, d :: r)) (hd : Inert d)
    (h : Next P (fun _ _ _ _ => False) c c') (hr : DetRun P (fun _ _ _ _ => False) s c' e) :
    DetRun P (fun _ _ _ _ => False) s c e :=
  .step hs (mid_of_split hsp hd).1 (mid_of_split hsp hd).2 h hr

/-- A single `FRAME` or `LABEL` is its own first non-value. -/
theorem split_one (d : Admin) (hd : d.val? = none) : splitVals [d] = ([], [d]) :=
  split_of [] d [] rfl hd

/-- **The Core run of the export with the internal call**: enter `0`, resolve `call 1`, enter
`1`, and return `42` through both frames. -/
theorem callRun :
    DetRun P (fun _ _ _ _ => False) callStore (invoke callStore 0 [])
      ⟨callStore, {}, vals [.i32 42]⟩ := by
  obtain ⟨fi, ⟨ty, loc, body⟩, x, ps, rs, hf, hc, hl, hb, hx, he, hps, hrs⟩ :=
    callsB_sound callStore_calls
  obtain ⟨fi₁, ⟨ty₁, loc₁, body₁⟩, ps₁, rs₁, hf₁, hc₁, hl₁, hb₁, he₁, hps₁, hrs₁⟩ :=
    constB_sound callStore_const
  change loc = [] at hl; change body = _ at hb; change loc₁ = [] at hl₁
  change body₁ = _ at hb₁
  subst hl hb hl₁ hb₁
  rw [invoke_eq hf]
  have h1 : [Val.i32 42].length = rs.length := hrs.symm
  have h2 : [Val.i32 42].length = rs₁.length := hrs₁.symm
  have n0 := next_callRef (P := P) (host := fun _ _ _ _ => False) (f := {}) hf hc he hps
  have n1 := next_call (P := P) (host := fun _ _ _ _ => False)
    (f := Frame.forCall fi.module [] []) hx hf₁
  have n2 := next_callRef (P := P) (host := fun _ _ _ _ => False)
    (f := Frame.forCall fi.module [] []) hf₁ hc₁ he₁ hps₁
  refine DetRun.step' rfl (split_of [.ref (.func 0)] _ [] (by rfl) (by rfl)) (by trivial) n0 ?_
  refine DetRun.step' rfl (split_one _ (by rfl)) (by trivial)
    (Next.frame (split_one _ (by rfl)) (by trivial)
      (Next.label (split_one _ (by rfl)) (by trivial) n1)) ?_
  refine DetRun.step' rfl (split_one _ (by rfl)) (by trivial)
    (Next.frame (split_one _ (by rfl)) (by trivial)
      (Next.label (split_of [.ref (.func 1)] _ [] (by rfl) (by rfl)) (by trivial) n2)) ?_
  refine DetRun.step' rfl (split_one _ (by rfl)) (by trivial)
    (Next.frame (split_one _ (by rfl)) (by trivial) (Next.label (split_one _ (by rfl)) (by trivial)
      (Next.frame (split_one _ (by rfl)) (by trivial) (next_labelVals (ws := [.i32 42]))))) ?_
  refine DetRun.step' rfl (split_one _ (by rfl)) (by trivial)
    (Next.frame (split_one _ (by rfl)) (by trivial) (Next.label (split_one _ (by rfl)) (by trivial)
      (next_frameVals h2))) ?_
  refine DetRun.step' rfl (split_one _ (by rfl)) (by trivial)
    (Next.frame (split_one _ (by rfl)) (by trivial) (next_labelVals (ws := [.i32 42]))) ?_
  refine DetRun.step' rfl (split_one _ (by rfl)) (by trivial) (next_frameVals h1) ?_
  exact .done _ _

/-- **The Core run of the inlined export**: enter `0` and return `42`. -/
theorem inlineRun :
    DetRun P (fun _ _ _ _ => False) inlineStore (invoke inlineStore 0 [])
      ⟨inlineStore, {}, vals [.i32 42]⟩ := by
  obtain ⟨fi, ⟨ty, loc, body⟩, ps, rs, hf, hc, hl, hb, he, hps, hrs⟩ :=
    constB_sound inlineStore_const
  change loc = [] at hl; change body = _ at hb
  subst hl hb
  rw [invoke_eq hf]
  have h1 : [Val.i32 42].length = rs.length := hrs.symm
  have n0 := next_callRef (P := P) (host := fun _ _ _ _ => False) (f := {}) hf hc he hps
  refine DetRun.step' rfl (split_of [.ref (.func 0)] _ [] (by rfl) (by rfl)) (by trivial) n0 ?_
  refine DetRun.step' rfl (split_one _ (by rfl)) (by trivial)
    (Next.frame (split_one _ (by rfl)) (by trivial) (next_labelVals (ws := [.i32 42]))) ?_
  refine DetRun.step' rfl (split_one _ (by rfl)) (by trivial) (next_frameVals h1) ?_
  exact .done _ _

theorem callStore_ok : StoreOk callStore := prepStore_ok callMod_valid callMod_prep

theorem inlineStore_ok : StoreOk inlineStore := prepStore_ok inlineMod_valid inlineMod_prep

theorem invOk_callStore_iff (vs : List Val) : InvOk callStore (0, vs) ↔ vs = [] := by
  obtain ⟨fi, fn, x, ps, rs, hf, -, -, -, -, he, hps, -⟩ := callsB_sound callStore_calls
  exact invOk_iff callStore_ok (Interp.storeChk_of_check callStore_chk) hf he hps vs

theorem invOk_inlineStore_iff (vs : List Val) : InvOk inlineStore (0, vs) ↔ vs = [] := by
  obtain ⟨fi, fn, ps, rs, hf, -, -, -, he, hps, -⟩ := constB_sound inlineStore_const
  exact invOk_iff inlineStore_ok (Interp.storeChk_of_check inlineStore_chk) hf he hps vs

theorem callSpec : Spec P InvOk callStore 0 [.i32 42] := ⟨invOk_callStore_iff, callRun⟩

theorem inlineSpec : Spec P InvOk inlineStore 0 [.i32 42] := ⟨invOk_inlineStore_iff, inlineRun⟩

theorem callStore_ne_inlineStore : callStore ≠ inlineStore := by
  intro h
  have h₁ := callStore_calls
  rw [h, callStore_ne] at h₁
  cases h₁

end Silmaril.Proofs.Wasm.Abstract.PubViewExample
