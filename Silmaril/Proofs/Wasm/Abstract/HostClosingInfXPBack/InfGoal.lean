module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack.InfSplit

/-!
# Productive runs: the statements and glue (proofs)

In the deterministic profile `SingleThreaded.profile o`, for a host with typed answers in the
host slices:

* `CallInfX J z K ω`: `K` is a typed call of `z` in some `call_ref` form under values, with
  nothing after it, and runs productively with `ω`;
* `InfOutX J s f stk es ω`: the trees run productively within their function (`InfLXP`), their
  open calls resolved to exactly `ω`; or they reach a call `z` after a resolved prefix `q`, and
  the call runs productively with the rest (`CallInfX J`). When `q` is empty the reach is a
  host-free run into a context around the call (`Lifts`): infinitely many of those in a row
  would be host-free divergence, which a productive run is not;
* `InfG J es`: every typed problem of the trees `es` with a productive Core run is `InfOutX J`.

Glue: contexts lifting host-free steps (`Lifts`), lifting `InfOutX J` through the constructors
(`infOut_lift`), a finished head tree ruled out (`head_contraI`) and a head tree run normally in
front of the trees after it (`head_consI`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Abstract.CallXP (POut)
open Silmaril.Wasm.Binaryen (BExpr liftInstrs)
open Shape (streamAppend)

variable {H : Type} {J : Silmaril.Wasm.Interp.BackInv H}

/-! ## The statements -/

/-- The configuration of trees on a stack. -/
abbrev pcfg (s : Store H) (f : Frame) (stk : List Val) (es : List BExpr) : Config H :=
  ⟨s, f, xcode stk es⟩

/-- A context lifting host-free steps. -/
def Lifts (o : GrowOracle) (W : Config H → Config H) : Prop :=
  ∀ a b, Det.DStep o a b → Det.DStep o (W a) (W b)

/-- **A typed call running productively**, in some frame and `call_ref` form, under values, with
nothing after it. -/
def CallInfX (J : Silmaril.Wasm.Interp.BackInv H) (tags : List TagInst) (o : GrowOracle) (host : HostSemantics H)
    (z : (wasmOShape H).self.Op) (K : Config H) (ω : Nat → Call (wasmHostSig H)) : Prop :=
  ∃ (f : Frame) (pre : List Val) (cr : Admin), cr.IsCallRef ∧
    K = ⟨z.2.2, f, Interp.callCode pre z.2.1 z.1 cr []⟩ ∧ CallChkP tags z.2.2 z.1 z.2.1 ∧
    J.CT K ∧ CoreInf (profile o) host K ω

/-- **The canonical reading of a productive run of trees.** -/
def InfOutX (J : Silmaril.Wasm.Interp.BackInv H) (tags : List TagInst) (o : GrowOracle) (host : HostSemantics H) (s : Store H)
    (f : Frame) (stk : List Val) (es : List BExpr) (ω : Nat → Call (wasmHostSig H)) : Prop :=
  (∃ ν : Nat → OCall H, InfLXP s f stk es ν ∧ Shape.SubstInf Cl (fun i => (ν i).lift) ω) ∨
    ∃ (l : List (OCall H)) (z : (wasmOShape H).self.Op) (q : List (Call (wasmHostSig H)))
      (K : Config H) (ω' : Nat → Call (wasmHostSig H)), ReachLXP s f stk es l z ∧
      Shape.SubstPre Cl (l.map OCall.lift) q ∧ CallInfX J tags o host z K ω' ∧ ω = q ++ω ω' ∧
      (q = [] → ∃ W, Lifts o W ∧ Relation.ReflTransGen (Det.DStep o) (pcfg s f stk es) (W K))

/-- **The productive backward simulation of trees.** -/
def InfG (J : Silmaril.Wasm.Interp.BackInv H) (tags : List TagInst) (o : GrowOracle) (host : HostSemantics H) (es : List BExpr) :
    Prop :=
  ∀ (s : Store H) (f : Frame) (stk : List Val) (ω : Nat → Call (wasmHostSig H)),
    J.TypedP tags s f stk es → CoreInf (profile o) host (pcfg s f stk es) ω →
    InfOutX J tags o host s f stk es ω

/-! ## Contexts -/

variable {o : GrowOracle}

theorem Lifts.comp {W₁ W₂ : Config H → Config H} (h₁ : Lifts o W₁) (h₂ : Lifts o W₂) :
    Lifts o (fun c => W₁ (W₂ c)) := fun _ _ h => h₁ _ _ (h₂ _ _ h)

theorem Lifts.rtg {W : Config H → Config H} (hW : Lifts o W) {a b : Config H}
    (h : Relation.ReflTransGen (Det.DStep o) a b) :
    Relation.ReflTransGen (Det.DStep o) (W a) (W b) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (hW _ _ hs)

theorem Lifts.tg {W : Config H → Config H} (hW : Lifts o W) {a b : Config H}
    (h : Relation.TransGen (Det.DStep o) a b) : Relation.TransGen (Det.DStep o) (W a) (W b) := by
  induction h with
  | single hs => exact .single (hW _ _ hs)
  | tail _ hs ih => exact ih.tail (hW _ _ hs)

theorem lifts_id : Lifts o (fun c : Config H => c) := fun _ _ h => h

theorem lifts_suffix (rest : List Admin) :
    Lifts o (fun c : Config H => ⟨c.store, c.frame, c.code ++ rest⟩) :=
  fun ⟨_, _, _⟩ ⟨_, _, _⟩ h => Sim.Step.append_right h rest

theorem lifts_label (ws : List Val) (n : Nat) (cont : List Instr) (rest : List Admin) :
    Lifts o (fun c : Config H => ⟨c.store, c.frame, vals ws ++ [.label n cont c.code] ++ rest⟩) :=
  fun ⟨_, _, _⟩ ⟨_, _, _⟩ h => Silmaril.Wasm.Logic.Core.Step.ctx ws rest (Step.ctxtLabel h)

theorem lifts_handler (ws : List Val) (n : Nat) (cs : List Catch) (rest : List Admin) :
    Lifts o (fun c : Config H => ⟨c.store, c.frame, vals ws ++ [.handler n cs c.code] ++ rest⟩) :=
  fun ⟨_, _, _⟩ ⟨_, _, _⟩ h => Silmaril.Wasm.Logic.Core.Step.ctx ws rest (Step.ctxtHandler h)

theorem lifts_frame (f : Frame) (ws : List Val) (n : Nat) (rest : List Admin) :
    Lifts o (fun c : Config H =>
      ⟨c.store, f, vals ws ++ [.frame n c.frame [.label n [] c.code]] ++ rest⟩) :=
  fun ⟨_, _, _⟩ ⟨_, _, _⟩ h =>
    Silmaril.Wasm.Logic.Core.Step.ctx ws rest (Step.ctxtFrame (Step.ctxtLabel h))

theorem rtg_trans_tg {R : Config H → Config H → Prop} {a b c : Config H}
    (h : Relation.ReflTransGen R a b) (h' : Relation.TransGen R b c) : Relation.TransGen R a c := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact h'
  | head hab _ ih => exact .head hab ih

theorem tg_trans_rtg {R : Config H → Config H → Prop} {a b c : Config H}
    (h : Relation.TransGen R a b) (h' : Relation.ReflTransGen R b c) : Relation.TransGen R a c := by
  induction h' with
  | refl => exact h
  | tail _ hs ih => exact ih.tail hs

theorem evRunN_nil_dsteps {host : HostSemantics H} {k : Nat} {X Y : Config H}
    (h : EvRunN (profile o) host k X [] Y) : Relation.ReflTransGen (Det.DStep o) X Y :=
  silentRun_dsteps (evRun_nil_silentRun (evRunN_evRun h))

theorem lift_streamAppend (l : List (OCall H)) (ν : Nat → OCall H) :
    (fun i => ((l ++ω ν) i).lift) = (l.map OCall.lift) ++ω (fun i => (ν i).lift) := by
  funext i
  by_cases hi : i < l.length
  · rw [Shape.streamAppend_lt hi, Shape.streamAppend_lt (by simpa using hi), List.getElem_map]
  · rw [Shape.streamAppend_ge (by omega), Shape.streamAppend_ge (by simp; omega),
      List.length_map]

/-! ## Lifting the conclusion -/

variable {tags : List TagInst} {host : HostSemantics H}

theorem infOut_lift {s s' : Store H} {f f' : Frame} {stk stk' : List Val} {es es' : List BExpr}
    {l₀ : List (OCall H)} {q₀ : List (Call (wasmHostSig H))} {ω : Nat → Call (wasmHostSig H)}
    (hd : ∀ ν, InfLXP s' f' stk' es' ν → InfLXP s f stk es (l₀ ++ω ν))
    (hr : ∀ l z, ReachLXP s' f' stk' es' l z → ReachLXP s f stk es (l₀ ++ l) z)
    (h₀ : Shape.SubstPre Cl (l₀.map OCall.lift) q₀)
    (hlink : q₀ = [] → ∃ W, Lifts o W ∧
      Relation.ReflTransGen (Det.DStep o) (pcfg s f stk es) (W (pcfg s' f' stk' es')))
    (h : InfOutX J tags o host s' f' stk' es' ω) : InfOutX J tags o host s f stk es (q₀ ++ω ω) := by
  rcases h with ⟨ν, hν, hs⟩ | ⟨l, z, q, K, ω', hry, hres, hq, rfl, hl⟩
  · refine .inl ⟨l₀ ++ω ν, hd ν hν, ?_⟩
    rw [lift_streamAppend]
    exact Shape.substInf_append h₀ hs
  · refine .inr ⟨l₀ ++ l, z, q₀ ++ q, K, ω', hr l z hry,
      by rw [List.map_append]; exact substPre_append' h₀ hres, hq,
      (Shape.streamAppend_append _ _ _).symm, fun hnil => ?_⟩
    obtain ⟨h1, h2⟩ := List.append_eq_nil_iff.mp hnil
    obtain ⟨W₁, hW₁, hr₁⟩ := hlink h1
    obtain ⟨W, hW, ht⟩ := hl h2
    exact ⟨fun c => W₁ (W c), hW₁.comp hW, hr₁.trans (hW₁.rtg ht)⟩

theorem infOut_lift₀ {s s' : Store H} {f f' : Frame} {stk stk' : List Val} {es es' : List BExpr}
    {ω : Nat → Call (wasmHostSig H)}
    (hd : ∀ ν, InfLXP s' f' stk' es' ν → InfLXP s f stk es ν)
    (hr : ∀ l z, ReachLXP s' f' stk' es' l z → ReachLXP s f stk es l z)
    (hlink : ∃ W, Lifts o W ∧
      Relation.ReflTransGen (Det.DStep o) (pcfg s f stk es) (W (pcfg s' f' stk' es')))
    (h : InfOutX J tags o host s' f' stk' es' ω) : InfOutX J tags o host s f stk es ω := by
  have := infOut_lift (l₀ := []) (q₀ := [])
    (fun ν h => by rw [Shape.streamAppend_nil]; exact hd ν h)
    (fun l z h => by simpa using hr l z h) .nil (fun _ => hlink) h
  rwa [Shape.streamAppend_nil] at this

/-- **From the head tree alone to the trees**: a host-free run from the head tree alone into a
context is one from the trees. -/
theorem link_cons {s : Store H} {f : Frame} {stk : List Val} {e : BExpr} {es : List BExpr}
    {K : Config H}
    (h : ∃ W, Lifts o W ∧ Relation.ReflTransGen (Det.DStep o) (pcfg s f stk [e]) (W K)) :
    ∃ W, Lifts o W ∧ Relation.ReflTransGen (Det.DStep o) (pcfg s f stk (e :: es)) (W K) := by
  obtain ⟨W, hW, hr⟩ := h
  refine ⟨fun c => (fun c : Config H => (⟨c.store, c.frame,
    c.code ++ expression (Binaryen.BExpr.lowerList es)⟩ : Config H)) (W c),
    (lifts_suffix _).comp hW, ?_⟩
  have h2 := (lifts_suffix (o := o) (expression (Binaryen.BExpr.lowerList es))).rtg hr
  have e : (pcfg s f stk (e :: es) : Config H) = ⟨s, f, xcode stk [e] ++
      expression (Binaryen.BExpr.lowerList es)⟩ := by simp
  rw [e]
  exact h2

/-- **A head tree with a resolved logged run does not run productively alone** after its log. -/
theorem head_contraI (hH : HostSliceT host) (hE : HostSliceE tags host)
    {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr} {l : List (OCall H)}
    {r : Store H × Frame × POut} {cs₁ : List (Call (wasmHostSig H))}
    {ω : Nat → Call (wasmHostSig H)}
    (ht : J.TypedP tags s f stk es) (hd : EvalLXPh s f stk es l r) (hres : ResW l cs₁)
    (hdv : CoreInf (profile o) host (pcfg s f stk es) (cs₁ ++ω ω)) : False := by
  obtain ⟨-, labels, ret, out, hS, hc, -, -, hts⟩ := ht
  have hcons : (coreHostRel host).Consistent cs₁ := fun c hc' => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc'
    have := coreInf_consistent hdv i
    rwa [Shape.streamAppend_lt hi] at this
  obtain ⟨s', f', c', oc, hrun, he⟩ :=
    evalLXPh_res_evRun (P := profile o) hH hE hd hres hcons hts hS hc
  exact noInf_of_evRun hrun (outcome_ends_stuck he s' f') hdv

/-- **A head tree run normally in front of the trees after it**, productively. -/
theorem head_consI {s s₂ : Store H} {f f₂ : Frame} {stk stk₂ : List Val} {e : BExpr}
    {l : List (OCall H)} (h : EvalLXPh s f stk [e] l (s₂, f₂, .flow (.normal stk₂)))
    (es : List BExpr) :
    ∀ ν, InfLXP s₂ f₂ stk₂ es ν → InfLXP s f stk (e :: es) (l ++ω ν) := by
  generalize hes : [e] = es₀ at h
  generalize hr : (s₂, f₂, POut.flow (.normal stk₂)) = r at h
  induction h generalizing e s₂ f₂ stk₂ with
  | argsAbort _ ho => cases hr; exact (ho trivial).elim
  | callRet hargs hfi hty hk =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hes
    cases hk; cases hr
    exact fun ν h => by simpa using InfLXP.callK hargs hfi hty h
  | opOk hi hargs hflat hk =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hes
    cases hk; cases hr
    exact fun ν h => by simpa using InfLXP.opK hi hargs hflat h
  | blockOk har hbody hvs hk =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hes
    cases hk; cases hr
    exact fun ν h => by simpa using InfLXP.blockK har hbody hvs h
  | blockEsc _ _ ho => cases hr; exact ho.elim
  | loopOk har hbody hk =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hes
    cases hk; cases hr
    exact fun ν h => by simpa using InfLXP.loopK har hbody h
  | loopBack har hbody hk _ ih₂ =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hes
    have hl := ih₂ rfl hr
    exact fun ν h => by
      rw [Shape.streamAppend_append]
      exact InfLXP.loopBack har hbody (hl ν h)
  | loopEsc _ _ ho => cases hr; exact ho.elim
  | ifOk hc hb har harm hvs hk =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hes
    cases hk; cases hr
    exact fun ν h => by simpa using InfLXP.ifK hc hb har harm hvs h
  | ifEsc _ _ _ _ ho => cases hr; exact ho.elim
  | ifAbort _ ho => cases hr; exact (ho trivial).elim
  | indRet hargs hres hfi hty hy hk =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hes
    cases hk; cases hr
    exact fun ν h => by simpa using InfLXP.indK hargs hres hfi hty hy h
  | refRet hargs hfi hty hy hk =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hes
    cases hk; cases hr
    exact fun ν h => by simpa using InfLXP.refK hargs hfi hty hy h
  | tryOk har hbody hvs hk =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hes
    cases hk; cases hr
    exact fun ν h => by simpa using InfLXP.tryK har hbody hvs h
  | tryEsc _ _ ho => cases hr; exact ho.elim
  | opStop _ _ _ hfl => cases hr; exact (hfl trivial).elim
  | nil => cases hes
  | _ => cases hr

end Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack
