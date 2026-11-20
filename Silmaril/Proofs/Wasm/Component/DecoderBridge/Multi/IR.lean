module

public import Silmaril.Wasm.Component.DecoderBridge.Multi.Defs
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp.Calls
public import Silmaril.Proofs.Wasm.Component.InstSem.WiredEngine
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.Compose

/-!
# The IR's node calls (piece (a))

* `RTN`: an IR configuration (host code `Nat`) is typed, with host functions of core type `fFlat`;
* `implsN_lowF`: the wiring `lowF` of an import call with one `i32` argument is one call of `f`
  on its `u32`, answered `()` with no results;
* `startRun_calls`: in a typed start run whose imports are lowerings of `f`, every import call
  has one `i32` argument, so each round of the wiring is one call of `f`, answered `()`;
* `nodeCalls_of_play`: a node's ready instantiation play with the calls `w`, each answered `()`,
  is `NodeCalls`;
* `nodeCallsIR`: **`Task.nodeCallsIR`**, node by node (`NodesInst`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Conformance Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Proofs.Wasm.Component.InstSem
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore
open Silmaril.Wasm.SingleThreaded (Internal status neverFail profile)
open Silmaril.Wasm.Execution.Core (Store StoreOk)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread

/-! ## Typed IR configurations -/

/-- An IR configuration is typed, with host functions of core type `fFlat`. -/
structure RTN (S : Store Nat) (t : STh) : Prop where
  store : StoreOk S
  thread : Silmaril.Wasm.SingleThreaded.ThreadOk S t []
  hosts : HostTy S

theorem args_of_calloutN {S : Store Nat} {t : STh} (hR : RTN S t) {h : Nat}
    {args : List Silmaril.Wasm.Execution.Core.Val} (hst : status neverFail S t = .callout h args) :
    ∃ b : BitVec 32, args = [.num ⟨.int .i32, b⟩] := by
  obtain ⟨fi, hfi, hcode, ps, rs, hexp, hargs⟩ :=
    Silmaril.Wasm.Component.Engine.Core3.Typed.callout_args_typed hR.store hR.thread hst
  have hty := hR.hosts fi hfi h hcode
  rw [hty] at hexp
  have he := Silmaril.Wasm.Execution.Core.Expand.func_eq hexp
    (Silmaril.Wasm.Component.Engine.Core3.Typed.expand_ofFlatType (Param.v1Type fFlat))
  injection he with he₁ he₂
  rw [he₁] at hargs
  simp only [Param.v1Type, fFlat, List.map_cons, List.map_nil,
    Silmaril.Wasm.Validation.Ty.toList_ofList] at hargs
  rcases hargs with _ | ⟨hv, hrest⟩
  cases hrest
  obtain ⟨b, rfl⟩ := Silmaril.Wasm.Execution.Core.ValOk.int_inv hv
  exact ⟨b, rfl⟩

theorem rtN_resume {S : Store Nat} {t : STh} (hR : RTN S t) {h : Nat}
    {args : List Silmaril.Wasm.Execution.Core.Val} (hst : status neverFail S t = .callout h args) :
    RTN S (Silmaril.Wasm.SingleThreaded.resume S t (.values [])) := by
  refine ⟨hR.store, ?_, hR.hosts⟩
  refine Silmaril.Wasm.SingleThreaded.resume_typed hR.store hR.thread hst hR.store
    (Silmaril.Wasm.Execution.Core.Extend.refl hR.store) ?_
  intro E a args' hd
  obtain ⟨fi, yy, ps, rs, hfi, hcode, -, he, -, -⟩ :=
    Silmaril.Wasm.SingleThreaded.decompose?_sound hd
  have hty := hR.hosts fi (List.mem_of_getElem? hfi) h hcode
  refine ⟨fi, _, _, hfi, by
    rw [hty]
    exact Silmaril.Wasm.Component.Engine.Core3.Typed.expand_ofFlatType (Param.v1Type fFlat), ?_⟩
  simp [Param.v1Type, fFlat]

theorem rtN_run {x y : Store Nat × STh} (h : Relation.ReflTransGen (Internal neverFail) x y)
    (hR : RTN x.1 x.2) : RTN y.1 y.2 := by
  obtain ⟨hs, ht⟩ := Silmaril.Wasm.SingleThreaded.reachable_typed h hR.store hR.thread
  have hf := funcs_steps h
  exact ⟨hs, ht, fun fi hfi => hR.hosts fi (by rw [← hf]; exact hfi)⟩

/-! ## The wiring of an import call -/

/-- **An import call with one `i32` argument, wired to `lowF`, is one call of `f`**, whose
answer `()` is answered with no results. -/
theorem implsN_lowF {w : List Impl} (hw : ∀ im ∈ w, im = lowF) {n : Nat} {h : Fin n}
    (hh : h.val < w.length) (b : BitVec 32) :
    ∃ k, implsN 1 w n (h, .flat [⟨.int .i32, b⟩]) = .call ((0, .vals [.u32 b]) : sigU.Op) k ∧
      k (some (.vals [])) = .pure (some (.flat [])) := by
  have hget : w[h.val]? = some lowF := by
    rw [List.getElem?_eq_getElem hh, hw _ (List.getElem_mem hh)]
  simp only [implsN, implsH, hget, Impl.prog, runChain, Adapter.down, liftArgs, ValTy.liftList,
    ValTy.lift, Option.map_some, Target.prog, Nat.zero_lt_one, ↓reduceIte]
  exact ⟨_, rfl, rfl⟩

/-! ## The calls of a start run -/

theorem internalP_eqN : @Engine.CoreEngine.Internal (core3P (profile neverFail)) Nat =
    Internal neverFail := internalP_profileR

/-- **The rounds of a typed start run with lowered imports**: each is one call of `f`. -/
theorem startRun_calls {imps : CoreIface} (himps : imps.all (·.2 == fFlat) = true)
    {w : List Impl} (hw : ∀ im ∈ w, im = lowF) (hwl : imps.length ≤ w.length) :
    ∀ {c c' : (core3P (profile neverFail)).Config Nat}
      {cs : List (Σ _ : (sigN imps.length).Op, Option Payload)},
      Param.StartRunI (core3P (profile neverFail)) imps c cs c' → RTN c.1 c.2 →
      ∀ {ys : List (Round sigU (sigN imps.length))}, cs = ys.map Round.call →
      (∀ y ∈ ys, Prog.Runs (implsN 1 w imps.length y.q) y.cs y.a) →
      (∀ x ∈ allCalls ys, x.2 = InstTests.unitV) →
      List.Forall₂ (fun y x => ∃ k, implsN 1 w imps.length y.1 = .call x.1 k ∧ k x.2 = .pure y.2)
        cs (allCalls ys) := by
  intro c c' cs hrun
  induction hrun with
  | nil run =>
    intro _ ys hys _ _
    cases ys with
    | nil => exact .nil
    | cons y ys => cases hys
  | @call s s₁ t t₁ h args c'' cs run callout hh r rest ih =>
    intro hR ys hys hruns hu
    cases ys with
    | nil => cases hys
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at hys
      obtain ⟨hy, hys⟩ := hys
      unfold Engine.CoreEngine.Steps at run
      rw [internalP_eqN] at run
      have hR₁ : RTN s₁ t₁ := rtN_run run hR
      obtain ⟨args', hst', hfl⟩ :=
        Silmaril.Wasm.Component.Engine.Core3.Typed.flatStatus_eq_callout' callout
      have hs₁ : status neverFail s₁ t₁ = .callout h args' :=
        (statusP_profile s₁ t₁).symm.trans hst'
      obtain ⟨b, rfl⟩ := args_of_calloutN hR₁ hs₁
      simp only [List.mapM_cons, List.mapM_nil, Silmaril.Wasm.SingleThreaded.toFlat?] at hfl
      cases hfl
      obtain ⟨yq, ycs, ya⟩ := y
      simp only [Round.call, Sigma.mk.injEq] at hy
      obtain ⟨rfl, hya⟩ := hy
      have hya' : r = ya := eq_of_heq hya
      subst hya'
      obtain ⟨k, hk, hk'⟩ := implsN_lowF hw (n := imps.length) (h := ⟨h, hh⟩) (by simp; omega) b
      have hrun₀ := hruns _ List.mem_cons_self
      simp only at hrun₀
      rw [hk] at hrun₀
      cases hrun₀ with
      | @call _ _ n' cs'' _ hrk =>
        have hn' : n' = InstTests.unitV := hu ⟨(0, .vals [.u32 b]), n'⟩ (by simp [allCalls])
        subst hn'
        simp only [InstTests.unitV] at hrk
        rw [hk'] at hrk
        cases hrk
        have himp : imps[h].2 = fFlat := by
          have := List.all_eq_true.mp himps _ (List.getElem_mem hh)
          simpa using this
        have eres : (core3P (profile neverFail)).resume s₁ t₁
            (Param.resultOf imps[h].2.results (some (.flat []))) =
            Silmaril.Wasm.SingleThreaded.resume s₁ t₁ (.values []) := by
          rw [himp, resultOf_fFlat]
          rfl
        have hR₂ : RTN s₁ ((core3P (profile neverFail)).resume s₁ t₁
            (Param.resultOf imps[h].2.results (some (.flat [])))) := by
          rw [eres]
          exact rtN_resume hR₁ hs₁
        have ih' := ih hR₂ hys (fun y hy => hruns y (List.mem_cons_of_mem _ hy))
          (fun x hx => hu x (by simp only [allCalls, List.cons_append, List.nil_append]; exact
            List.mem_cons_of_mem _ hx))
        simp only [allCalls, List.cons_append, List.nil_append]
        exact .cons ⟨k, hk, hk'⟩ ih'

/-! ## A node's instantiation play -/

/-- **A node's ready instantiation play with the calls `w`, each answered `()`, is
`NodeCalls`**, for a module whose imports have core type `fFlat`, each wired to `lowF`. -/
theorem nodeCalls_of_play {p : Binary.CoreMod × List Impl}
    (himps : (CoreModule.imports p.1).all (·.2 == fFlat) = true)
    (hwl : (CoreModule.imports p.1).length ≤ p.2.length) (hw : ∀ im ∈ p.2, im = lowF)
    (hnames : funcExportNames (Binary.coreModule p.1) = (CoreModule.exports p.1).map (·.1))
    {w : List (Σ _ : sigU.Op, Option Payload)} (hu : ∀ x ∈ w, x.2 = InstTests.unitV)
    (h : instPlay (F := sigU) w .ready ∈
      coreNodeI (Binary.coreModSemI (profile neverFail)) 1 p.1 p.2) :
    NodeCalls 1 .ready p.1 p.2 w := by
  rw [instPlay_eq] at h
  obtain ⟨ys, hm, hr, rfl⟩ := coreNodeI_inst_inv h
  have hEI := engine_inst_inv (E := core3P (profile neverFail))
    (I := Param.instOfI (core3P (profile neverFail)) (Binary.coreModule p.1)
      (CoreModule.imports p.1) (CoreModule.exports p.1)) (by rw [instPlay_eq]; exact hm)
  refine ⟨ys.map Round.call, hEI, ?_⟩
  obtain ⟨-, hsome⟩ := instOfI_cases himps hnames
  obtain ⟨J, hJ, ⟨-, hnil⟩ | ⟨f, c', fvs, hfs, hrun, -⟩⟩ := hEI
  · cases ys with
    | nil => exact .nil
    | cons y ys => cases hnil
  · obtain ⟨mi', hp⟩ := hsome J hJ
    rw [hfs] at hp
    have hA := hp
    obtain ⟨hs', -, ⟨new, hnew, hwasm⟩, hcfg⟩ :=
      Silmaril.Wasm.Component.Engine.Core3.Typed.prepareE?_typed
        (storeOk_irStore (CoreModule.imports p.1).length) hA
    have hR : RTN J.store (Silmaril.Wasm.SingleThreaded.Thread.invoke f []) := by
      refine ⟨hs', hcfg f rfl, fun fi hfi h hcode => ?_⟩
      rw [hnew] at hfi
      rcases List.mem_append.mp hfi with hfi | hfi
      · simp only [irStore, List.mem_map, List.mem_range] at hfi
        obtain ⟨i, -, rfl⟩ := hfi
        rfl
      · obtain ⟨c, hc⟩ := hwasm fi hfi
        rw [hc] at hcode
        cases hcode
    exact startRun_calls himps hw hwl hrun hR rfl hr hu

/-! ## The nodes, in order -/

/-- What the fragment says about each IR node. -/
structure NodeOk (p : Binary.CoreMod × List Impl) : Prop where
  imps : (CoreModule.imports p.1).all (·.2 == fFlat) = true
  wl : (CoreModule.imports p.1).length ≤ p.2.length
  wires : ∀ im ∈ p.2, im = lowF
  names : funcExportNames (Binary.coreModule p.1) = (CoreModule.exports p.1).map (·.1)

theorem isLowImpl_eq : ∀ {im : Impl}, isLowImpl im = true → im = lowF
  | ⟨[.lower ⟨[.u32], []⟩], .call 0⟩, _ => rfl

theorem nodeOk_of_nodeW {p : Binary.CoreMod × List Impl} {q : Silmaril.Wasm.Module × List Impl}
    (hW : NodeW (.core p.1 p.2) q)
    (hq : (irTypesOk q.1 && decide (q.1.imports.length ≤ q.2.length) &&
      q.2.all isLowImpl) = true) : NodeOk p := by
  obtain ⟨cm, he, hd, hci⟩ := hW
  injection he with he₁ he₂
  subst he₁
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hq
  obtain ⟨⟨hit, hl⟩, hlw⟩ := hq
  rw [← he₂] at hl hlw
  have hmod : Binary.coreModule p.1 = q.1 := by
    unfold Binary.coreModule
    rw [hd]
    rfl
  refine ⟨?_, ?_, fun im him => isLowImpl_eq (hlw im him), ?_⟩
  · unfold irTypesOk at hit
    rw [hci] at hit
    exact hit
  · rw [← coreIface_imports_length hci] at hl
    exact hl
  · rw [hmod, coreIface_exports hci]

theorem nodeOk_all : ∀ {ps : List (Binary.CoreMod × List Impl)}
    {qs : List (Silmaril.Wasm.Module × List Impl)},
    List.Forall₂ NodeW (coreNodes ps) qs →
    (qs.all fun q => irTypesOk q.1 && decide (q.1.imports.length ≤ q.2.length) &&
      q.2.all isLowImpl) = true →
    ∀ p ∈ ps, NodeOk p
  | [], _, _, _ => fun _ h => by cases h
  | p :: ps, q :: qs, .cons hW hF, hall => by
    simp only [List.all_cons, Bool.and_eq_true] at hall
    intro p' hp'
    rcases List.mem_cons.mp hp' with rfl | hp'
    · exact nodeOk_of_nodeW hW (by simpa [Bool.and_eq_true] using hall.1)
    · exact nodeOk_all hF hall.2 p' hp'

/-- In the fragment, every IR node satisfies `NodeOk`. -/
theorem nodeOk_frag {b : ByteArray} {c : Comp Binary.CoreMod} {r : RefComponent}
    {ps : List (Binary.CoreMod × List Impl)} (hc : Binary.parseComponent b = .ok c)
    (hr : decodeRef b = .ok r) (hf : MultiImpFrag r) (hn : c.nodes = coreNodes ps) :
    ∀ p ∈ ps, NodeOk p := by
  obtain ⟨-, hw, ⟨R, hR, hlw, -⟩, -⟩ := multiImpFrag_inv hf
  obtain ⟨R', hR', -, -, hN⟩ := relW_of_decode hc hr (inFrag_of_hostWired hw)
  rw [hR] at hR'
  cases hR'
  rw [hn] at hN
  exact nodeOk_all hN hlw

theorem forall₂_append {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} {x : α} {y : β}, List.Forall₂ R l₁ l₂ → R x y →
      List.Forall₂ R (l₁ ++ [x]) (l₂ ++ [y])
  | [], [], _, _, .nil, h => .cons h .nil
  | _ :: _, _ :: _, _, _, .cons h₁ h₂, h => .cons h₁ (forall₂_append h₂ h)

/-- **The node-by-node instantiation, as the nodes' `NodeCalls`.** -/
theorem nodesCalls :
    ∀ {ps : List (Binary.CoreMod × List Impl)} {t : List (Σ _ : sigU.Op, Option Payload)}
      {a : InstAns Unit},
      NodesInst (Binary.coreModSemI (profile neverFail)) 1 ps t a → a = .ready →
      (∀ p ∈ ps, NodeOk p) → (∀ x ∈ t, x.2 = InstTests.unitV) →
      ∃ ts : List (List (Σ _ : sigU.Op, Option Payload)), t = ts.flatten ∧
        List.Forall₂ (fun p tj => NodeCalls 1 .ready p.1 p.2 tj) ps ts := by
  intro ps t a h
  induction h with
  | nil => exact fun _ _ _ => ⟨[], rfl, .nil⟩
  | failed _ _ => exact fun h => by cases h
  | @step pre x w w' a h hx ih =>
    intro ha hok hu
    subst ha
    obtain ⟨ts, rfl, hF⟩ := ih rfl (fun p hp => hok p (List.mem_append_left _ hp))
      (fun y hy => hu y (List.mem_append_left _ hy))
    have hxo := hok x (List.mem_append_right _ List.mem_cons_self)
    refine ⟨ts ++ [w'], by simp, forall₂_append hF ?_⟩
    exact nodeCalls_of_play hxo.imps hxo.wl hxo.wires hxo.names
      (fun y hy => hu y (List.mem_append_right _ hy)) hx

/-- **Piece (a), the IR's node calls.** -/
theorem nodeCallsIR : Task.nodeCallsIR := by
  intro b c r ps t hc hr hf himp hn hu h
  exact nodesCalls h rfl (nodeOk_frag hc hr hf hn) hu

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi
