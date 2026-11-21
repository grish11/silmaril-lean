module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.Later
public import Silmaril.Proofs.Wasm.Component.Reference.InstExport

/-!
# The later definitions, and the instantiation from its pieces

* the symbolic reading (`refStep`): its nodes grow only at core instantiations, which the
  definitions before the first core instantiation do not contain (`firstCore?_noInst`);
* `FrameRel mods R sc`: the frame of the reference machine has the index spaces of the symbolic
  state `R` (types, all function types; component and core functions; core instances whose
  exports the reading wires are function exports of the instance, `CIRel`);
* `nonCore_step`: a definition after the first core instantiation other than a core
  instantiation runs silently (`tau` steps only), keeping `FrameRel` and `LaterInv`;
* `nodesRef_of`: `Task.nodesRef` from the first node (`FirstK'`) and a later core instantiation
  (`LaterCoreStep'`), by induction over the definitions after the first core instantiation, the
  IR's nodes consumed in order at the core instantiations, and the continuation finishing the
  instantiation (`KFin`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi

open Silmaril.Games Silmaril.Games.Inst
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp
open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Instantiate
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
  Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.Component.Reference.Core3Adder (first)
open Silmaril.Wasm.SingleThreaded (neverFail profile)

local notation "Σh" => Unit × List HLinked2.HostEvent

/-! ## The symbolic reading -/

/-- A core instantiation definition. -/
def IsInst {M : Type} : Syntax.Definition M → Prop
  | .coreInstance (.instantiate _ _) => True
  | _ => False

theorem firstCore?_noInst {M : Type} :
    ∀ (r : List (Syntax.Definition M)) {pre : List (Syntax.Definition M)} {mi : Nat}
      {cargs : List (String × Nat)} {post : List (Syntax.Definition M)},
      firstCore? r = some (pre, mi, cargs, post) → ∀ d ∈ pre, ¬ IsInst d
  | [], _, _, _, _, h => by cases h
  | d :: ds, pre, mi, cargs, post, h => by
    cases d with
    | coreInstance ci =>
      cases ci with
      | instantiate mi' a =>
        simp only [firstCore?, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        intro d hd; cases hd
      | exports items =>
        simp only [firstCore?, Option.map_eq_some_iff] at h
        obtain ⟨q, hq, he⟩ := h
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, -⟩ := he
        intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact id
        · exact firstCore?_noInst ds hq d hd
    | _ =>
      simp only [firstCore?, Option.map_eq_some_iff] at h
      obtain ⟨q, hq, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, -⟩ := he
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact id
      · exact firstCore?_noInst ds hq d hd

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem refStep_nodes {R R' : RSt} {d : Syntax.Definition Silmaril.Wasm.Module}
    (h : refStep R d = some R') : ∃ Y, R'.nodes = R.nodes ++ Y ∧ (¬ IsInst d → Y = []) := by
  unfold refStep at h
  split at h <;>
    (try simp only [Option.bind_eq_some_iff, Option.some.injEq, bind] at h)
  all_goals first
    | (subst h; exact ⟨[], by simp, fun _ => rfl⟩)
    | (obtain ⟨_, _, _, _, _, _, rfl⟩ := h; exact ⟨_, rfl, fun h => (h trivial).elim⟩)
    | (obtain ⟨_, _, _, _, rfl⟩ := h; exact ⟨[], by simp, fun _ => rfl⟩)
    | (obtain ⟨_, _, rfl⟩ := h; exact ⟨[], by simp, fun _ => rfl⟩)
    | (obtain ⟨_, _, h⟩ := h; split at h <;> simp at h <;> (subst h; exact ⟨[], by simp, fun _ => rfl⟩))
    | cases h

theorem foldlM_refStep_nodes :
    ∀ {ds : List (Syntax.Definition Silmaril.Wasm.Module)} {R Rf : RSt},
      ds.foldlM refStep R = some Rf →
      ∃ Y, Rf.nodes = R.nodes ++ Y ∧ ((∀ d ∈ ds, ¬ IsInst d) → Y = [])
  | [], R, Rf, h => by
    simp only [List.foldlM_nil] at h
    cases h
    exact ⟨[], by simp, fun _ => rfl⟩
  | d :: ds, R, Rf, h => by
    simp only [List.foldlM_cons] at h
    cases hR : refStep R d with
    | none => rw [hR] at h; cases h
    | some R' =>
      rw [hR] at h
      obtain ⟨Y₁, h₁, h₁'⟩ := refStep_nodes hR
      obtain ⟨Y₂, h₂, h₂'⟩ := foldlM_refStep_nodes h
      refine ⟨Y₁ ++ Y₂, by rw [h₂, h₁, List.append_assoc], fun hn => ?_⟩
      rw [h₁' (hn d List.mem_cons_self), h₂' (fun d' hd' => hn d' (List.mem_cons_of_mem _ hd'))]
      rfl

/-! ## The frame and the symbolic state -/

/-- A core instance of the frame and the reading's: the function exports the reading wires are
function exports of the instance. -/
def CIRel (mods : List Silmaril.Wasm.Module) :
    RCI → List (String × Silmaril.Wasm.Execution.Core.ExternAddr) → Prop
  | .node _ exps, es => ∃ m ∈ mods, (∃ nm im, coreIface m = .ok (nm, im, exps)) ∧
      List.Forall₂ (fun (e : Silmaril.Wasm.Export) (x : String × Silmaril.Wasm.Execution.Core.ExternAddr) =>
        x.1 = e.name ∧ ∀ i, e.index = .func i → ∃ a : Nat, x.2 = .func a) m.exports es
  | .inline its, es => ∀ n, (its.lookup n).isSome →
      ∃ a : Nat, es.lookup n = some (Silmaril.Wasm.Execution.Core.ExternAddr.func a)

/-- **The frame has the index spaces of the symbolic state.** -/
structure FrameRel (mods : List Silmaril.Wasm.Module) (R : RSt) (sc : Scope (core3 neverFail)) :
    Prop where
  rmods : R.mods = mods
  types_len : sc.frame.types.length = R.types.length
  types_func : ∀ x ∈ sc.frame.types, ∃ t, x = .func t
  funcs_len : sc.frame.funcs.length = R.funcs.length
  cf_len : sc.frame.coreFuncs.length = R.coreFuncs.length
  ci : List.Forall₂ (CIRel mods) R.coreInsts
    (sc.frame.coreInstances : List (List (String × Silmaril.Wasm.Execution.Core.ExternAddr)))

theorem forall₂_get {α β : Type} {P : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ P l₁ l₂ → ∀ {i : Nat} {a : α}, l₁[i]? = some a →
      ∃ b, l₂[i]? = some b ∧ P a b
  | _, _, .nil, _, _, h => by cases h
  | _ :: _, _ :: _, .cons hp _, 0, _, h => by cases h; exact ⟨_, rfl, hp⟩
  | _ :: _, _ :: _, .cons _ hr, i + 1, _, h => forall₂_get hr h

theorem lookup_of_forall₂ {n : String} :
    ∀ {exps : List Silmaril.Wasm.Export} {es : List (String × Silmaril.Wasm.Execution.Core.ExternAddr)},
      List.Forall₂ (fun (e : Silmaril.Wasm.Export) (x : String × Silmaril.Wasm.Execution.Core.ExternAddr) =>
        x.1 = e.name ∧ ∀ i, e.index = .func i → ∃ a : Nat, x.2 = .func a) exps es →
      (exps.map (·.name)).Nodup → ∀ e ∈ exps, e.name = n → ∀ i, e.index = .func i →
      ∃ a : Nat, es.lookup n = some (Silmaril.Wasm.Execution.Core.ExternAddr.func a)
  | _, _, .nil, _, _, h, _, _, _ => by cases h
  | e' :: exps, x :: es, .cons ⟨hx1, hx2⟩ hr, hnd, e, he, hn, i, hi => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp he with rfl | he
    · obtain ⟨a, ha⟩ := hx2 i hi
      refine ⟨a, ?_⟩
      obtain ⟨x1, x2⟩ := x
      simp only at hx1 ha
      subst hx1 hn ha
      simp [List.lookup]
    · have hne : e'.name ≠ n := fun h => hnd.1 (by rw [h, ← hn]; exact List.mem_map_of_mem he)
      obtain ⟨a, ha⟩ := lookup_of_forall₂ hr hnd.2 e he hn i hi
      refine ⟨a, ?_⟩
      obtain ⟨x1, x2⟩ := x
      simp only at hx1
      subst hx1
      have : (n == e'.name) = false := by simpa using fun h => hne h.symm
      simp [List.lookup, this, ha]

theorem cirel_lookup {mods : List Silmaril.Wasm.Module}
    (hnd : mods.all (fun m => (m.exports.map (·.name)).Nodup) = true) {ci : RCI}
    {es : List (String × Silmaril.Wasm.Execution.Core.ExternAddr)} (h : CIRel mods ci es)
    {n : String} {im : Impl} (hi : rciImpl ci n = some im) :
    ∃ a : Nat, es.lookup n = some (Silmaril.Wasm.Execution.Core.ExternAddr.func a) := by
  cases ci with
  | inline its => exact h n (by simp [rciImpl] at hi; simp [hi])
  | node base exps =>
    obtain ⟨m, hm, ⟨nm, ims, hci⟩, hF⟩ := h
    simp only [rciImpl, Option.map_eq_some_iff] at hi
    obtain ⟨j, hj, -⟩ := hi
    obtain ⟨hlt, hj', -⟩ := List.findIdx?_eq_some_iff_getElem.mp hj
    have hmem : n ∈ exps.map (·.1) :=
      List.mem_map.mpr ⟨exps[j], List.getElem_mem _, by simpa using hj'⟩
    rw [FirstCore.coreIface_exports hci] at hmem
    simp only [funcExportNames, List.mem_filterMap] at hmem
    obtain ⟨e, he, hfe⟩ := hmem
    split at hfe
    · rename_i i hix
      cases hfe
      exact lookup_of_forall₂ hF (by simpa using List.all_eq_true.mp hnd m hm) e he rfl i hix
    · cases hfe

/-! ## Silent runs -/

theorem sruns_tau {E : CoreEngine} {σ : Type} {dispatch : Call E → P E σ (Ret E)} {α : Type}
    {p : P E σ α} {m m' : Machine.Config E σ} {os : List HostObs} {a : α}
    (h : SRuns p m os a m') (th : Option ThreadId) :
    os = [] → ∃ tr, RunsQ dispatch th p m tr a m' ∧ ∀ l ∈ tr, l = .tau := by
  induction h with
  | pure a m => exact fun _ => ⟨[], .pure a m, fun _ h => nomatch h⟩
  | get _ ih =>
    intro he
    obtain ⟨tr, hr, hq⟩ := ih he
    exact ⟨_, .get hr, fun l hl => by
      rcases List.mem_cons.mp hl with rfl | hl
      · rfl
      · exact hq l hl⟩
  | modify hf _ ih =>
    intro he
    obtain ⟨tr, hr, hq⟩ := ih he
    exact ⟨_, .modify (hf _) hr, fun l hl => by
      rcases List.mem_cons.mp hl with rfl | hl
      · rfl
      · exact hq l hl⟩
  | emit _ _ => intro he; cases he

/-! ## The definitions other than core instantiations -/

theorem LaterInv.frame {pre : RefComponent} {sc sc' : Scope (core3 neverFail)}
    {M : Machine.Config (core3 neverFail) Σh} (h : LaterInv pre sc M)
    (hm : sc'.frame.coreModules = sc.frame.coreModules)
    (hi : sc'.frame.coreInstances = sc.frame.coreInstances) : LaterInv pre sc' M :=
  h.congr hm hi (fs := []) (by simp)

theorem getElem?_some_of_len {α β : Type} {l : List α} {l' : List β} (hl : l.length = l'.length)
    {i : Nat} {b : β} (h : l'[i]? = some b) : ∃ a, l[i]? = some a :=
  ⟨l[i]'(by rw [hl]; exact (List.getElem?_eq_some_iff.mp h).1), List.getElem?_eq_getElem _⟩

/-- **A definition after the first core instantiation other than a core instantiation runs
silently**, keeping the frame related to the symbolic state and the machine invariant. -/
theorem nonCore_step {pre : RefComponent} {R R' : RSt}
    {d : Syntax.Definition Silmaril.Wasm.Module} {sc : Scope (core3 neverFail)}
    {M : Machine.Config (core3 neverFail) Σh}
    (hpost : postDefOk (preLowers pre) (preInsts pre) (coreMods pre) d = true) (hni : ¬ IsInst d)
    (hR : refStep R d = some R') (hF : FrameRel (coreMods pre) R sc) (hL : LaterInv pre sc M) :
    ∃ sc' M', TRuns (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI) sc d) M sc' M' ∧
      FrameRel (coreMods pre) R' sc' ∧ LaterInv pre sc' M' ∧ M'.host = M.host := by
  cases d with
  | coreInstance ci =>
    cases ci with
    | instantiate => exact (hni trivial).elim
    | exports => simp [postDefOk] at hpost
  | type t =>
    cases t with
    | func ft =>
      have hft : funcTypePrim ft = true := by simpa [postDefOk] using hpost
      obtain ⟨ty, hty⟩ := resolveFuncType_prim sc.frame hft
      simp only [refStep, Option.bind_eq_some_iff, Option.some.injEq, bind] at hR
      obtain ⟨w, -, rfl⟩ := hR
      erw [instDef_funcTypeG sc hty]
      refine ⟨_, M, TRuns.pure _ M, ⟨hF.rmods, ?_, ?_, hF.funcs_len, hF.cf_len, hF.ci⟩,
        hL.frame rfl rfl, rfl⟩
      · simp [hF.types_len]
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hF.types_func x hx
        · simp at hx; exact ⟨_, hx⟩
    | _ => simp [postDefOk] at hpost
  | «alias» a =>
    cases a with
    | coreExport i n s =>
      cases s with
      | func =>
        have hnd : (coreMods pre).all (fun m => (m.exports.map (·.name)).Nodup) = true := by
          simpa [postDefOk] using hpost
        simp only [refStep, Option.bind_eq_some_iff, Option.some.injEq, bind] at hR
        obtain ⟨ci, hci, im, him, rfl⟩ := hR
        obtain ⟨es, hes, hrel⟩ := forall₂_get hF.ci hci
        obtain ⟨a, ha⟩ := cirel_lookup hnd hrel him
        erw [instDef_alias sc (es := es) hes ha rfl]
        refine ⟨_, M, TRuns.pure _ M, ⟨hF.rmods, hF.types_len, hF.types_func, hF.funcs_len,
          by rw [List.length_append, List.length_append, hF.cf_len]; rfl, hF.ci⟩,
          hL.frame rfl rfl, rfl⟩
      | _ => simp [postDefOk] at hpost
    | _ => simp [postDefOk] at hpost
  | canon c =>
    cases c with
    | lift f opts t =>
      have hopts : opts = [] := by
        cases opts with
        | nil => rfl
        | cons _ _ => simp [postDefOk] at hpost
      subst hopts
      simp only [refStep, Option.bind_eq_some_iff, Option.some.injEq, bind] at hR
      obtain ⟨im, him, ft, hft, rfl⟩ := hR
      obtain ⟨a, ha⟩ := getElem?_some_of_len hF.cf_len him
      obtain ⟨x, hx⟩ := getElem?_some_of_len hF.types_len hft
      obtain ⟨ty, rfl⟩ := hF.types_func x (List.mem_of_getElem? hx)
      erw [instDef_lift sc ha hx]
      refine ⟨_, _, (TRuns.allocObj ArenaField.funcs (fun _ _ => rfl) _ M).bind (TRuns.pure _ _),
        ⟨hF.rmods, hF.types_len, hF.types_func, by simp [hF.funcs_len], hF.cf_len, hF.ci⟩,
        hL.congr rfl rfl (fs := [_]) rfl, rfl⟩
    | _ => simp [postDefOk] at hpost
  | export_ nm si ty =>
    obtain ⟨srt, k⟩ := si
    cases srt with
    | func =>
      cases ty with
      | none =>
        simp only [refStep, Option.bind_eq_some_iff, Option.some.injEq, bind] at hR
        obtain ⟨⟨im, ft⟩, hk, rfl⟩ := hR
        obtain ⟨fid, hfid⟩ := getElem?_some_of_len hF.funcs_len hk
        erw [instDef_funcExport sc hfid]
        refine ⟨_, M, TRuns.pure _ M, ⟨hF.rmods, hF.types_len, hF.types_func,
          by simp [hF.funcs_len], hF.cf_len, hF.ci⟩, hL.frame rfl rfl, rfl⟩
      | some _ => simp [postDefOk] at hpost
    | _ => simp [postDefOk] at hpost
  | _ => simp [postDefOk] at hpost

/-! ## The pieces, strengthened -/

/-- **`LaterCoreStep`, with the component-level index spaces kept**: the core instantiation
pushes only its core instance (types and component functions unchanged). -/
def LaterCoreStep' : Prop :=
  ∀ (pre : RefComponent) (mi : Nat) (cargs : List (String × Nat)) (ds : RefComponent)
    (sc : Scope (core3 neverFail)) (M : Machine.Config (core3 neverFail) Σh)
    (m : Silmaril.Wasm.Module) (p : Binary.CoreMod × List Impl)
    (t : List (Σ _ : sigU.Op, Option Payload)) (L : List HLinked2.HostEvent)
    (K : Scope (core3 neverFail) → Canon.P (core3 neverFail) Σh (Ret (core3 neverFail))),
    (coreMods pre)[mi]? = some m →
    postDefOk (preLowers pre) (preInsts pre) (coreMods pre)
      (.coreInstance (.instantiate mi cargs)) = true →
    Binary.coreModule p.1 = m → (CoreModule.imports p.1).length = m.imports.length → NodeOk p →
    NodeCalls hostI.length .ready p.1 p.2 t →
    (∀ x ∈ t, x.2 = InstTests.unitV) →
    LaterInv pre sc M →
    M.ctl = [.ofProg none
      ((Syntax.Definition.coreInstance (.instantiate mi cargs) :: ds).foldlM
        (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc >>= K)] →
    M.host = ((), L) →
    ∃ (tr : List (Label (core3 neverFail) Σh)) (M' : Machine.Config (core3 neverFail) Σh)
      (sc' : Scope (core3 neverFail)) (es : List (String × (core3 neverFail).ExternVal)),
      LRun first.prof embL.hr (DG embL.host) M tr M' ∧
      (∀ ev, Label.host ev ∉ tr) ∧ (∀ msg, Label.trap msg ∉ tr) ∧
      M'.ctl = [.ofProg none
        (ds.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc' >>= K)] ∧
      LaterInv pre sc' M' ∧ M'.host = ((), L ++ logOfCalls t) ∧
      sc'.frame.coreModules = sc.frame.coreModules ∧
      sc'.frame.coreInstances = sc.frame.coreInstances ++ [es] ∧
      sc'.frame.coreFuncs = sc.frame.coreFuncs ∧ sc'.exports = sc.exports ∧
      List.Forall₂ (fun (e : Silmaril.Wasm.Export) (x : String × (core3 neverFail).ExternVal) =>
        x.1 = e.name ∧ ∀ i, e.index = .func i → ∃ a : Nat, x.2 = Silmaril.Wasm.Execution.Core.ExternAddr.func a)
        m.exports es ∧
      sc'.frame.types = sc.frame.types ∧ sc'.frame.funcs = sc.frame.funcs

/-- **`FirstK`, with the frame related to the symbolic reading** of the definitions up to and
including the first core instantiation. -/
def FirstKAt (fragment : RefComponent → Prop) : Prop :=
  ∀ (b : ByteArray) (c : Comp Binary.CoreMod) (r : RefComponent)
    (p : Binary.CoreMod × List Impl) (ps : List (Binary.CoreMod × List Impl))
    (t₀ : List (Σ _ : sigU.Op, Option Payload)) (pre : RefComponent) (mi : Nat)
    (cargs : List (String × Nat)) (post : RefComponent),
    Binary.parseComponent b = .ok c → decodeRef b = .ok r → fragment r →
    c.imports = hostI → c.nodes = coreNodes (p :: ps) → (∀ x ∈ t₀, x.2 = InstTests.unitV) →
    NodeCalls hostI.length .ready p.1 p.2 t₀ →
    firstCore? r = some (pre, mi, cargs, post) →
    ∃ sc M, RefAtDefsK r post sc (logOfCalls t₀) M ∧ LaterInv pre sc M ∧
      ∀ R₀, (pre ++ [Syntax.Definition.coreInstance (.instantiate mi cargs)]).foldlM refStep
          ({ env := (r.filter isFuncImport).length } : RSt) = some R₀ →
        FrameRel (coreMods pre) R₀ sc

def FirstK' : Prop := FirstKAt MultiImpFrag

/-! ## Core instantiations in the symbolic reading -/

theorem refStep_inst {R R' : RSt} {mi : Nat} {cargs : List (String × Nat)}
    (h : refStep R (.coreInstance (.instantiate mi cargs)) = some R') :
    ∃ m nm imps exps w, R.mods[mi]? = some m ∧ coreIface m = .ok (nm, imps, exps) ∧
      R'.nodes = R.nodes ++ [(m, w)] ∧ R'.coreInsts = R.coreInsts ++ [RCI.node R.env exps] ∧
      R'.mods = R.mods ∧ R'.types = R.types ∧ R'.funcs = R.funcs ∧
      R'.coreFuncs = R.coreFuncs := by
  simp only [refStep, Option.bind_eq_some_iff, Option.some.injEq, bind] at h
  obtain ⟨m, hm, ⟨nm, imps, exps⟩, hci, w, -, rfl⟩ := h
  refine ⟨m, nm, imps, exps, w, hm, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  cases hc : coreIface m with
  | error e => rw [hc] at hci; cases hci
  | ok v => rw [hc] at hci; cases hci; rfl

theorem frameRel_inst {pre : RefComponent} {R R' : RSt} {mi : Nat} {cargs : List (String × Nat)}
    {sc sc' : Scope (core3 neverFail)} {m : Silmaril.Wasm.Module}
    {es : List (String × (core3 neverFail).ExternVal)}
    (hF : FrameRel (coreMods pre) R sc) (hR : refStep R (.coreInstance (.instantiate mi cargs)) = some R')
    (hm : (coreMods pre)[mi]? = some m)
    (hci : sc'.frame.coreInstances = sc.frame.coreInstances ++ [es])
    (hcf : sc'.frame.coreFuncs = sc.frame.coreFuncs) (hty : sc'.frame.types = sc.frame.types)
    (hfn : sc'.frame.funcs = sc.frame.funcs)
    (hE : List.Forall₂ (fun (e : Silmaril.Wasm.Export) (x : String × (core3 neverFail).ExternVal) =>
        x.1 = e.name ∧ ∀ i, e.index = .func i →
          ∃ a : Nat, x.2 = Silmaril.Wasm.Execution.Core.ExternAddr.func a) m.exports es) :
    FrameRel (coreMods pre) R' sc' := by
  obtain ⟨m', nm, imps, exps, w, hm', hc, -, hR1, hR2, hR3, hR4, hR5⟩ := refStep_inst hR
  rw [hF.rmods, hm] at hm'
  cases hm'
  refine ⟨hR2.trans hF.rmods, by rw [hty, hR3]; exact hF.types_len, by rw [hty]; exact hF.types_func,
    by rw [hfn, hR4]; exact hF.funcs_len, by rw [hcf, hR5]; exact hF.cf_len, ?_⟩
  rw [hci, hR1]
  have hn : CIRel (coreMods pre) (.node R.env exps) es :=
    ⟨m, List.mem_of_getElem? hm, ⟨nm, imps, hc⟩, hE⟩
  exact List.rel_append hF.ci (.cons hn .nil)

/-! ## The later definitions -/

theorem ctl_cons {sc : Scope (core3 neverFail)} {d : Syntax.Definition Silmaril.Wasm.Module}
    {ds : RefComponent}
    {K : Scope (core3 neverFail) → Canon.P (core3 neverFail) Σh (Ret (core3 neverFail))} :
    ((d :: ds).foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc >>= K) =
      (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI) sc d >>= fun sc' =>
        ds.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc' >>= K) := by
  erw [List.foldlM_cons]
  simp only [bind_assoc]

theorem findSome_append_some {tr₁ tr₂ : List (Label (core3 neverFail) Σh)}
    (h : ∃ x, (traceObs tr₂).findSome? decodeInstantiated? = some x) :
    ∃ x, (traceObs (tr₁ ++ tr₂)).findSome? decodeInstantiated? = some x := by
  obtain ⟨x, hx⟩ := h
  simp only [traceObs, List.filterMap_append, List.findSome?_append] at hx ⊢
  cases (tr₁.filterMap Label.obs?).findSome? decodeInstantiated? with
  | none => exact ⟨x, by simpa using hx⟩
  | some y => exact ⟨y, rfl⟩

theorem traceObs_tau {tr : List (Label (core3 neverFail) Σh)} (h : ∀ l ∈ tr, l = .tau) :
    traceObs tr = [] := by
  induction tr with
  | nil => rfl
  | cons l tr ih =>
    rw [h l List.mem_cons_self]
    exact ih (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))

/-- **The later definitions, then the end of the instantiation.** -/
theorem later_run (h2 : LaterCoreStep') {pre : RefComponent} :
    ∀ (ds : RefComponent) (R Rf : RSt) (sc : Scope (core3 neverFail))
      (M : Machine.Config (core3 neverFail) Σh)
      (K : Scope (core3 neverFail) → Canon.P (core3 neverFail) Σh (Ret (core3 neverFail)))
      (L : List HLinked2.HostEvent) (ps : List (Binary.CoreMod × List Impl))
      (ts : List (List (Σ _ : sigU.Op, Option Payload))),
      ds.foldlM refStep R = some Rf →
      ds.all (postDefOk (preLowers pre) (preInsts pre) (coreMods pre)) = true →
      (∃ X, Rf.nodes = R.nodes ++ X ∧ List.Forall₂ NodeW (coreNodes ps) X) →
      (∀ p ∈ ps, NodeOk p) →
      List.Forall₂ (fun q tj => NodeCalls hostI.length .ready q.1 q.2 tj) ps ts →
      (∀ x ∈ ts.flatten, x.2 = InstTests.unitV) →
      FrameRel (coreMods pre) R sc → LaterInv pre sc M → KFin K →
      M.ctl = [.ofProg none
        (ds.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc >>= K)] →
      M.host = ((), L) →
      ∃ tr M', LRun first.prof embL.hr (DG embL.host) M tr M' ∧
        (∀ ev, Label.host ev ∉ tr) ∧ M'.ctl = [] ∧ M'.store.lockdown = false ∧
        M'.host = ((), L ++ logOfCalls ts.flatten) ∧
        ∃ x, (traceObs tr).findSome? decodeInstantiated? = some x
  | [], R, Rf, sc, M, K, L, ps, ts, hfold, _, hX, _, hNC, _, _, hL, hK, hc, hh => by
    simp only [List.foldlM_nil] at hfold
    cases hfold
    obtain ⟨X, hX, hW⟩ := hX
    have hX0 : X = [] := by simpa using hX.symm
    subst hX0
    have hps : ps = [] := by
      cases ps with
      | nil => rfl
      | cons _ _ => cases hW
    subst hps
    cases hNC
    have hc' : M.ctl = [.ofProg none (K sc)] := by rw [hc]; rfl
    obtain ⟨tr, M', hs, hn, hctl, hlock, hhost, -, hobs, -⟩ := hK sc M hL.lock hc'
    exact ⟨tr, M', hs, hn, hctl, hlock, by rw [hhost, hh]; simp [logOfCalls], _, hobs⟩
  | d :: ds, R, Rf, sc, M, K, L, ps, ts, hfold, hpost, hX, hok, hNC, hu, hF, hL, hK, hc, hh => by
    simp only [List.foldlM_cons] at hfold
    cases hR : refStep R d with
    | none => rw [hR] at hfold; cases hfold
    | some R₁ =>
    rw [hR] at hfold
    simp only [List.all_cons, Bool.and_eq_true] at hpost
    obtain ⟨hd, hpost⟩ := hpost
    obtain ⟨X, hX, hW⟩ := hX
    obtain ⟨Y, hY, -⟩ := foldlM_refStep_nodes hfold
    by_cases hi : IsInst d
    · -- a core instantiation
      obtain ⟨mi, cargs, rfl⟩ : ∃ mi cargs, d = .coreInstance (.instantiate mi cargs) := by
        cases d with
        | coreInstance ci => cases ci with
          | instantiate mi cargs => exact ⟨mi, cargs, rfl⟩
          | exports => exact hi.elim
        | _ => exact hi.elim
      obtain ⟨m, nm, imps, exps, w, hm, hci, hRn, -⟩ := refStep_inst hR
      have hm' : (coreMods pre)[mi]? = some m := by rw [← hF.rmods]; exact hm
      have hXY : X = (m, w) :: Y := by
        rw [hY, hRn] at hX
        simpa using hX.symm
      subst hXY
      obtain ⟨p, ps', rfl, hpW, hW'⟩ : ∃ p ps', ps = p :: ps' ∧ NodeW (.core p.1 p.2) (m, w) ∧
          List.Forall₂ NodeW (coreNodes ps') Y := by
        cases ps with
        | nil => cases hW
        | cons p ps' => cases hW with | cons h1 h2 => exact ⟨p, ps', rfl, h1, h2⟩
      obtain ⟨cm, he, hdec, hcif⟩ := hpW
      injection he with he₁ he₂
      subst he₁
      have hmod : Binary.coreModule p.1 = m := by
        unfold Binary.coreModule
        rw [hdec]
        rfl
      have hilen : (CoreModule.imports p.1).length = m.imports.length :=
        (FirstImp.coreIface_imports_length hcif).symm ▸ rfl
      obtain ⟨t, ts', rfl, ht, hNC'⟩ : ∃ t ts', ts = t :: ts' ∧
          NodeCalls hostI.length .ready p.1 p.2 t ∧
          List.Forall₂ (fun q tj => NodeCalls hostI.length .ready q.1 q.2 tj) ps' ts' := by
        cases hNC with | cons h1 h2 => exact ⟨_, _, rfl, h1, h2⟩
      simp only [List.flatten_cons, List.mem_append] at hu
      obtain ⟨tr₁, M₁, sc₁, es, d₁, hn₁, -, hc₁, hL₁, hh₁, -, hci₁, hcf₁, -, hE, hty₁, hfn₁⟩ :=
        h2 pre mi cargs ds sc M m p t L K hm' hd hmod hilen (hok p List.mem_cons_self) ht
          (fun x hx => hu x (.inl hx)) hL hc hh
      have hF₁ := frameRel_inst hF hR hm' hci₁ hcf₁ hty₁ hfn₁ hE
      obtain ⟨tr₂, M₂, d₂, hn₂, hctl, hlock, hhost, hobs⟩ :=
        later_run h2 ds _ Rf sc₁ M₁ K (L ++ logOfCalls t) ps' ts' hfold hpost ⟨Y, hY, hW'⟩
          (fun q hq => hok q (List.mem_cons_of_mem _ hq)) hNC' (fun x hx => hu x (.inr hx))
          hF₁ hL₁ hK hc₁ hh₁
      refine ⟨tr₁ ++ tr₂, M₂, d₁.trans d₂, ?_, hctl, hlock, ?_, ?_⟩
      · intro ev hev
        rcases List.mem_append.mp hev with h | h
        · exact hn₁ ev h
        · exact hn₂ ev h
      · rw [hhost, List.flatten_cons, logOfCalls_append, List.append_assoc]
      · exact findSome_append_some hobs
    · -- another definition
      obtain ⟨sc₁, M₁, hT, hF₁, hL₁, hh₁⟩ := nonCore_step hd hi hR hF hL
      obtain ⟨tr₁, hq, htau⟩ := sruns_tau (dispatch := DG embL.host) hT none rfl
      have d₁ := RunsQ.lrun_at (prof := first.prof) (hr := embL.hr) hq hL.lock
        (fun sc' => ds.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc' >>= K)
        (segs := []) (rest := []) (by rw [hc, ctl_cons]; rfl)
      obtain ⟨Y₁, hY₁, hY₁'⟩ := refStep_nodes hR
      have hY0 := hY₁' hi
      subst hY0
      obtain ⟨tr₂, M₂, d₂, hn₂, hctl, hlock, hhost, hobs⟩ :=
        later_run h2 ds R₁ Rf sc₁ { M₁ with ctl := _ } K L ps ts hfold hpost
          ⟨X, by rw [hX, hY₁, List.append_nil], hW⟩ hok hNC hu hF₁
          (hL₁.congr rfl rfl (fs := []) (by simp)) hK rfl (by rw [← hh, ← hh₁])
      refine ⟨tr₁ ++ tr₂, M₂, d₁.trans d₂, ?_, hctl, hlock, hhost, ?_⟩
      · intro ev hev
        rcases List.mem_append.mp hev with h | h
        · exact absurd (htau _ h) (by simp)
        · exact hn₂ ev h
      · rw [traceObs, List.filterMap_append]
        have := traceObs_tau htau
        simp only [traceObs] at this
        rw [this, List.nil_append]
        exact hobs

/-! ## The instantiation -/

theorem foldlM_option_append {α β : Type} (f : β → α → Option β) :
    ∀ (l₁ l₂ : List α) (b : β),
      (l₁ ++ l₂).foldlM f b = (l₁.foldlM f b).bind fun b' => l₂.foldlM f b'
  | [], l₂, b => rfl
  | a :: l₁, l₂, b => by
    simp only [List.cons_append, List.foldlM_cons]
    cases f b a with
    | none => rfl
    | some b' => exact foldlM_option_append f l₁ l₂ b'

/-- **The instantiation by unique steps**: `Task.nodesRef`, with the run from the instantiation
host event a live run of unique steps (`LRun` from `instCfg r`) to a configuration with the host
in control, observing the instance `inst` with the exports `es`. -/
def NodesRefL : Prop :=
  ∀ (b : ByteArray) (c : Comp Binary.CoreMod) (r : RefComponent)
    (ps : List (Binary.CoreMod × List Impl)) (ts : List (List (Σ _ : sigU.Op, Option Payload))),
    Binary.parseComponent b = .ok c → decodeRef b = .ok r → MultiImpFrag r →
    c.imports = hostI → c.nodes = coreNodes ps →
    (∀ x ∈ ts.flatten, x.2 = InstTests.unitV) →
    List.Forall₂ (fun q tj => NodeCalls hostI.length .ready q.1 q.2 tj) ps ts →
    ∃ tr M' inst es, LRun first.prof embL.hr (DG embL.host) (instCfg r) tr M' ∧
      (∀ ev, Label.host ev ∉ tr) ∧ M'.ctl = [] ∧ M'.store.lockdown = false ∧
      (traceObs tr).findSome? decodeInstantiated? = some (inst, es) ∧
      M'.host = ((), logOfCalls ts.flatten)

/-- **The instantiation by unique steps, from the first node and the later core
instantiations.** -/
theorem nodesRefL_of' (h1 : FirstK') (h2 : LaterCoreStep') : NodesRefL := by
  intro b c r ps ts hpc hr hf himp hnodes hu hNC
  obtain ⟨-, hw, -, pre, mi, cargs, post, hs, -, hpostOk⟩ := multiImpFrag_inv hf
  obtain ⟨p, ps', rfl⟩ := nodes_ne_nil hpc hr hf hnodes
  have hok := nodeOk_frag hpc hr hf hnodes
  cases hNC with
  | @cons _ t₀ _ ts' h₀ hNC' =>
  simp only [List.flatten_cons, List.mem_append] at hu
  obtain ⟨sc, M, ⟨⟨tr₀, hs₀, hn₀, -⟩, ⟨K, hK, hc⟩, -, hh⟩, hL, hFR⟩ :=
    h1 b c r p ps' t₀ pre mi cargs post hpc hr hf himp hnodes (fun x hx => hu x (.inl hx)) h₀ hs
  obtain ⟨R, hR, -, -, hN⟩ := relW_of_decode hpc hr (inFrag_of_hostWired hw)
  rw [hnodes] at hN
  have hrr := firstCore?_eq r hs
  unfold refRead at hR
  have hsplit : r = (pre ++ [Syntax.Definition.coreInstance (.instantiate mi cargs)]) ++ post := by
    rw [hrr]; simp
  rw [hsplit, foldlM_option_append] at hR
  cases hR₀ : (pre ++ [Syntax.Definition.coreInstance (.instantiate mi cargs)]).foldlM refStep
      ({ env := (r.filter isFuncImport).length } : RSt) with
  | none =>
    rw [← hsplit, hR₀] at hR
    cases hR
  | some R₀ =>
  rw [← hsplit, hR₀] at hR
  simp only [Option.bind_some] at hR
  -- the nodes of the reading before `post`: the first core instantiation's
  rw [foldlM_option_append] at hR₀
  cases hR₁ : pre.foldlM refStep ({ env := (r.filter isFuncImport).length } : RSt) with
  | none => rw [hR₁] at hR₀; cases hR₀
  | some R₁ =>
  rw [hR₁] at hR₀
  simp only [Option.bind_some, List.foldlM_cons, List.foldlM_nil] at hR₀
  obtain ⟨Y₁, hY₁, hY₁'⟩ := foldlM_refStep_nodes hR₁
  have hY₁0 := hY₁' (firstCore?_noInst r hs)
  subst hY₁0
  cases hci : refStep R₁ (.coreInstance (.instantiate mi cargs)) with
  | none => rw [hci] at hR₀; cases hR₀
  | some R₂ =>
  rw [hci] at hR₀
  have hR₀' : R₂ = R₀ := by simpa using hR₀
  subst hR₀'
  obtain ⟨m0, -, -, -, w0, -, -, hn2, -⟩ := refStep_inst hci
  obtain ⟨X, hX, -⟩ := foldlM_refStep_nodes hR
  rw [hX, hn2, hY₁] at hN
  simp only [List.append_nil] at hN
  have hN' : List.Forall₂ NodeW (coreNodes ps') X := by
    simp only [List.nil_append, List.singleton_append] at hN
    cases hN with | cons _ h => exact h
  obtain ⟨tr₁, M', d, hn₁, hctl, hlock, hhost, ⟨⟨inst, es⟩, hobs⟩⟩ :=
    later_run h2 post _ R sc M K (logOfCalls t₀) ps' ts' hR hpostOk ⟨X, hX, hN'⟩
      (fun q hq => hok q (List.mem_cons_of_mem _ hq)) hNC' (fun x hx => hu x (.inr hx))
      (hFR _ (by rw [foldlM_option_append, hR₁]; simp [hci])) hL hK hc hh
  obtain ⟨y, hy⟩ := findSome_append_some (tr₁ := tr₀) ⟨_, hobs⟩
  refine ⟨tr₀ ++ tr₁, M', y.1, y.2, hs₀.trans d, ?_, hctl, hlock, hy, ?_⟩
  · intro ev hev
    rcases List.mem_append.mp hev with h | h
    · exact hn₀ ev h
    · exact hn₁ ev h
  · rw [hhost, List.flatten_cons, logOfCalls_append]

/-- **The instantiation, from the first node and the later core instantiations.** -/
theorem nodesRef_of' (h1 : FirstK') (h2 : LaterCoreStep') : Task.nodesRef := by
  intro b c r ps ts hpc hr hf himp hnodes hu hNC
  obtain ⟨tr, M', inst, es, d, hn, hctl, hlock, hobs, hhost⟩ :=
    nodesRefL_of' h1 h2 b c r ps ts hpc hr hf himp hnodes hu hNC
  have hready : HostReadyCfg hostConfigX := ⟨rfl, rfl, rfl⟩
  exact ⟨M', inst, es, ⟨tr, .cons (.hostRun hready) d.steps, hn, hctl, hlock, hobs⟩, hhost⟩

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi
