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

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi
