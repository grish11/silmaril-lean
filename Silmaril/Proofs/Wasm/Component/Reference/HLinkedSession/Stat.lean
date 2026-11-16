module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd.Round
public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.Inst

/-!
# Forward runs of a call of `HLinked2.toRef`: the invariant over the host-first layout

The `Linked2` forward machinery (`LinkedSessionFwd`) keeps `LInv`/`LReady`/`ReadyL` along a
call. These depend on the linked component only through the renaming `gL P l` of the shared
store's host code (a trampoline to its import index). For an `HLinked2`, the importer's
trampoline of import `n` lowers `l.fid n`: the exporter's lifted function `k + wire[n]` for a
wired import, host function `n - wire.length` for a host import (`k = host.length`). Here:

* `toW l`: the `Linked2` wiring *every* import of the importer, import `n` to `l.fid n`
  (`toW_wireFid`). It is only used through its renaming `gL P l.toW` (`gL_fid`), so the
  invariants of the `HLinked2` call are `LInv P l.toW`, `LReady P l.toW`, `ReadyL P l.toW`;
* `HStat`: the static facts (`LStat` with the host-first layout): the trampolines of the shared
  functions lower `l.fid k`, the frame's function `l.fid k` of a wired import is the exporter's
  lifted export `wire[k]`, and the frame's function `i < k` is host function `i`;
* `hstat_init`, `readyH_init`: both hold at the configuration after `HLinked2.instantiates`
  (`afterLinkH`), from the stores of the two core instances (**item 1**);
* the forward lemmas at the `HLinked2` layout: `LInv.reach_fwdH` (runs of the importer's part),
  `LInv.callout_fwdH` (a callout of the part is a callout of the shared thread to the trampoline
  of `l.fid k`), `LInv.siteH` (a wired callout is a link site), `LInv.resume_fwdH` (a returned
  nested call of the exporter).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower Payload sigN FuncTy)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel Rel4 Grow Touch)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread

/-! ## Every import wired -/

/-- **Every import of the importer wired to a component function**, as a `Linked2`: import
`n < wire.length` to `k + wire[n]`, import `wire.length + i` to host function `i`
(`k = host.length`). Only its renaming of trampolines `gL P l.toW` is used. -/
def _root_.Silmaril.Wasm.Component.Reference.HLinked2.toW (l : HLinked2) : Linked2 :=
  ⟨l.exp, l.imp, l.wire.map (l.host.length + ·) ++ List.range l.host.length⟩

theorem toW_nodup {l : HLinked2} (hn : l.toL2.WireNodup) : l.toW.WireNodup := by
  unfold Linked2.WireNodup HLinked2.toW
  refine List.nodup_append.2 ⟨List.Nodup.map (fun a b h => by simpa using h) hn,
    List.nodup_range, ?_⟩
  intro a ha b hb hab
  simp only [List.mem_map, List.mem_range] at ha hb
  obtain ⟨c, -, rfl⟩ := ha
  omega

theorem toW_length {l : HLinked2} (hW : l.WireTy) :
    l.toW.wire.length = l.imp.imports.length := by
  simp [HLinked2.toW, imports_length hW]

theorem toW_get {l : HLinked2} (hW : l.WireTy) {n : Nat} (hn : n < l.imp.imports.length) :
    l.toW.wire[n]? = some (l.fid n).idx := by
  have hlen := imports_length hW
  simp only [HLinked2.toW, HLinked2.fid]
  split_ifs with h
  · rw [List.getElem?_append_left (by simpa using h)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_map]
    rw [List.getElem?_range (by omega)]

/-- **The wiring of `toW` is `l.fid`.** -/
theorem toW_wireFid {l : HLinked2} (hW : l.WireTy) {n : Nat} (hn : n < l.imp.imports.length) :
    l.toW.wireFid n = l.fid n := by
  unfold Linked2.wireFid
  rw [List.getD_eq_getElem?_getD, toW_get hW hn]
  rfl

/-- **The renaming `gL P l.toW` recovers the import index of a trampoline of `l.fid`.** -/
theorem gL_fid {P : Profile} {l : HLinked2} (hW : l.WireTy) (hn : l.toL2.WireNodup) {n : Nat}
    (h : n < l.imp.imports.length) (ft : WIT.FuncType Empty RtId) (o : CanonOpts (E3 P))
    (inst : InstId) : gL P l.toW (.lowered (l.fid n) ft o inst) = n := by
  rw [← toW_wireFid hW h]
  exact trampIdxL_wireFid (toW_nodup hn) (by rw [toW_length hW]; exact h) ft o inst

theorem gLInv_fid {P : Profile} {l : HLinked2} (hW : l.WireTy) {n : Nat} {nm : String}
    {p : FuncTy} (hk : l.imp.imports[n]? = some (nm, p)) :
    gLInv P l.toW n = .lowered (l.fid n) (witFt p) {} ⟨2⟩ := by
  have hn : n < l.imp.imports.length := (List.getElem?_eq_some_iff.mp hk).1
  unfold gLInv
  rw [show l.toW.imp = l.imp from rfl, hk]
  simp only
  rw [toW_wireFid hW hn]

/-! ## The static facts -/

variable {P : Profile} {σ : Type}

/-- **The static facts of a call of an `HLinked2`** (`LStat` over the host-first layout): the
components and instances, the wiring, the arities and float-freedom of the imports, the
trampolines of the shared functions `F₀` (to `l.fid k`), the exporter's lifted exports and the
host functions in the frame `B`, the exporter's export functions owned by its part. -/
structure HStat (P : Profile) (l : HLinked2) (Ie Ii : Silmaril.Wasm.Game.ScalarInstance)
    (u₀ : Store Nat) (F₀ : List (FuncInst (CanonHost (E3 P)))) (B : Machine.Config (E3 P) σ)
    (Op₀ : Own) : Prop where
  expGood : l.exp.Good
  expInst : l.exp.mod.IsInst Ie
  impGood : l.imp.Good
  impInst : l.imp.mod.IsInst Ii
  impWf : Ii.WellFormed u₀
  wireTy : l.WireTy
  nodup : l.toL2.WireNodup
  arity : l.imp.Arity
  floats : l.imp.FloatFree
  tramp : ∀ (A : Nat) (fi : FuncInst (CanonHost (E3 P))) (h : CanonHost (E3 P)),
    F₀[A]? = some fi → fi.code = .host h →
    ∃ k nm p, h = .lowered (l.fid k) (witFt p) {} ⟨2⟩ ∧ l.imp.imports[k]? = some (nm, p)
  lifted : ∀ k w (xe : SimpleExport), l.wire[k]? = some w → l.exp.exports[w]? = some xe →
    ArenaField.funcs.get? B.store (l.fid k) =
      some (.lifted (Ie.addrs.getD xe.core 0) (witFt xe.ty) {} ⟨1⟩)
  hostFn : ∀ (i : Nat) (hi : i < l.host.length),
    ArenaField.funcs.get? B.store ⟨i⟩ = some (.host (witFt l.host[i].2) ⟨i⟩)
  owned : ∀ xe ∈ l.exp.exports, Op₀.fn (Ie.addrs.getD xe.core 0)

section Stat

variable {l : HLinked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {u₀ s₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {B : Machine.Config (E3 P) σ} {Op₀ Oc₀ : Own}
  {f : Ii.F.Op}

/-- The static facts at another importer store and another frame with the same functions. -/
theorem HStat.move {u : Store Nat} {B' : Machine.Config (E3 P) σ}
    (S : HStat P l Ie Ii u₀ F₀ B Op₀) (hw : Ii.WellFormed u) (hB : B'.store.funcs = B.store.funcs) :
    HStat P l Ie Ii u F₀ B' Op₀ :=
  { S with
    impWf := hw
    lifted := fun k w xe hw' hxe => by
      have e : ArenaField.funcs.get? B'.store (l.fid k) =
          ArenaField.funcs.get? B.store (l.fid k) := by
        simp only [ArenaField.get?, ArenaField.funcs, hB]
      rw [e]
      exact S.lifted k w xe hw' hxe
    hostFn := fun i hi => by
      have e : ArenaField.funcs.get? B'.store (⟨i⟩ : FuncId) =
          ArenaField.funcs.get? B.store ⟨i⟩ := by
        simp only [ArenaField.get?, ArenaField.funcs, hB]
      rw [e]
      exact S.hostFn i hi }

/-- The shared store of a call has only trampolines of `l.fid` as host code. -/
theorem hostsSat_hstat (S : HStat P l Ie Ii u₀ F₀ B Op₀) {s : Store (CanonHost (E3 P))}
    (hs : s.funcs = F₀) : HostsSat (fun h => gLInv P l.toW (gL P l.toW h) = h) s := by
  intro A fi h hA hc
  obtain ⟨k, nm, p, rfl, hk⟩ := S.tramp A fi h (hs ▸ hA) hc
  have hk' : k < l.imp.imports.length := (List.getElem?_eq_some_iff.mp hk).1
  show gLInv P l.toW (gL P l.toW (.lowered (l.fid k) (witFt p) {} ⟨2⟩)) = _
  rw [gL_fid S.wireTy S.nodup hk', gLInv_fid S.wireTy hk]

/-- The typed values answer of the import question `e` of `Ii` from the lowering of results
`us` of the import's type. -/
theorem resAnswerH (S : HStat P l Ie Ii u₀ F₀ B Op₀) {e : Ii.E.Op} {k : Nat} {nm : String}
    {p : FuncTy} (hk : l.imp.imports[k]? = some (nm, p)) (he : e.1.val = k)
    {us : List Silmaril.Wasm.Component.Val} (hus : ValTy.checkList p.results us = true) :
    List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal (Ii.imports.get e.1).results
      ((lowerArgs p.results us).map Silmaril.Wasm.SingleThreaded.ofFlat) := by
  obtain ⟨hk', hpk⟩ := List.getElem?_eq_some_iff.mp hk
  have hty : (lowerArgs p.results us).map (·.type) = ValTy.flatList p.results :=
    lowerList_types _ _ hus
  have heq : (Silmaril.Wasm.Component.Reference.fnOf l.imp.imports[k].2.flat).results =
      (lowerArgs p.results us).map (fun x => Silmaril.Wasm.Game.ScalarType.num x.type) := by
    rw [hpk]
    show (ValTy.flatList p.results).map _ = _
    rw [← hty, List.map_map]
    rfl
  rw [imports_get S.impGood S.impInst e k hk' he, heq]
  exact forall₂_hasVal_ofFlat _

/-- **A run of the importer's part is a core run of the shared thread** (`LInv.reach_fwd` at the
`HLinked2` layout). -/
theorem LInv.reach_fwdH (S : HStat P l Ie Ii u₀ F₀ B Op₀) {y : CoreSt (E3 P)}
    {x : Store Nat × STh} {π : Store Nat} (hI : LInv P l.toW Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y x π)
    {x' : Store Nat × STh} (hx : Silmaril.Wasm.Game.Reach P x x') :
    ∃ y', Relation.ReflTransGen (CoreStep (E3 P)) y y' ∧
      LInv P l.toW Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y' x' π := by
  obtain ⟨ρp, Op, ρc, Oc, hL, hR⟩ := hI.rel
  obtain ⟨y', ρc', Oc', hrun, hL', hgr, htc, hfy⟩ :=
    reach_link_fwd (gL P l.toW) (gLInv P l.toW) hx (hostsSat_hstat S hI.funcs) hL
  have hrc : PartRel ρc' Oc' (reloc s₀ x'.1) (Store.mapH (gL P l.toW) y'.1) := by
    have h := hL'.rel.rel
    rwa [Silmaril.Wasm.SingleThreaded.Thread.config_store] at h
  exact ⟨y', hrun, ⟨⟨ρp, Op, ρc', Oc', hL', Rel4.after_c hR hrc hgr htc⟩,
    hI.fnE.congr (mapH_funcs_eq _ hfy) rfl, hI.wf, hfy.trans hI.funcs,
    hI.run.trans (reach_ssteps hx)⟩⟩

/-- **A callout of the importer's part is a callout of the shared thread** to the trampoline of
`l.fid k`, on the flat arguments of the part's (`LInv.callout_fwd` at the `HLinked2` layout). -/
theorem LInv.callout_fwdH (S : HStat P l Ie Ii u₀ F₀ B Op₀) {y : CoreSt (E3 P)}
    {x : Store Nat × STh} {π : Store Nat} (hI : LInv P l.toW Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y x π)
    {k : Nat} {args : List Silmaril.Wasm.Execution.Core.Val}
    (hc : Silmaril.Wasm.Game.CalloutAt x.1 x.2 k args) {e : Ii.E.Op}
    (he : Ii.importOp? k args = some e) :
    ∃ (nm : String) (p : FuncTy) (ys : List Flat) (E : Silmaril.Wasm.SingleThreaded.Ctx)
      (a : Nat),
      l.imp.imports[k]? = some (nm, p) ∧
      Silmaril.Wasm.SingleThreaded.decompose? x.1 (x.2.config x.1).code = some (E, a, k, args) ∧
      args.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some ys ∧
      (E3 P).status y.1 y.2 = .callout (.lowered (l.fid k) (witFt p) {} ⟨2⟩) ys ∧
      ys.map (·.type) = ValTy.flatList p.params := by
  obtain ⟨E, a, hdx⟩ := hc
  obtain ⟨ρp, Op, ρc, Oc, hL, -⟩ := hI.rel
  have hdy := (decompose?_config_mapH (gL P l.toW) y.1 y.2).symm.trans (link_callout hL hdx)
  obtain ⟨⟨E', A, h, args'⟩, hd, hq⟩ := Option.map_eq_some_iff.mp hdy
  simp only [mapR, Prod.mk.injEq] at hq
  obtain ⟨-, -, hgh, hargs⟩ := hq
  obtain ⟨fi, -, -, -, hf, hcode, -⟩ := Silmaril.Wasm.SingleThreaded.decompose?_sound hd
  rw [hI.funcs] at hf
  obtain ⟨k', nm, p, rfl, hk⟩ := S.tramp A fi _ hf hcode
  have hk' : k' < l.imp.imports.length := (List.getElem?_eq_some_iff.mp hk).1
  have hkk : k' = k := by
    rw [← hgh]
    exact (gL_fid S.wireTy S.nodup hk' _ _ _).symm
  subst hkk
  have hek := ifaceOp?_some he
  have h2 : List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal (Ii.imports.get e.1).params args :=
    hek.2 ▸ e.2.2
  rw [imports_get S.impGood S.impInst e k' hk' hek.1, (List.getElem?_eq_some_iff.mp hk).2] at h2
  obtain ⟨ys, hys⟩ := Silmaril.Proofs.Wasm.Component.Core3G.toFlat?_isSome h2
  have hargs' : args' = args := by
    rw [hargs]
    exact map_val_of_flat _ hys
  subst hargs'
  refine ⟨nm, p, ys, E, a, hk, hdx, hys, ?_, flat_types_of_hasVal h2 hys⟩
  show flatStatus (Silmaril.Wasm.Game.statusP P y.1 y.2) = _
  rw [statusP_of_decomp hd]
  simp only [flatStatus, hys]

/-- **A wired callout of the shared thread is a link site.** -/
theorem LInv.siteH (S : HStat P l Ie Ii u₀ F₀ B Op₀) {y : CoreSt (E3 P)}
    {x : Store Nat × STh} {π : Store Nat} (hI : LInv P l.toW Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y x π)
    {k w : Nat} {nm : String} {xe : SimpleExport} {ys : List Flat}
    (hk : l.imp.imports[k]? = some (nm, xe.ty)) (hw : l.wire[k]? = some w)
    (hxe : l.exp.exports[w]? = some xe) (hys : ys.map (·.type) = ValTy.flatList xe.ty.params) :
    LinkSite B y (.lowered (l.fid k) (witFt xe.ty) {} ⟨2⟩) ys := by
  obtain ⟨ρp, Op, ρc, Oc, -, hR⟩ := hI.rel
  have hmem : xe ∈ l.exp.exports := List.mem_of_getElem? hxe
  have hmi : (nm, xe.ty) ∈ l.imp.imports := List.mem_of_getElem? hk
  obtain ⟨hmaxp, hmaxr, hres⟩ := S.arity.2 _ hmi
  obtain ⟨hpf, hrf⟩ := S.floats.2 _ hmi
  exact linkSite_exp (S.lifted k w xe hw hxe) hpf hys hmaxp hres hrf hmaxr S.expInst
    (S.expGood.core xe hmem) hI.wf (gL P l.toW) hR hI.fnE (S.owned xe hmem)

/-- **A returned nested call of the specification, forward** (`LInv.resume_fwd` at the
`HLinked2` layout). -/
theorem LInv.resume_fwdH (S : HStat P l Ie Ii u₀ F₀ B Op₀) {y : CoreSt (E3 P)}
    {x : Store Nat × STh} {π : Store Nat} (hI : LInv P l.toW Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y x π)
    {k : Nat} {nm : String} {w : Nat} {xe : SimpleExport} {E : Silmaril.Wasm.SingleThreaded.Ctx}
    {a : Nat} {args : List Silmaril.Wasm.Execution.Core.Val} {e : Ii.E.Op}
    (hk : l.imp.imports[k]? = some (nm, xe.ty)) (hxe : l.exp.exports[w]? = some xe)
    (hdx : Silmaril.Wasm.SingleThreaded.decompose? x.1 (x.2.config x.1).code = some (E, a, k, args))
    (he : Ii.importOp? k args = some e) {ws us : List Silmaril.Wasm.Component.Val}
    {π' : Store Nat} (hRet : RetAt P l.exp Ie xe ws π us π') :
    ∃ (ev : CoreSt (E3 P)) (zs : List Flat),
      Relation.ReflTransGen (CoreStep (E3 P))
        (y.1, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (Ie.addrs.getD xe.core 0)
          (lowerArgs xe.ty.params ws)) ev ∧
      (E3 P).status ev.1 ev.2 = .returned (.values zs) ∧ liftArgs xe.ty.results zs = some us ∧
      LInv P l.toW Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f
        (ev.1, (E3 P).resume ev.1 y.2 (.values (lowerArgs xe.ty.results us)))
        (x.1, Silmaril.Wasm.SingleThreaded.resumeResult x.1 x.2
          (.values ((lowerArgs xe.ty.results us).map Silmaril.Wasm.SingleThreaded.ofFlat))) π' := by
  obtain ⟨ρp, Op, ρc, Oc, hL, hR⟩ := hI.rel
  have hmem : xe ∈ l.exp.exports := List.mem_of_getElem? hxe
  obtain ⟨t', cvs, zs, run, final, hm, hus⟩ := hRet.run
  obtain ⟨ev, ρp', Op', hrun, hLe, hR', hF', hfe⟩ := exp_fwd (gL P l.toW) (gLInv P l.toW)
    (hostsSat_hstat S hI.funcs) hR hI.fnE (S.owned xe hmem) (lowerArgs xe.ty.params ws) run
  have hst := status_of_values (gL P l.toW) hLe final hm
  have hwf' : Ie.WellFormed π' := RetAt.wellFormed S.expInst (S.expGood.core xe hmem) hI.wf hRet
  have hfm : (Store.mapH (gL P l.toW) ev.1).funcs = (Store.mapH (gL P l.toW) y.1).funcs :=
    mapH_funcs_eq (gL P l.toW) hfe
  have hL1 : LinkSt s₀ ρc Oc x (Store.mapH (gL P l.toW) ev.1, y.2) :=
    linkSt_transport hL hfm hR'.rc
  have hL2 : LinkSt s₀ ρc Oc
      (x.1, Silmaril.Wasm.SingleThreaded.resumeResult x.1 x.2
        (.values ((lowerArgs xe.ty.results us).map Silmaril.Wasm.SingleThreaded.ofFlat)))
      (Store.mapH (gL P l.toW) ev.1, Silmaril.Wasm.SingleThreaded.resumeResult
        (Store.mapH (gL P l.toW) ev.1) y.2
        (.values ((lowerArgs xe.ty.results us).map Silmaril.Wasm.SingleThreaded.ofFlat))) :=
    link_resume hL1 hdx (ofFlat_scalar _)
  have hres : (E3 P).resume ev.1 y.2 (.values (lowerArgs xe.ty.results us)) =
      Silmaril.Wasm.SingleThreaded.resumeResult (Store.mapH (gL P l.toW) ev.1) y.2
        (.values ((lowerArgs xe.ty.results us).map Silmaril.Wasm.SingleThreaded.ofFlat)) :=
    (resume_values ev.1 y.2 _).trans (resumeResult_mapH (gL P l.toW) ev.1 y.2 _).symm
  have hcheck : ValTy.checkList xe.ty.results us = true :=
    Silmaril.Wasm.Component.checkList_of_liftArgs hus
  have hek : e.1.val = k ∧ e.2.1 = args := ifaceOp?_some he
  have hdx' : Silmaril.Wasm.SingleThreaded.decompose? (x.2.config x.1).store
      (x.2.config x.1).code = some (E, a, k, args) :=
    (Silmaril.Wasm.SingleThreaded.Thread.config_store x.1 x.2).symm ▸ hdx
  have hstep : Silmaril.Wasm.Game.SStep P (valEnv Ii) (x.2.config x.1, ())
      (⟨(x.2.config x.1).store, (x.2.config x.1).frame,
        E.fill (Silmaril.Wasm.Execution.Core.Result.values
          ((lowerArgs xe.ty.results us).map Silmaril.Wasm.SingleThreaded.ofFlat)).toAdmin⟩, ()) :=
    Silmaril.Wasm.Game.SStep.answer (P := P) (L := valEnv Ii) (q := ()) (q' := ())
      (w := .values ⟨_, resAnswerH S hk hek.1 hcheck⟩) hdx' he ⟨_, rfl⟩
  have hcfg := resumeResult_config hdx'
    (.values ((lowerArgs xe.ty.results us).map Silmaril.Wasm.SingleThreaded.ofFlat))
  refine ⟨ev, zs, hrun, hst, hus, ⟨⟨ρp', Op', ρc, Oc, hres ▸ hL2, hR'⟩, hF', hwf',
    hfe.trans hI.funcs, ?_⟩⟩
  show Silmaril.Wasm.Game.SSteps P (valEnv Ii) _ (Silmaril.Wasm.SingleThreaded.Thread.config x.1
    (Silmaril.Wasm.SingleThreaded.resumeResult x.1 x.2 _), ())
  rw [hcfg]
  exact hI.run.tail hstep

end Stat

/-! ## After instantiation -/

section Init

/-- **The shared core store after instantiation, renamed**: under `gL P l.toW` it is the
exporter instance's store followed by the importer instance's, relocated
(`linkStore_mapH` at the `HLinked2` layout). -/
theorem linkStoreH_mapH {l : HLinked2} (hn : l.toL2.WireNodup) (hw : l.WireTy)
    {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {cse : (E3 P).Store (CanonHost (E3 P))}
    {cie : (E3 P).Inst} (hFe : CoreFacts (Pf := P) l.exp Ie cse cie)
    {r : Store (CanonHost (E3 P) × Nat)} (hrs : Store.mapH Prod.snd r = Ii.store)
    (hh : HostsSat (fun h => ∃ (k : Nat) (hk : k < l.imp.imports.length),
      h = (.lowered (l.fid k) (witFt l.imp.imports[k].2) {} ⟨2⟩, k)) r) :
    Store.mapH (gL P l.toW) (reloc cse (Store.mapH Prod.fst r)) = reloc Ie.store Ii.store := by
  have hcse := hostsSat_cse hFe
  have he : Store.mapH (gL P l.toW) cse = Ie.store :=
    (mapH_congr_hosts hcse (g' := fun _ => 0) fun _ h => h.elim).trans hFe.store
  have hi : Store.mapH (gL P l.toW) (Store.mapH Prod.fst r) = Ii.store := by
    rw [mapH_mapH, ← hrs]
    refine mapH_congr_hosts hh ?_
    rintro _ ⟨k, hk, rfl⟩
    show gL P l.toW (.lowered (l.fid k) (witFt l.imp.imports[k].2) {} ⟨2⟩) = k
    exact gL_fid hw hn hk _ _ _
  have e := mapH_reloc (gL P l.toW) (cse : Store (CanonHost (E3 P))) (Store.mapH Prod.fst r)
  rw [he, hi] at e
  exact e

/-- **The host functions of the shared core store are the importer's trampolines of `l.fid`.** -/
theorem tramp_linkStoreH {l : HLinked2} {cs : Store (CanonHost (E3 P))}
    (hcse : HostsSat (fun _ => False) cs) {r : Store (CanonHost (E3 P) × Nat)}
    (hh : HostsSat (fun h => ∃ (k : Nat) (hk : k < l.imp.imports.length),
      h = (.lowered (l.fid k) (witFt l.imp.imports[k].2) {} ⟨2⟩, k)) r) :
    ∀ (A : Nat) (fi : FuncInst (CanonHost (E3 P))) (h : CanonHost (E3 P)),
      (reloc cs (Store.mapH Prod.fst r)).funcs[A]? = some fi →
      fi.code = .host h →
      ∃ k nm p, h = .lowered (l.fid k) (witFt p) {} ⟨2⟩ ∧ l.imp.imports[k]? = some (nm, p) := by
  intro A fi h hA hc
  rcases Nat.lt_or_ge A cs.funcs.length with hlt | hge
  · have h₁ : cs.funcs[A]? = some fi :=
      (List.getElem?_append_left (l₂ := (Store.mapH Prod.fst r).funcs.map (sh cs).finst)
        hlt).symm.trans hA
    exact (hcse A fi h h₁ hc).elim
  obtain ⟨fr, hfr, hfe⟩ := reloc_suffix_get hge hA
  have hcf : (FuncInst.mapH Prod.fst fr).code = .host h := by
    rw [← hc, ← hfe]
    rfl
  obtain ⟨hk, hcode, hh'⟩ := mapH_fst_host hcf
  obtain ⟨k, hkl, hke⟩ := hh _ fr hk hfr hcode
  have hkh : h = .lowered (l.fid k) (witFt l.imp.imports[k].2) {} ⟨2⟩ := by
    rw [← hh', hke]
  exact ⟨k, l.imp.imports[k].1, l.imp.imports[k].2, hkh, List.getElem?_eq_getElem hkl⟩

/-- The component functions after instantiation: the host functions of `l.host`, the
exporter's lifted functions, then the rest. -/
abbrev funcsH (l : HLinked2) (Ie : Silmaril.Wasm.Game.ScalarInstance)
    (rest : List (CFuncInst (E3 P))) : List (CFuncInst (E3 P)) :=
  hostList 0 l.host ++ liftedList (Pf := P) (fun k => Ie.addrs.getD k 0) ⟨1⟩ l.exp.exports ++ rest

/-- The lifted function of the exporter's export `w`, after the host functions. -/
theorem lifted_initH {l : HLinked2} {Ie : Silmaril.Wasm.Game.ScalarInstance}
    (rest : List (CFuncInst (E3 P))) {k w : Nat} {xe : SimpleExport}
    (hw : l.wire[k]? = some w) (hxe : l.exp.exports[w]? = some xe) :
    (funcsH (P := P) l Ie rest)[(l.fid k).idx]? =
      some (.lifted (Ie.addrs.getD xe.core 0) (witFt xe.ty) {} ⟨1⟩) := by
  have hwl : w < l.exp.exports.length := (List.getElem?_eq_some_iff.mp hxe).1
  have hkl : k < l.wire.length := (List.getElem?_eq_some_iff.mp hw).1
  have hidx : (l.fid k).idx = l.host.length + w := by
    simp only [HLinked2.fid, hkl, ↓reduceIte, List.getD_eq_getElem?_getD, hw, Option.getD_some]
  rw [hidx, List.getElem?_append_left (by simp [liftedList, hostList, hwl]),
    List.getElem?_append_right (by simp [hostList])]
  simp [liftedList, hostList, hxe, liftedFt, witFt]

/-- The host function `i`, at the front of the component functions. -/
theorem hostFn_initH {l : HLinked2} {Ie : Silmaril.Wasm.Game.ScalarInstance}
    (rest : List (CFuncInst (E3 P))) {i : Nat} (hi : i < l.host.length) :
    (funcsH (P := P) l Ie rest)[i]? = some (.host (witFt l.host[i].2) ⟨i⟩) := by
  unfold funcsH
  rw [List.append_assoc, List.getElem?_append_left (by simp [hostList, hi])]
  simp [hostList, hi]

/-- **The static facts of a call after instantiation**, with the frame's component functions
those of `afterLinkH`. -/
theorem hstat_init {l : HLinked2} (hEg : l.exp.Good) (hIg : l.imp.Good) (hW : l.WireTy)
    (hn : l.toL2.WireNodup) (har : l.imp.Arity) (hff : l.imp.FloatFree)
    {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {cse : (E3 P).Store (CanonHost (E3 P))}
    {cie : (E3 P).Inst} (hFe : CoreFacts (Pf := P) l.exp Ie cse cie) (hI : l.imp.mod.IsInst Ii)
    {r : Store (CanonHost (E3 P) × Nat)}
    (hh : HostsSat (fun h => ∃ (k : Nat) (hk : k < l.imp.imports.length),
      h = (.lowered (l.fid k) (witFt l.imp.imports[k].2) {} ⟨2⟩, k)) r)
    {B : Machine.Config (E3 P) σ} (rest : List (CFuncInst (E3 P)))
    (hB : B.store.funcs = funcsH l Ie rest) :
    HStat P l Ie Ii Ii.store (reloc (cse : Store (CanonHost (E3 P))) (Store.mapH Prod.fst r)).funcs
      B (ownOf Ie.store) where
  expGood := hEg
  expInst := hFe.isInst
  impGood := hIg
  impInst := hI
  impWf := hI.1.choose_spec.ok
  wireTy := hW
  nodup := hn
  arity := har
  floats := hff
  tramp := tramp_linkStoreH (hostsSat_cse hFe) hh
  lifted := fun k w xe hw hxe => by
    simp only [ArenaField.get?, ArenaField.funcs, hB, Arena.get?_eq_getElem?]
    exact lifted_initH rest hw hxe
  hostFn := fun i hi => by
    simp only [ArenaField.get?, ArenaField.funcs, hB, Arena.get?_eq_getElem?]
    exact hostFn_initH rest hi
  owned := owned_init hEg hFe.isInst

/-- The component functions of a linked component with host imports: the importer's export `j`
is the lift of its core export at the relocated address, after the host functions and the
exporter's lifted functions. -/
def LiftedOkH (l : HLinked2) (Ii : Silmaril.Wasm.Game.ScalarInstance) (s₀ : Store Nat)
    (fs : List (CFuncInst (core3P P))) : Prop :=
  ∀ j : Fin l.imp.exports.length, fs[l.host.length + l.exp.exports.length + j]? =
    some (.lifted (s₀.funcs.length + Ii.addrs.getD l.imp.exports[j].core 0)
      (liftedFt l.imp.exports[j]) {} ⟨2⟩)

theorem afterLinkH_lifted {l : HLinked2} (addrE addrI : Nat → Nat)
    (j : Fin l.imp.exports.length) :
    (hostList 0 l.host ++ liftedList (Pf := P) addrE ⟨1⟩ l.exp.exports ++
      liftedList addrI ⟨2⟩ l.imp.exports)[l.host.length + l.exp.exports.length + j]? =
      some (.lifted (addrI l.imp.exports[j].core) (liftedFt l.imp.exports[j]) {} ⟨2⟩) := by
  rw [List.getElem?_append_right (by simp [liftedList, hostList])]
  simp [liftedList, hostList]

/-- The component functions of `afterLinkH` lift the importer's exports at the relocated
addresses of its instance. -/
theorem liftedOkH_afterLink {l : HLinked2} {Ii : Silmaril.Wasm.Game.ScalarInstance}
    (hI : l.imp.mod.IsInst Ii) (hIg : l.imp.Good)
    {Ie : Silmaril.Wasm.Game.ScalarInstance} {cse : (E3 P).Store (CanonHost (E3 P))}
    {cie : (E3 P).Inst} (hFe : CoreFacts (Pf := P) l.exp Ie cse cie) :
    LiftedOkH l Ii Ie.store (hostList 0 l.host ++
      liftedList (Pf := P) (fun k => Ie.addrs.getD k 0) ⟨1⟩ l.exp.exports ++
      liftedList (addrL (cse : Store _).funcs.length Ii) ⟨2⟩ l.imp.exports) := by
  intro j
  obtain ⟨nm, hcore⟩ := hIg.core _ (List.getElem_mem j.isLt)
  have hk : l.imp.exports[j].core < l.imp.mod.exports.length :=
    (List.getElem?_eq_some_iff.mp hcore).1
  have hlen : l.imp.exports[j].core < Ii.addrs.length := by
    rw [hI.1.choose_spec.ok.addrs_length, hI.2.2, List.length_map]
    exact hk
  rw [afterLinkH_lifted, addrL_eq _ hlen, coreFacts_length (l := l.toL2) hFe]

/-- **The invariant between calls after instantiation** (`ReadyL` over the host-first layout,
at the renaming `gL P l.toW`): the shared core store renames to the exporter instance's store
followed by the importer instance's, both thread tables empty, no leftovers. -/
theorem readyH_init {l : HLinked2} (hS : l.toL2.SplitOk) (hn : l.toL2.WireNodup)
    (hW : l.WireTy) {Ie Ii : Silmaril.Wasm.Game.ScalarInstance}
    {cse : (E3 P).Store (CanonHost (E3 P))} {cie : (E3 P).Inst}
    (hFe : CoreFacts (Pf := P) l.exp Ie cse cie) (hIi : l.imp.mod.IsInst Ii)
    {r : Store (CanonHost (E3 P) × Nat)} (hrs : Store.mapH Prod.snd r = Ii.store)
    (hh : HostsSat (fun h => ∃ (k : Nat) (hk : k < l.imp.imports.length),
      h = (.lowered (l.fid k) (witFt l.imp.imports[k].2) {} ⟨2⟩, k)) r) :
    ReadyL P l.toW Ie Ii Ie.store Ii.store
      (reloc (cse : Store (CanonHost (E3 P))) (Store.mapH Prod.fst r)).funcs
      (reloc (cse : Store (CanonHost (E3 P))) (Store.mapH Prod.fst r)) {} {}
      (Garb.empty : Garb P σ) Ii.store Ie.store 0 := by
  have hg₀ : StoreGood Ie.store := storeGood_inst hS.exp hFe.isInst.1.choose_spec
  have hgu : StoreGood Ii.store := storeGood_inst hS.imp hIi.1.choose_spec
  exact { inv := lready_init hg₀ hgu (linkStoreH_mapH hn hW hFe hrs hh) rfl
            hFe.isInst.1.choose_spec.ok hIi.1.choose_spec.ok
          thE := threadsOk_empty
          thI := threadsOk_empty
          leave := rfl
          fresh := { pending := (fun _ h => nomatch h), results := (fun _ h => nomatch h) } }

end Init

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession
