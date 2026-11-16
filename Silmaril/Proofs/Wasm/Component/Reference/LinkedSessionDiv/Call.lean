module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDiv.Round

/-!
# Diverging linked calls: one call

From the importer's core activation at the shared thread `y` (in any frame `extN B ιe N C`),
`LInv` relating it to the importer's part at `(s, t)` and the exporter's store `π`, each source
of a specification divergence is a divergence of the machine:

* `divB_core` (**B diverges host-free**): B's infinite run is an infinite core run of the shared
  thread (`link_inf`), one machine step per core step (`coreCfg_diverges_of`);
* `divA_core` (**A diverges inside an import call**): B's run to the callout (`LInv.reach_fwd`,
  `LInv.callout_fwd`), the nested `canon lower`/`canon lift` into A (`nest_atTS`), and A's
  infinite run from its store `π` as an infinite core run of the nested activation (`link_inf`
  from `exp_invoke`);
* `chatter_core` (**chatter**): each served import call is a nonempty quiet machine run back to
  the importer's core activation (`roundsPre_fwd` on one call, `lseg_runN`), `LInv` holding at
  the next store of the exporter; these segments are concatenated by `diverges_of_segs`
  (productivity is their nonemptiness). A served call answered by a trap would doom the importer
  (`doomed_no_call`), contradicting the next call.

`linkDiv_fwd`: from a configuration between linked calls (`ReadyL` at the importer's store `u` and
the exporter's `π`), a round that never answers (`Linked2.RoundDiv`) is a diverging top-level
call: the host's invocation, the deterministic prefix (`call_atLKTS`), the round's prefix
(`roundsPre_fwd`, `lseg_run`) and one of the three. When the prefix dooms the importer, no
source applies (`not_divB_doomed`, `doomed_no_ask`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDiv

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower Payload sigN FuncTy)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}
  {l : Linked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {u₀ s₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {B : Machine.Config (E3 P) σ} {Op₀ Oc₀ : Own}
  {f : Ii.F.Op} {th : Option ThreadId} {K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))}
  {segs : List (Seg (E3 P) σ)} {rest : List (Activation (E3 P) σ)}

/-! ## The three sources at the importer's core activation -/

/-- **(i) B diverges host-free**: the machine diverges in B's core activation. -/
theorem divB_core (S : LStat P l Ie Ii u₀ F₀ B Op₀) {y : CoreSt (E3 P)} {s π : Store Nat}
    {t : STh} (hI : LInv P l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y (s, t) π) (hd : Linked2.DivB P s t)
    (ιe : InstState) (N : List (NRec P)) (C : List (Option (Activation (E3 P) σ))) :
    Diverges prof (fun _ _ => false) (DI P impl) (coreCfg (extN B ιe N C) th K segs rest y) := by
  obtain ⟨g, hg0, hg⟩ := hd
  obtain ⟨ρp, Op, ρc, Oc, hL, -⟩ := hI.rel
  exact SessionDiv.coreCfg_diverges_of
    (link_inf (gL P l) (gLInv P l) hg (hostsSat_lstat S hI.funcs) (hg0 ▸ hL))

/-- **(ii) A diverges inside an import call**: the machine diverges in the nested activation of
A's export. -/
theorem divA_core (S : LStat P l Ie Ii u₀ F₀ B Op₀) (hB : LFrame B th) {y : CoreSt (E3 P)}
    {s π : Store Nat} {t : STh} (hI : LInv P l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y (s, t) π)
    (hd : Linked2.DivA P l Ie Ii f s t π) {ιe : InstState} (hte : ThreadsOk ιe)
    (N : List (NRec P)) (C : List (Option (Activation (E3 P) σ))) :
    Diverges prof (fun _ _ => false) (DI P impl) (coreCfg (extN B ιe N C) th K segs rest y) := by
  obtain ⟨e, s', t', nm, ft, ws, w, hpath, himp, hlift, hwire, hdiv⟩ := hd
  obtain ⟨k, args, x₁, run, co, op⟩ : ∃ (k : Nat) (args : List Silmaril.Wasm.Execution.Core.Val)
      (x₁ : Store Nat × STh), Silmaril.Wasm.Game.Reach P (s, t) x₁ ∧
        Silmaril.Wasm.Game.CalloutAt x₁.1 x₁.2 k args ∧ Ii.importOp? k args = some e := by
    cases hpath with
    | cons h₁ _ =>
      cases h₁ with
      | ucall run co op => exact ⟨_, _, _, run, co, op⟩
  obtain ⟨y₁, hy₁, hI₁⟩ := LInv.reach_fwd S hI run
  obtain ⟨nm', p, wi, xe, ys, E, a, hk, hw, hxe, hpx, hdx, hys, hst, hyty⟩ :=
    LInv.callout_fwd S hI₁ co op
  have hek := ifaceOp?_some op
  have hft : ft = p := by
    rw [hek.1, hk] at himp
    simp only [Option.some.injEq, Prod.mk.injEq] at himp
    exact himp.2.symm
  subst hft
  have hfilt : e.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat? = ys :=
    hek.2 ▸ filterMap_of_mapM hys
  rw [hfilt] at hlift
  have hw₂ : w.val = wi := by
    rw [hek.1, hw] at hwire
    exact (Option.some.inj hwire).symm
  have hx₂ : l.exp.exports[w] = xe :=
    (List.getElem?_eq_some_iff.mp (hw₂.symm ▸ hxe : l.exp.exports[w.val]? = some xe)).2
  rw [hx₂] at hdiv
  have hxm : xe ∈ l.exp.exports := List.mem_of_getElem? hxe
  have hres : ft.results.length ≤ 1 := (S.arity.2 _ (List.mem_of_getElem? hk)).2.2
  have hfl : ArenaField.funcs.get? B.store (l.wireFid k) =
      some (.lifted (Ie.addrs.getD xe.core 0) (witFt ft) {} ⟨1⟩) :=
    hpx ▸ S.lifted k wi xe hw hxe
  obtain ⟨hpf, hys', hmaxp, hrf, hmaxr, -⟩ :=
    site_of ((LInv.linkOk S hI₁) [] y₁ _ ys (.done .refl) hst) hfl hres
  -- the machine run to the nested activation of A
  obtain ⟨tr₁, htr₁, r₁⟩ := Adequacy.coreCfg_steps_of (prof := prof)
    (hr := fun _ _ => false) (dispatch := DI P impl) (B := extN B ιe N C) (th := th) (K := K)
    (segs := segs) (rest := rest) hy₁
  obtain ⟨ιi, hi, hleave⟩ := hB.inst2 ιe N C
  obtain ⟨pos, C₁, M₁, th', K', segs', rest', tr₂, hrun, hctl, hcore, -, -, -⟩ :=
    nest_atTS (prof := prof) (impl := impl) B ιe _ N C th K segs rest y₁ (l.wireFid k)
      (Ie.addrs.getD xe.core 0) ft ys ιi ws hst (hB.entry _ _ _ _ _) hi hleave hfl hB.len
      (addThread?_ok hte _) (removeThread?_enter ιe _) hpf hys' hmaxp hlift hres hrf hmaxr
  have hM : M₁ = coreCfg M₁ th' K' segs' rest' (y₁.1,
      Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (Ie.addrs.getD xe.core 0)
        (lowerArgs ft.params ws)) := by
    rw [← hcore]
    exact eq_coreCfg hctl
  -- A's infinite run in the shared store
  obtain ⟨g, hg0, hg⟩ := hdiv.run
  obtain ⟨ρp, Op, ρc, Oc, -, hR⟩ := hI₁.rel
  have hL₀ := exp_invoke hR.rp hI₁.fnE (hR.fnp ▸ S.owned xe hxm) (lowerArgs ft.params ws)
  rw [hpx] at hg0
  have hinf := link_inf (gL P l) (gLInv P l) hg (hostsSat_lstat S hI₁.funcs)
    (y := (y₁.1, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (Ie.addrs.getD xe.core 0)
      (lowerArgs ft.params ws))) (hg0 ▸ hL₀)
  have hdM : Diverges prof (fun _ _ => false) (DI P impl) M₁ := by
    rw [hM]
    exact SessionDiv.coreCfg_diverges_of hinf
  exact steps_diverges (Adequacy.steps_append r₁ hrun.steps)
    (fun ev hm => (List.mem_append.mp hm).elim (Adequacy.not_host_of_core htr₁ ev)
      (Adequacy.LRun.no_host hrun ev)) hdM

/-- **(iii) Chatter**: infinitely many served import calls are a divergence of the machine. -/
theorem chatter_core (S : LStat P l Ie Ii u₀ F₀ B Op₀) (hB : LFrame B th) {y : CoreSt (E3 P)}
    {s π : Store Nat} {t : STh} (hI : LInv P l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y (s, t) π)
    (hd : Linked2.Chatter P l Ie Ii f s t π) {ιe : InstState} (hte : ThreadsOk ιe)
    (N : List (NRec P)) (C : List (Option (Activation (E3 P) σ))) :
    Diverges prof (fun _ _ => false) (DI P impl) (coreCfg (extN B ιe N C) th K segs rest y) := by
  obtain ⟨q, c, ds, st, hq0, hst0, hc⟩ := hd
  refine diverges_of_segs (fun m => ∃ (k : Nat) (y : CoreSt (E3 P)) (x : Store Nat × STh)
      (ιe : InstState) (N : List (NRec P)) (C : List (Option (Activation (E3 P) σ))),
      m = coreCfg (extN B ιe N C) th K segs rest y ∧ ThreadsOk ιe ∧
      q k = .running f x.1 x.2 ∧ LInv P l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y x (st k)) ?_
    ⟨0, y, (s, t), ιe, N, C, rfl, hte, hq0, hst0 ▸ hI⟩
  rintro m ⟨k, y, x, ιe, N, C, rfl, hte, hqk, hIk⟩
  obtain ⟨hpath, hrel, hexp⟩ := hc k
  rw [hqk] at hpath
  -- the state after the call is running
  obtain ⟨s₁, t₁, hq₁⟩ : ∃ s₁ t₁, q (k + 1) = .running f s₁ t₁ := by
    generalize q (k + 1) = q' at hpath
    obtain ⟨e, v⟩ := c k
    obtain ⟨s', t', -, -, -, -, -, hp⟩ := path_round_inv (rest := []) (by simpa [callMoves] using hpath)
    cases hp
    exact ⟨_, _, rfl⟩
  rw [hq₁] at hpath
  have hexp' : Linked2.ExpRunT P l Ie (st k) [ds k].flatten (st (k + 1)) := by
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using hexp
  rcases roundsPre_fwd S [c k] [ds k] y x (st k) (st (k + 1)) s₁ t₁ hIk (.cons hrel .nil) hexp'
      hpath with ⟨recs, yc, hseg, hlen, hIc⟩ | hdm
  · obtain ⟨ιe', N', C', tr, hte', hq, hne, r⟩ := lseg_runN (prof := prof) (impl := impl) (K := K)
      (segs := segs) (rest := rest) hB hseg ιe N C hte (LInv.linkOk S hIk)
    have htr : tr ≠ [] := by
      rcases hne with h | h
      · subst h
        simp at hlen
      · exact h
    exact ⟨tr, _, r, htr, hq.1, k + 1, yc, (s₁, t₁), ιe', N', C', rfl, hte', hq₁, hIc⟩
  · have h₂ := (hc (k + 1)).1
    rw [hq₁] at h₂
    exact (doomed_no_call hdm h₂).elim

/-! ## One call -/

variable {B₀ : Machine.Config (E3 P) σ} {fs : List (CFuncInst (core3P P))}

/-- **A specification round that never answers is a diverging call of the reference machine.** -/
theorem linkDiv_fwd (S₀ : LStat P l Ie Ii u₀ F₀ B₀ (ownOf s₀)) (hB₀ : B₀.store.funcs = fs)
    (hfs : LiftedOk l Ii s₀ fs) {cs : (core3P P).Store (CanonHost (core3P P))}
    {ιe ιi : InstState} {G : Garb P σ} {ST : List Subtask} {h₀ : σ} {k : Nat} {u π : Store Nat}
    (R : ReadyL P l Ie Ii s₀ u₀ F₀ cs ιe ιi G u π k) {j : Fin l.imp.exports.length}
    {vs : List Silmaril.Wasm.Component.Val} (hd : Linked2.RoundDiv P l Ie Ii u π j vs) :
    CallDiverges prof (fun _ _ => false) (DI P impl) (readyCfgL cs ιe ιi fs G ST h₀) ⟨k⟩
      ⟨l.exp.exports.length + j⟩ (vs.map toRefVal) := by
  obtain ⟨d, s, t, π₁, rfl, rfl, hok, hpath, hexp, hsrc⟩ := hd
  obtain ⟨xs, hck, hf₁, hf₂, hrel⟩ := hok
  have hvs : ValTy.checkList l.imp.exports[d.j].ty.params d.vs = true := by
    unfold checkLower at hck
    split_ifs at hck with h
    exact h
  have hxs : xs = lowerArgs l.imp.exports[d.j].ty.params d.vs := by
    simp only [checkLower, hvs, ↓reduceIte, Option.some.injEq] at hck
    exact hck.symm
  subst hxs
  have hx : l.imp.exports[d.j] ∈ l.imp.exports := List.getElem_mem d.j.isLt
  obtain ⟨hmax, hmaxr, hres⟩ := S₀.arity.1 _ hx
  obtain ⟨hpf, hrf⟩ := S₀.floats.1 _ hx
  have ha : Ii.addrs.getD l.imp.exports[d.j].core 0 = Ii.addr d.f.1 := by
    rw [← hf₁]
    rfl
  have hfj : fs[l.exp.exports.length + d.j]? = some (.lifted (s₀.funcs.length + Ii.addr d.f.1)
      (liftedFt l.imp.exports[d.j]) {} ⟨2⟩) := ha ▸ hfs d.j
  obtain ⟨M₀, th, K, segs, rest, tr₁, hpre, hat⟩ := call_atLKTS (impl := impl) prof cs ιe ιi fs G
    ST h₀ k (l.exp.exports.length + d.j) _ l.imp.exports[d.j] d.vs hpf hvs hmax hres hmaxr hrf
    R.thI R.leave hfj
  have S : LStat P l Ie Ii u F₀ M₀ (ownOf s₀) := S₀.move R.inv.wfI (hat.funcs.trans hB₀.symm)
  have hI₀ : LInv P l Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) d.f
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (s₀.funcs.length + Ii.addr d.f.1)
        (lowerArgs l.imp.exports[d.j].ty.params d.vs)) (u, Ii.initThread d.f) π :=
    linv_ready R.inv hf₂ rfl
  have hpath' : Ii.Path P (.running d.f u (Ii.initThread d.f)) (callMoves d.cs)
      (.running d.f s t) := by
    have h : Ii.Path P (.idle u) (.inr (.ask d.f) :: callMoves d.cs) (.running d.f s t) := hpath
    cases h with
    | cons h₁ h₂ =>
      cases h₁
      exact h₂
  rcases roundsPre_fwd S d.cs d.dss _ (u, Ii.initThread d.f) π π₁ s t hI₀ hrel hexp hpath' with
    ⟨recs, yc, hseg, -, hIc⟩ | hdm
  · have hlive₀ : Live M₀ := by
      rw [hat.start]
      exact coreCfg_extN_live _ _ _ _ _ _ _ _ _
    obtain ⟨ιe', N', C', tr₂, hte', hq₂, r₂⟩ := lseg_run (prof := prof) (impl := impl) (K := K)
      (segs := segs) (rest := rest) hat.frame hseg ιe [] M₀.conts R.thE (LInv.linkOk S hI₀)
    have r₁₂ : Steps prof (fun _ _ => false) (DI P impl)
        (invokedAtL cs ιe ιi fs G ST h₀ k (l.exp.exports.length + d.j) (d.vs.map toRefVal))
        (tr₁ ++ tr₂) (coreCfg (extN M₀ ιe' N' C') th K segs rest yc) := by
      refine Adequacy.steps_append hpre.steps ?_
      rw [← hat.start] at r₂
      exact r₂
    have hq₁₂ : Quiet (tr₁ ++ tr₂) := (Quiet.of_lrun hpre hlive₀).append hq₂
    refine ⟨_, invoke_stepL R.fresh _ _, steps_diverges r₁₂ hq₁₂.1 ?_⟩
    rcases hsrc with h | h | h
    · exact divB_core S hIc h ιe' N' C'
    · exact divA_core S hat.frame hIc h hte' N' C'
    · exact chatter_core S hat.frame hIc h hte' N' C'
  · exfalso
    rcases hsrc with h | ⟨e, s', t', nm, ft, ws, w, h, _⟩ | ⟨q, c, ds, st, hq0, _, hc⟩
    · exact not_divB_doomed hdm h
    · exact doomed_no_ask hdm h
    · have h₀ := (hc 0).1
      rw [hq0] at h₀
      exact doomed_no_call hdm h₀

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDiv
