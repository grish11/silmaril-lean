module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionDiv.Round

/-!
# Diverging calls of `HLinked2.toRef`: one call

From the importer's core activation at the shared thread `y`, in any `extG` extension of the
call's frame in host state `h`, `LInv` (at `l.toW`) relating it to the importer's part at
`(s, t)` and the exporter's store `π`, each internal source of a specification divergence is a
quiet divergence of the machine in host state `h`:

* `divB_coreH` (**B diverges host-free**): B's infinite run is an infinite core run of the shared
  thread (`link_inf` at the renaming `gL P l.toW`), one core step per segment;
* `divA_coreH` (**A diverges inside a wired import call**): B's run to the callout, the nested
  `canon lower`/`canon lift` into A (`nest_atTSH`, which keeps the host state), and A's infinite
  run from its store as an infinite core run of the nested activation;
* `chatter_coreH` (**wired chatter**): each served import call is a nonempty quiet run back to
  the importer's core activation in host state `h` (`roundsPre_fwdH` on one call, which makes no
  host call: `expRunT_toH`), concatenated by `quietDiverges_of_segs`.

`linkDivH_fwd`: from a configuration between calls (`ReadyL` at `l.toW`) in host state `h₀`, a
round that never answers after its host calls (`HLinked2.RoundDiv`, the host answering as `g`
from `h₀` to `h'`, `Handles`) is a top-level call diverging quietly in host state `h'`: the
host's invocation, the deterministic prefix (`call_atLKTS`), the round's prefix
(`roundsPre_fwdH`, its host calls answered) and one of the three. When the prefix dooms the
importer, no source applies (`not_divB_doomed`, `doomed_no_ask`, `doomed_no_call`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionDiv

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDiv
open Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower Payload sigN FuncTy)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread
local notation "RVal" => Silmaril.Wasm.Component.Reference.Val

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}
  {g : σ → HostFuncId → List RVal → Option (List RVal × σ)}

/-- **Wired import calls are exporter runs without host calls**: an `ExpRunT` segment of the
underlying `Linked2` is an `ExpRunH` segment with no host call. -/
theorem expRunT_toH {l : HLinked2} {I : Silmaril.Wasm.Game.ScalarInstance} :
    ∀ {s s' : Store Nat} {ds : List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)},
      Linked2.ExpRunT P l.toL2 I s ds s' → HLinked2.ExpRunH P l I s ds s' ∧ l.hostCalls ds = []
  | _, _, _, .nil _ => ⟨.nil _, rfl⟩
  | _, _, _, .ret (k := k) w hw hR h => by
    have hk : k.val < l.wire.length := (List.getElem?_eq_some_iff.mp hw).1
    have ih := expRunT_toH h
    exact ⟨.ret w hw hR ih.1, (hostCalls_cons_wired hk).trans ih.2⟩
  | _, _, _, .trap (k := k) w hw hT h => by
    have hk : k.val < l.wire.length := (List.getElem?_eq_some_iff.mp hw).1
    have ih := expRunT_toH h
    exact ⟨.trap w hw hT ih.1, (hostCalls_cons_wired hk).trans ih.2⟩

/-- A configuration from which the machine reaches, by a finite run without host events, a
configuration diverging quietly in host state `h`. -/
def DivFrom (prof : ProfileKind) (P : Profile) (impl : HostImpl (E3 P) σ) (h : σ)
    (m : Machine.Config (E3 P) σ) : Prop :=
  ∃ tr m₂, Steps prof (fun _ _ => false) (DI P impl) m tr m₂ ∧ (∀ ev, Label.host ev ∉ tr) ∧
    QuietDiverges prof (fun _ _ => false) (DI P impl) h m₂

theorem DivFrom.of_quiet {h : σ} {m : Machine.Config (E3 P) σ}
    (d : QuietDiverges prof (fun _ _ => false) (DI P impl) h m) : DivFrom prof P impl h m :=
  ⟨[], m, .refl _, (fun _ hm => nomatch hm), d⟩

theorem DivFrom.steps {h : σ} {m m' : Machine.Config (E3 P) σ} {tr : List (Label (E3 P) σ)}
    (r : Steps prof (fun _ _ => false) (DI P impl) m tr m') (hq : ∀ ev, Label.host ev ∉ tr)
    (d : DivFrom prof P impl h m') : DivFrom prof P impl h m := by
  obtain ⟨tr', m₂, r', hq', d'⟩ := d
  obtain ⟨r'', hq''⟩ := steps_quiet_append r hq r' hq'
  exact ⟨_, m₂, r'', hq'', d'⟩

/-! ## The three internal sources at the importer's core activation -/

section Sources

variable {l : HLinked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {u₀ s₀ u : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {M₀ : Machine.Config (E3 P) σ}
  {th : Option ThreadId} {K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))}
  {segs : List (Seg (E3 P) σ)} {rest : List (Activation (E3 P) σ)} {f : Ii.F.Op}

/-- **(i) B diverges host-free**: the machine diverges quietly in B's core activation. -/
theorem divB_coreH (S : HStat P l Ie Ii u F₀ M₀ (ownOf s₀)) {y : CoreSt (E3 P)} {s π : Store Nat}
    {t : STh} (hI : LInv P l.toW Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f y (s, t) π)
    (hd : Linked2.DivB P s t) (ιe : InstState) (SL : List Subtask) (CL : List (Caller (E3 P)))
    (TL : List (Runtime.Task (E3 P))) (HL : List Runtime.Thread)
    (C : List (Option (Activation (E3 P) σ))) (h : σ) :
    QuietDiverges prof (fun _ _ => false) (DI P impl) h
      (coreCfg (extG M₀ ιe SL CL TL HL C h) th K segs rest y) := by
  obtain ⟨gx, hg0, hg⟩ := hd
  obtain ⟨ρp, Op, ρc, Oc, hL, -⟩ := hI.rel
  exact coreCfg_quietDiverges
    (link_inf (gL P l.toW) (gLInv P l.toW) hg (hostsSat_hstat S hI.funcs) (hg0 ▸ hL))

/-- **(ii) A diverges inside a wired import call**: the machine runs quietly to the nested
activation of A's export, which diverges quietly in the same host state. -/
theorem divA_coreH (S : HStat P l Ie Ii u F₀ M₀ (ownOf s₀)) (hF : GFrame M₀ th)
    {y : CoreSt (E3 P)} {s π : Store Nat} {t : STh}
    (hI : LInv P l.toW Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f y (s, t) π)
    (hd : Linked2.DivA P l.toL2 Ie Ii f s t π) {ιe : InstState} (hte : ThreadsOk ιe)
    (SL : List Subtask) (CL : List (Caller (E3 P))) (TL : List (Runtime.Task (E3 P)))
    (HL : List Runtime.Thread) (C : List (Option (Activation (E3 P) σ))) (h : σ) :
    DivFrom prof P impl h (coreCfg (extG M₀ ιe SL CL TL HL C h) th K segs rest y) := by
  obtain ⟨e, s', t', nm, ft, ws, w, hpath, himp, hlift, hwire, hdiv⟩ := hd
  obtain ⟨k, args, x₁, run, co, op⟩ : ∃ (k : Nat) (args : List Silmaril.Wasm.Execution.Core.Val)
      (x₁ : Store Nat × STh), Silmaril.Wasm.Game.Reach P (s, t) x₁ ∧
        Silmaril.Wasm.Game.CalloutAt x₁.1 x₁.2 k args ∧ Ii.importOp? k args = some e := by
    cases hpath with
    | cons h₁ _ =>
      cases h₁ with
      | ucall run co op => exact ⟨_, _, _, run, co, op⟩
  obtain ⟨y₁, hy₁, hI₁⟩ := LInv.reach_fwdH S hI run
  obtain ⟨nm', p, ys, E, a, hk, hdx, hys, hst, hyty⟩ := LInv.callout_fwdH S hI₁ co op
  have hek := ifaceOp?_some op
  have hft : ft = p := by
    rw [hek.1, hk] at himp
    simp only [Option.some.injEq, Prod.mk.injEq] at himp
    exact himp.2.symm
  subst hft
  have hfilt : e.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat? = ys :=
    hek.2 ▸ filterMap_of_mapM hys
  rw [hfilt] at hlift
  have hw : l.wire[k]? = some w.val := by
    rw [← hek.1]
    exact hwire
  have hxe : l.exp.exports[w.val]? = some l.exp.exports[w] := List.getElem?_eq_getElem w.isLt
  obtain ⟨xe', hxe', hty⟩ := S.wireTy.ty k w.val hw
  rw [hxe] at hxe'
  obtain rfl := Option.some.inj hxe'
  have hpx : l.exp.exports[w].ty = ft := by
    rw [hk] at hty
    simp only [Option.map_some, Option.some.injEq] at hty
    exact hty.symm
  have hk₁ : l.imp.imports[k]? = some (nm', l.exp.exports[w].ty) := by rw [hpx]; exact hk
  have hxm : l.exp.exports[w] ∈ l.exp.exports := List.getElem_mem w.isLt
  have hres : ft.results.length ≤ 1 := (S.arity.2 _ (List.mem_of_getElem? hk)).2.2
  have hfl : ArenaField.funcs.get? M₀.store (l.fid k) =
      some (.lifted (Ie.addrs.getD l.exp.exports[w].core 0) (witFt ft) {} ⟨1⟩) :=
    hpx ▸ S.lifted k w.val l.exp.exports[w] hw hxe
  have hsite : LinkSite M₀ y₁ (.lowered (l.fid k) (witFt ft) {} ⟨2⟩) ys :=
    hpx ▸ LInv.siteH S hI₁ hk₁ hw hxe (hpx ▸ hyty)
  obtain ⟨hpf, hys', hmaxp, hrf, hmaxr, -⟩ := site_of hsite hfl hres
  -- the machine run to the nested activation of A
  obtain ⟨tr₁, htr₁, r₁⟩ := Adequacy.coreCfg_steps_of (prof := prof)
    (hr := fun _ _ => false) (dispatch := DI P impl) (B := extG M₀ ιe SL CL TL HL C h) (th := th)
    (K := K) (segs := segs) (rest := rest) hy₁
  have hB := hF.lframe ιe SL CL TL HL C h
  have hf' : ArenaField.funcs.get? (extG M₀ ιe SL CL TL HL C h).store (l.fid k) =
      some (.lifted (Ie.addrs.getD l.exp.exports[w].core 0) (witFt ft) {} ⟨1⟩) :=
    (funcs_extG _ _ _ _ _ _ _ _ _).trans hfl
  obtain ⟨ιi, hi, hleave⟩ := hB.inst2 ιe [] C
  have hadd := addThread?_ok hte
    ⟨(extN (extG M₀ ιe SL CL TL HL C h) ιe [] C).store.threads.length⟩
  have hrem := removeThread?_enter ιe
    ⟨(extN (extG M₀ ιe SL CL TL HL C h) ιe [] C).store.threads.length⟩
  obtain ⟨pos, C₁, M₁, th', K', segs', rest', tr₂, hrun, hctl, hcore, -, hhost, -, -⟩ :=
    nest_atTSH (prof := prof) (impl := impl) (extG M₀ ιe SL CL TL HL C h) ιe _ [] C th K segs
      rest y₁ (l.fid k) (Ie.addrs.getD l.exp.exports[w].core 0) ft ys ιi ws hst
      (hB.entry _ _ _ _ _) hi hleave hf' hB.len hadd hrem hpf hys' hmaxp hlift hres hrf hmaxr
  rw [extN_extG_nil] at hrun
  have hM : M₁ = coreCfg M₁ th' K' segs' rest' (y₁.1,
      Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (Ie.addrs.getD l.exp.exports[w].core 0)
        (lowerArgs ft.params ws)) := by
    rw [← hcore]
    exact eq_coreCfg hctl
  -- A's infinite run in the shared store
  obtain ⟨gx, hg0, hg⟩ := hdiv.run
  obtain ⟨ρp, Op, ρc, Oc, -, hR⟩ := hI₁.rel
  have hL₀ := exp_invoke hR.rp hI₁.fnE (hR.fnp ▸ S.owned l.exp.exports[w] hxm)
    (lowerArgs ft.params ws)
  rw [hpx] at hg0
  have hinf := link_inf (gL P l.toW) (gLInv P l.toW) hg (hostsSat_hstat S hI₁.funcs)
    (y := (y₁.1, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat
      (Ie.addrs.getD l.exp.exports[w].core 0) (lowerArgs ft.params ws))) (hg0 ▸ hL₀)
  have hdM : QuietDiverges prof (fun _ _ => false) (DI P impl) h M₁ := by
    have e : h = M₁.host := hhost.symm
    rw [e, hM]
    exact coreCfg_quietDiverges hinf
  exact ⟨_, M₁, Adequacy.steps_append r₁ hrun.steps,
    fun ev hm => (List.mem_append.mp hm).elim (Adequacy.not_host_of_core htr₁ ev)
      (Adequacy.LRun.no_host hrun ev), hdM⟩

/-- **(iii) Wired chatter**: infinitely many import calls of B, each answered by A, are a quiet
divergence of the machine in the host state of the frame. -/
theorem chatter_coreH (S : HStat P l Ie Ii u F₀ M₀ (ownOf s₀)) (hF : GFrame M₀ th)
    (hH : HostHandles prof P impl g l M₀ th K segs rest) (hT : l.HostTyped g)
    {y : CoreSt (E3 P)} {s π : Store Nat} {t : STh}
    (hI : LInv P l.toW Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f y (s, t) π)
    (hd : Linked2.Chatter P l.toL2 Ie Ii f s t π) {ιe : InstState} (hte : ThreadsOk ιe)
    (SL : List Subtask) (CL : List (Caller (E3 P))) (TL : List (Runtime.Task (E3 P)))
    (HL : List Runtime.Thread) (C : List (Option (Activation (E3 P) σ))) (h : σ) :
    QuietDiverges prof (fun _ _ => false) (DI P impl) h
      (coreCfg (extG M₀ ιe SL CL TL HL C h) th K segs rest y) := by
  obtain ⟨q, c, ds, st, hq0, hst0, hc⟩ := hd
  refine quietDiverges_of_segs (fun m => ∃ (k : Nat) (y : CoreSt (E3 P)) (x : Store Nat × STh)
      (ιe : InstState) (SL : List Subtask) (CL : List (Caller (E3 P)))
      (TL : List (Runtime.Task (E3 P))) (HL : List Runtime.Thread)
      (C : List (Option (Activation (E3 P) σ))),
      m = coreCfg (extG M₀ ιe SL CL TL HL C h) th K segs rest y ∧ ThreadsOk ιe ∧
      q k = .running f x.1 x.2 ∧
      LInv P l.toW Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f y x (st k)) h ?_ ?_
    ⟨0, y, (s, t), ιe, SL, CL, TL, HL, C, rfl, hte, hq0, hst0 ▸ hI⟩
  · rintro m ⟨k, y, x, ιe, SL, CL, TL, HL, C, rfl, -⟩
    rfl
  rintro m ⟨k, y, x, ιe, SL, CL, TL, HL, C, rfl, hte, hqk, hIk⟩
  obtain ⟨hpath, hrel, hexp⟩ := hc k
  rw [hqk] at hpath
  -- the state after the call is running
  obtain ⟨s₁, t₁, hq₁⟩ : ∃ s₁ t₁, q (k + 1) = .running f s₁ t₁ := by
    generalize q (k + 1) = q' at hpath
    obtain ⟨e, v⟩ := c k
    obtain ⟨s', t', -, -, -, -, -, hp⟩ :=
      path_round_inv (rest := []) (by simpa [callMoves] using hpath)
    cases hp
    exact ⟨_, _, rfl⟩
  rw [hq₁] at hpath
  obtain ⟨hexpH, hnh⟩ := expRunT_toH hexp
  have hexp' : HLinked2.ExpRunH P l Ie (st k) [ds k].flatten (st (k + 1)) := by
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using hexpH
  have hnh' : l.hostCalls [ds k].flatten = [] := by
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using hnh
  have hhr : HostRun g h (l.hostCalls [ds k].flatten) h := by
    rw [hnh']
    exact .nil h
  rcases roundsPre_fwdH S hF hH hT [c k] [ds k] y x (st k) (st (k + 1)) s₁ t₁ ιe SL CL TL HL C
      h h hIk (.cons hrel .nil) hexp' hhr hpath hte with
    ⟨ιe', SL', CL', TL', HL', C', tr, yc, hte', hq, hne, r, hIc⟩ | hdm
  · have htr : tr ≠ [] := by
      rcases hne with hn | hn | hn
      · cases hn
      · exact hn
      · exact absurd hnh' hn
    exact ⟨tr, _, r, htr, hq.1, k + 1, yc, (s₁, t₁), ιe', SL', CL', TL', HL', C', rfl, hte', hq₁,
      hIc⟩
  · have h₂ := (hc (k + 1)).1
    rw [hq₁] at h₂
    exact (doomed_no_call hdm h₂).elim

end Sources

/-! ## One call -/

section Call

variable {l : HLinked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {s₀ u₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {B₀ : Machine.Config (E3 P) σ}
  {fs : List (CFuncInst (core3P P))}

/-- **A specification round that never answers after its host calls is a quietly diverging call
of the reference machine**, for any host that handles the host callouts as `g` (`Handles`), in
the host state at the end of the round's host calls. -/
theorem linkDivH_fwd (hHd : Handles prof P impl g l) (hT : l.HostTyped g)
    (S₀ : HStat P l Ie Ii u₀ F₀ B₀ (ownOf s₀)) (hB₀ : B₀.store.funcs = fs)
    (hfs : LiftedOkH l Ii s₀ fs) {cs : (core3P P).Store (CanonHost (core3P P))}
    {ιe ιi : InstState} {G : Garb P σ} {ST : List Subtask} {h₀ : σ} {k : Nat} {u π : Store Nat}
    (R : ReadyL P l.toW Ie Ii s₀ u₀ F₀ cs ιe ιi G u π k) {j : Fin l.imp.exports.length}
    {vs : List Silmaril.Wasm.Component.Val} {h' : σ}
    (hd : HLinked2.RoundDiv P l Ie Ii g u π h₀ j vs h') :
    CallQuietDiverges prof (fun _ _ => false) (DI P impl) (readyCfgL cs ιe ιi fs G ST h₀) ⟨k⟩
      ⟨l.host.length + l.exp.exports.length + j⟩ (vs.map toRefVal) h' := by
  obtain ⟨d, s, t, π₁, rfl, rfl, hok, hpath, hexp, hhr, hsrc⟩ := hd
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
  have hfj : fs[l.host.length + l.exp.exports.length + d.j]? =
      some (.lifted (s₀.funcs.length + Ii.addr d.f.1) (liftedFt l.imp.exports[d.j]) {} ⟨2⟩) :=
    ha ▸ hfs d.j
  obtain ⟨M₀, th, K, segs, rest, tr₁, hpre, hat⟩ := call_atLKTS (impl := impl) prof cs ιe ιi fs G
    ST h₀ k (l.host.length + l.exp.exports.length + d.j) _ l.imp.exports[d.j] d.vs hpf hvs hmax
    hres hmaxr hrf R.thI R.leave hfj
  have S : HStat P l Ie Ii u F₀ M₀ (ownOf s₀) := S₀.move R.inv.wfI (hat.funcs.trans hB₀.symm)
  have hF := gframe_of hat
  have hH := hHd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hat S.hostFn
  have hI₀ : LInv P l.toW Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) d.f
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
  have hstart : M₀ = coreCfg (extG M₀ ιe [] [] [] [] M₀.conts h₀) th K segs rest
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (s₀.funcs.length + Ii.addr d.f.1)
        (lowerArgs l.imp.exports[d.j].ty.params d.vs)) := by
    have e := hat.start
    rw [extN_eq_extG] at e
    rw [← hat.host]
    exact e
  have hlive₀ : Live M₀ := by
    rw [hat.start]
    exact coreCfg_extN_live _ _ _ _ _ _ _ _ _
  have hq₁ : Quiet tr₁ := Quiet.of_lrun hpre hlive₀
  rcases roundsPre_fwdH (prof := prof) (impl := impl) S hF hH hT d.cs d.dss _
      (u, Ii.initThread d.f) π π₁ s t ιe [] [] [] [] M₀.conts h₀ h' hI₀ hrel hexp hhr hpath'
      R.thE with
    ⟨ιe', SL', CL', TL', HL', C', tr₂, yc, hte', hq₂, -, r₂, hIc⟩ | hdm
  · rw [← hstart] at r₂
    have hd : DivFrom prof P impl h' (coreCfg (extG M₀ ιe' SL' CL' TL' HL' C' h') th K segs rest
        yc) := by
      rcases hsrc with hs | hs | hs
      · exact .of_quiet (divB_coreH S hIc hs ιe' SL' CL' TL' HL' C' h')
      · exact divA_coreH S hF hIc hs hte' SL' CL' TL' HL' C' h'
      · exact .of_quiet (chatter_coreH S hF hH hT hIc hs hte' SL' CL' TL' HL' C' h')
    obtain ⟨tr, m₂, r, hq, hdq⟩ := DivFrom.steps (Adequacy.steps_append hpre.steps r₂)
      (hq₁.append hq₂).1 hd
    exact ⟨_, tr, m₂, invoke_stepL R.fresh _ _, r, hq, hdq⟩
  · exfalso
    rcases hsrc with hs | ⟨e, s', t', nm, ft, ws, w, hs, _⟩ | ⟨q, c, ds, st, hq0, _, hc⟩
    · exact not_divB_doomed hdm hs
    · exact doomed_no_ask hdm hs
    · have h₀ := (hc 0).1
      rw [hq0] at h₀
      exact doomed_no_call hdm h₀

end Call

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionDiv
