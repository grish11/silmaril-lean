module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.Linked
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.Wait

/-!
# Reading back a divergence of the exporter's environment along one run

The exporter A of a `Linked2` has no imports. A divergence of its environment (`expObs`, the
exporter's node above `maskH 0`) after complete rounds `L` and a typed pending question is read
back **along one run of its instance** (`exp_div_readback`): the complete rounds are a session
of the exporter's specification from the instance's store to a store `π` (`SessRounds`), and the
pending call diverges from `π` (`DivAt`). The profile need not be deterministic, so the store at
which the call diverges must come from the same run as the rounds; the read-back of complete
rounds alone (`expEnv_specRoundsT`) does not give it.

* `not_silentChatter_nil`: a component without imports has no silent chatter above any handler
  (its lower questions go through `maskH 0`);
* the environment's divergences are its node's own: `maskH 0` does not diverge
  (`DStrategy.ofHandler_div`) and the node makes no lower move, so it has no chatter with
  `maskH 0`;
* the node's divergence is the exporter's IR divergence (`div_node_inst`), read back by
  `imp_div_readback` at `SimpleI.ofSimple l.exp`;
* `sessRounds_of_rdI`, `divAt_of_path`: the instance's rounds (`RdI`) and its pending call, on
  the path the read-back gives.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq
open Silmaril.Wasm.SingleThreaded (ofFlat toFlat? Thread)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

/-! ## Plays without lower moves -/

section NoInl

variable {E F G : Sig.{0}}

theorem noInl_callMoves {cs : List (Round E)} (h : NoInl (callMoves cs : List (Move E F))) :
    cs = [] := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    obtain ⟨m, n⟩ := c
    exact absurd (List.mem_cons_self (a := (Sum.inl (Ev.ask m) : Move E F))) (h (.ask m))

theorem rplay_cons (r : CRound E F) (cl : List (CRound E F)) (g : F.Op) (cs : List (Round E)) :
    rplay (r :: cl) g cs =
      .inr (.ask r.q) :: (callMoves r.cs ++ (.inr (.ans r.q r.a) :: rplay cl g cs)) := by
  simp only [rplay, cplay, List.cons_append, List.append_assoc]

/-- A pending play without lower moves has no lower calls. -/
theorem noInl_rplay : ∀ {cl : List (CRound E F)} {g : F.Op} {cs : List (Round E)},
    NoInl (rplay cl g cs) → (∀ r ∈ cl, r.cs = []) ∧ cs = []
  | [], _, _, h => ⟨fun _ hr => (nomatch hr),
      noInl_callMoves fun e he => h e (List.mem_cons_of_mem _ he)⟩
  | r :: cl, g, cs, h => by
    rw [rplay_cons] at h
    have h₁ : r.cs = [] := noInl_callMoves fun e he =>
      h e (List.mem_cons_of_mem _ (List.mem_append_left _ he))
    obtain ⟨h₂, h₃⟩ := noInl_rplay (cl := cl) (g := g) (cs := cs) fun e he =>
      h e (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ he)))
    refine ⟨fun x hx => ?_, h₃⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h₁
    · exact h₂ x hx

/-- A handler below rounds without lower calls makes none. -/
theorem hb_eq_of_nil {h : Handler E E} :
    ∀ {up : List (CRound E G)} {low : List (CRound E G)},
      List.Forall₂ (HBR h) up low → (∀ r ∈ up, r.cs = []) → low = up
  | [], [], .nil, _ => rfl
  | _ :: _, _ :: _, .cons hr H, hn => by
    obtain ⟨q, a, cs, cs', rfl, rfl, H'⟩ := hr
    have hcs : cs = [] := hn _ List.mem_cons_self
    subst hcs
    cases H'
    rw [hb_eq_of_nil H fun r hr => hn r (List.mem_cons_of_mem _ hr)]

theorem twos_snoc_inj {L L' : List (Round F)} {x x' : Move E F}
    (h : twos L ++ [x] = twos L' ++ [x']) : L = L' ∧ x = x' := by
  obtain ⟨h₁, h₂⟩ := List.append_inj' h rfl
  exact ⟨twos_inj' h₁, List.singleton_inj.mp h₂⟩

theorem downBy_zero (r : CRound E sigU) : downBy 0 r = r := rfl

end NoInl

/-! ## Components without imports -/

/-- **No silent chatter above a component without imports**: its lower questions go through
`maskH 0`, so it makes none. -/
theorem not_silentChatter_nil {M : Type} [CoreModule M] (C : DCoreSem M) (h : Handler sigU sigU)
    (ns : List (Node M)) (xs : List Export) {p : List (Move sigU sigU)} :
    ¬ SilentChatter h ((Comp.mk [] ns xs).denUD C) p := by
  rintro ⟨I, hI, t₀, ht₀, ⟨g, hg⟩, hsil, -⟩
  have hinf := ((Comp.mk [] ns xs).denUD C).inf_isInf hI
  obtain ⟨t₁, ht₁, hlen⟩ := hinf.unbounded (t₀.length + 1)
  have hpre : t₀ <+: t₁ := by
    rcases hinf.total ht₀ ht₁ with h | h
    · exact h
    · have := h.length_le
      omega
  obtain ⟨r, rfl⟩ := hpre
  cases r with
  | nil => simp at hlen
  | cons x r =>
    have hx : t₀ ++ [] ++ [x] ∈ I := hinf.of_prefix ht₁ ⟨r, by simp⟩
    obtain ⟨e, rfl, -⟩ := hsil [] x hx
    have hmem := ((Comp.mk [] ns xs).denUD C).inf_sub hI hx
    obtain ⟨z, hz⟩ := ((Comp.mk [] ns xs).denUD C).toStrategy.legal hmem
    rw [List.append_nil] at hz
    obtain ⟨y, hy, hst⟩ := Path.concat_iff.1 hz
    obtain rfl := Path.det hg hy
    cases hst with
    | call _ m =>
      have hlt : m.1 < ([] : Iface).length :=
        lowAsk_denUD C _ _ _ hmem (List.mem_append_right _ List.mem_cons_self)
      exact Nat.not_lt_zero _ hlt

theorem impRel_ofSimple_nil {c : Simple} {I : SInst} :
    ∀ {ics : List (Round I.E)}
      {dss : List (List (Round (sigN (SimpleI.ofSimple c).imports.length)))},
      List.Forall₂ (ImpRel (SimpleI.ofSimple c) I) ics dss → ics = []
  | [], _, _ => rfl
  | _ :: _, _, .cons hx _ => by
    obtain ⟨nm, ft, A, hft, -⟩ := hx
    simp [SimpleI.ofSimple] at hft

theorem good_ofSimple {c : Simple} (hc : c.Good) : (SimpleI.ofSimple c).Good :=
  ⟨hc.names, hc.core, rfl⟩

theorem isInst_ofSimple {c : Simple} {I : SInst} (hI : c.mod.IsInst I) :
    (SimpleI.ofSimple c).mod.IsInst I :=
  ⟨hI.1, hI.2.1, hI.2.2⟩

theorem noInl_expComp (P : Profile) (l : Linked2) :
    ∀ t ∈ ((SimpleI.ofSimple l.exp).toComp.denUD (impSemD P)).toStrategy, NoInl t := by
  rw [Reference.toStrategy_denUD_impSemD, denU_ofSimple, denU_toComp]
  exact noInl_comp (noInl_comp (noInl_ofHandler_pure pure_maskH0))

theorem noInl_expNodeD (P : Profile) (l : Linked2) :
    ∀ t ∈ (Node.denD (impSemD P) 0 l.expNode).toStrategy, NoInl t := by
  rw [toStrategy_node_denD, forget_impSemD, Linked2.expNode, Node.den]
  exact noInl_comp (noInl_ofHandler_pure fun _ => ⟨none, rfl⟩)

/-! ## The instance's rounds and its pending call -/

theorem initThread_eq {c : Simple} {I : SInst} {j : Fin c.exports.length} {vs : List IVal}
    {f : I.F.Op} (h₁ : f.1.val = c.exports[j].core)
    (h₂ : f.2.1 = (lowerArgs c.exports[j].ty.params vs).map ofFlat) :
    I.initThread f =
      Thread.invokeFlat (I.addrs.getD c.exports[j].core 0)
        (lowerArgs c.exports[j].ty.params vs) := by
  show Thread.pending (I.addrs.getD f.1.val 0) f.2.1 = _
  rw [h₁, h₂]
  rfl

/-- **The instance's rounds along a path are a session of the specification** of the import-free
exporter, from the path's first store to its last. -/
theorem sessRounds_of_rdI {P : Profile} {c : Simple} {I : SInst} :
    ∀ {ri : List (CRound I.E I.F)} {up : List (CRound sigU sigU)} {s s' : Store Nat},
      List.Forall₂ (RdI (SimpleI.ofSimple c) I) ri up →
      I.Path P (.idle s) (cplay ri) (.idle s') →
      SessRounds P c I s (up.map CRound.toRound) s'
  | [], [], s, s', .nil, hp => by
    cases hp
    exact .nil s
  | r :: ri, u :: up, s, s', .cons hr H, hp => by
    obtain ⟨j, vs, xs, dss, hq, hl, hr₁, hr₂, hF, -, ha⟩ := hr
    obtain ⟨hck, rfl⟩ := checkLower_eq hl
    obtain ⟨rq, rcs, ra⟩ := r
    have hrcs : rcs = [] := impRel_ofSimple_nil hF
    subst hrcs
    obtain ⟨uq, ucs, ua⟩ := u
    have hq' : uq = (j.val, .vals vs) := hq
    subst hq'
    have ha' : ua = (answerPayload ra).bind
        (Adapter.up (.lift c.exports[j].ty)) := ha
    have hp' : I.Path P (.idle s) (.inr (.ask rq) :: .inr (.ans rq ra) :: cplay ri) (.idle s') := hp
    cases hp' with
    | cons t₁ h₁ =>
      cases t₁ with
      | call =>
        cases h₁ with
        | cons t₂ h₂ =>
          cases t₂ with
          | @oret _ _ s₁ _ t' res _ run final answer =>
            have hrest := sessRounds_of_rdI H h₂
            have hi := initThread_eq (c := c) (I := I) (j := j) (vs := vs) (f := rq) hr₁ hr₂
            rw [hi] at run
            have hpay : answerPayload ra = (coreRes res).map .flat := by
              rw [answerPayload_of_ofResult? answer]
              cases res <;> rfl
            rw [hpay] at ha'
            show SessRounds P c I s (⟨(j.val, .vals vs), ua⟩ :: up.map CRound.toRound) s'
            cases ua with
            | none =>
              exact .trap j.isLt ⟨hck, t', res, run, final, traps_of_up_none ha'.symm⟩ hrest
            | some a =>
              cases res with
              | values cvs =>
                cases hys : cvs.mapM toFlat? with
                | none => simp [coreRes, hys] at ha'
                | some ys =>
                  cases hws : liftArgs c.exports[j.val].ty.results ys with
                  | none => simp [coreRes, hys, Adapter.up, hws] at ha'
                  | some ws =>
                    have ha₀ : a = .vals ws := by simpa [coreRes, hys, Adapter.up, hws] using ha'
                    subst ha₀
                    exact .ret j.isLt ⟨hck, t', cvs, ys, run, final, hys, hws⟩ hrest
              | trap => simp [coreRes] at ha'
              | throw _ => simp [coreRes] at ha'

/-- **The pending call diverges from the store it starts at.** -/
theorem divAt_of_path {P : Profile} {c : Simple} {I : SInst} {w : Fin c.exports.length}
    {ws : List IVal} (hck : ValTy.checkList c.exports[w].ty.params ws = true) {f : I.F.Op}
    {π s : Store Nat} {t : Thread} (h₁ : f.1.val = c.exports[w].core)
    (h₂ : f.2.1 = (lowerArgs c.exports[w].ty.params ws).map ofFlat)
    (hp : I.Path P (.idle π) [.inr (.ask f)] (.running f s t)) (hB : Linked2.DivB P s t) :
    DivAt P I c.exports[w] ws π := by
  cases hp with
  | cons t₁ h₁' =>
    cases t₁ with
    | call =>
      cases h₁'
      obtain ⟨g, hg, hstep⟩ := hB
      refine ⟨hck, g, ?_, hstep⟩
      rw [hg, initThread_eq h₁ h₂]

/-! ## The exporter's environment -/

/-- **The exporter's environment diverges only where its node does**: `maskH 0` does not
diverge, and the node makes no lower move, so it has no chatter with `maskH 0`. -/
theorem expObs_nodeDiv {P : Profile} {l : Linked2} {p : List (Move sigU sigU)}
    (h : p ∈ (Linked2.expObs (impSemD P) l).div) :
    p ∈ NodeDiv 0 (Strategy.ofHandler (maskH 0)) (Node.denD (impSemD P) 0 l.expNode) := by
  rcases h with (⟨s, t, -, hs, -⟩ | hD) | ⟨I, -, L', hL', s₀, c₀, -, -, -, -, hk⟩
  · have hs' : s ∈ (DStrategy.ofHandler (maskH 0)).div := hs
    rw [DStrategy.ofHandler_div] at hs'
    exact hs'.elim
  · exact hD
  · exfalso
    obtain ⟨w', hw', -, hwL⟩ := hk 1
    have hmem := (Node.denD (impSemD P) 0 l.expNode).inf_sub hL' hwL
    obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos hw'
    exact noInl_expNodeD P l _ hmem x (List.mem_append_right _ (List.mem_map_of_mem hx))

/-- **A divergence of the exporter's environment** is complete rounds, then a pending question. -/
theorem expObs_div_shape {P : Profile} {l : Linked2} {p : List (Move sigU sigU)}
    (h : p ∈ (Linked2.expObs (impSemD P) l).div) :
    ∃ (L : List (Round sigU)) (g : sigU.Op), p = twos L ++ [.inr (.ask g)] := by
  obtain ⟨x, y, hz, hx, a, b, hz₂, ⟨ha, haN⟩, hb⟩ := expObs_nodeDiv h
  obtain ⟨f₂, ha₂⟩ :=
    ((DStrategy.id sigU).pair (Node.denD (impSemD P) 0 l.expNode)).div_run ⟨ha, .inr haN⟩
  obtain ⟨yb, hyb⟩ := Strategy.mem_ofHandler.mp hb
  obtain ⟨g₁, hy⟩ := run_of_zip_top hz₂ ha₂ hyb
  obtain ⟨cl, cs, rfl⟩ := exists_rplay hy
  exact ⟨_, _, (serve_run (noInl_ofHandler_pure pure_maskH0 x hx) hz).2⟩

/-! ## The read-back -/

/-- **The exporter's environment, diverging after complete rounds, read back along one run**
(under `Linked2.Adequate`): after typed complete rounds `L` and a typed pending call of export
`w` on `ws`, a divergence of the exporter's environment is a session of the exporter's
specification from its instance's store to a store `π`, from which the call diverges. -/
theorem exp_div_readback {P : Profile} {l : Linked2} (hl : l.Adequate) {Ie : SInst}
    (hIe : l.exp.mod.IsInst Ie) {L : List (Round sigU)}
    (hL : ∀ x ∈ L, ∃ (w : Fin l.exp.exports.length) (ws : List IVal),
      x.1 = (w.val, .vals ws) ∧ ValTy.checkList l.exp.exports[w].ty.params ws = true)
    {w : Fin l.exp.exports.length} {ws : List IVal}
    (hck : ValTy.checkList l.exp.exports[w].ty.params ws = true)
    (h : twos L ++ [.inr (.ask (w.val, .vals ws))] ∈ (Linked2.expObs (impSemD P) l).div) :
    ∃ π, SessRounds P l.exp Ie Ie.store L π ∧ DivAt P Ie l.exp.exports[w] ws π := by
  -- the node's own divergence, below `maskH 0` and `splitH 0`
  obtain ⟨x, y, hz, hx, a, b, hz₂, ⟨ha, haN⟩, hb⟩ := expObs_nodeDiv h
  obtain ⟨f₂, ha₂⟩ :=
    ((DStrategy.id sigU).pair (Node.denD (impSemD P) 0 l.expNode)).div_run ⟨ha, .inr haN⟩
  obtain ⟨yb, hyb⟩ := Strategy.mem_ofHandler.mp hb
  obtain ⟨g₁, hy⟩ := run_of_zip_top hz₂ ha₂ hyb
  obtain ⟨cl, cs, rfl⟩ := exists_rplay hy
  have hxn : NoInl x := noInl_ofHandler_pure pure_maskH0 x hx
  obtain ⟨-, hpe⟩ := serve_run hxn hz
  obtain ⟨rfl, hg₁⟩ := twos_snoc_inj hpe
  cases hg₁
  obtain ⟨low, k, H, hk, rfl⟩ := hc_zip_run (oneShot_splitH 0) ha₂ hyb hz₂
  rw [hc_splitH_inv H fun _ _ => Nat.zero_le _] at haN
  simp only [splitH, Nat.not_lt_zero, ↓reduceIte] at hk
  obtain ⟨hk, -⟩ := Prog.call.inj hk
  subst hk
  rw [halves_rplay_inr] at haN
  -- the node: the exporter's IR below `implsH 0 []`
  rw [Linked2.expNode, div_node_inst] at haN
  rcases haN with ⟨u, v, hzN, hu, hv⟩ | hsil
  swap
  · exact absurd hsil (not_silentChatter_nil _ _ _ _)
  obtain ⟨g₂, hv₂⟩ := ((SimpleI.ofSimple l.exp).toComp.denUD (impSemD P)).div_run hv
  obtain ⟨up, cs₂, rfl⟩ := exists_rplay hv₂
  obtain ⟨hupn, rfl⟩ := noInl_rplay
    (noInl_expComp P l _ (((SimpleI.ofSimple l.exp).toComp.denUD (impSemD P)).div_mem hv))
  obtain ⟨yN, hyN⟩ := Strategy.mem_ofHandler.mp hu
  obtain ⟨low₂, cs', H₂, H₂', he₂⟩ := hb_zip_run (oneShot_implsH _ _) hyN hzN
  cases H₂'
  rw [hb_eq_of_nil (hb_forall₂ H₂) hupn] at he₂
  obtain ⟨hcl, hg₂, rfl⟩ := rplay_inj he₂
  subst hg₂
  have hcl' : cl = up := by
    rw [← hcl]
    exact (List.map_id' cl).symm
  subst hcl'
  -- the exporter's IR
  have htop : ∀ u ∈ cl, TopI (SimpleI.ofSimple l.exp) u := by
    intro u hu
    exact hL _ (List.mem_map_of_mem hu)
  obtain ⟨ri, f, ics, dss, sB, tB, F, hpath, hdiv, hf₁, hf₂, hF, -⟩ :=
    imp_div_readback (good_ofSimple hl.expGood) (isInst_ofSimple hIe) htop (j := w) hck hv
  obtain rfl := impRel_ofSimple_nil hF
  have hpath' : Ie.Path P (.idle Ie.store) (cplay ri ++ [.inr (.ask f)]) (.running f sB tB) :=
    hpath
  obtain ⟨q₁, hp₁, hp₂⟩ := path_split_inst hpath'
  obtain ⟨π, rfl⟩ := idle_of_path_cplay hp₁
  exact ⟨π, sessRounds_of_rdI F hp₁, divAt_of_path (c := l.exp) hck hf₁ hf₂ hp₂ hdiv⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq
