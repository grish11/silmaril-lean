module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.BuildC
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.Coherent
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.ImpCoherent
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionObs.Prod
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionEquiv.Filter
public import Silmaril.Wasm.Component.Reference.LinkedSessionD.Thms
public import Silmaril.Wasm.Component.Reference.LinkedSessionDivInv.Thms

/-!
# Infinite plays of a linked component: infinitely many complete rounds

* **No infinite play ends inside a round** (`inf_idle`): the linked component has no imports, so
  its infinite plays have no lower moves, and every prefix extends, inside the play, to an idle
  position. An infinite interaction between the importer and the exporter inside one round has
  no visible move: it is a divergence (`chatterSrc`), not an infinite play.
* **A strategy below serving infinitely many complete rounds** (`inf_comp_serve`): the
  composite plays the rounds with their lower calls hidden; the strategy below plays the lower
  calls one after another (a finite play when there are finitely many, an infinite play
  otherwise).
* **The exporter serving the import calls of infinitely many rounds** (`exp_env_inf_cat`, at
  `profile o`): the concatenated calls are one stream (`exists_limit`), served along one run
  (`exists_expRunT_stream`), an infinite play of the exporter's environment (`exp_env_inf`).
* **Infinitely many linked rounds** (`inf_denD_build`, at `profile o`): rounds of the importer
  played one after another from its store, their import calls served by the exporter along one
  run, are an infinite play of `l.toComp.denD (impSemD (profile o))`, through the layers of
  `imp_inf_cpl`, the importer's node, `splitH`, the exporter's environment and the outer
  handlers (the infinite versions of `link_layersT` and `linked_seq_denT`).
* `inf_of_infRounds`: hence the coherent rounds of the linked triple (`InfRounds`, the
  productive executions at `profile o`) are infinite plays of the IR.
* `refSessEquivFull_iff_of`: the full injection, from the divergence and infinite-play iffs.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Games.Abstract (streamTake)
open Silmaril.Games.Abstract.StratThread (InfRounds)
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq
open Silmaril.Wasm.Abstract.InstSession (spullD instSession)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance
local notation "GChain" => Silmaril.Games.Chain

/-! ## No infinite play ends inside a round -/

/-- **Without lower moves, an infinite play completes infinitely many rounds**: every prefix
extends, inside the play, to an idle position. -/
theorem inf_idle {F : Sig.{0}} (δ : DStrategy (sigN 0) F) {J : Set (List (Move (sigN 0) F))}
    (hJ : J ∈ δ.inf) : ∀ p ∈ J, ∃ p' ∈ J, p <+: p' ∧ Path .idle p' .idle := by
  intro p hp
  have hI := δ.inf_isInf hJ
  obtain ⟨s, hs, hlen⟩ := hI.unbounded (p.length + 1)
  have hps : p <+: s := (hI.total hp hs).resolve_right fun h => by
    have := h.length_le
    omega
  obtain ⟨y, hy⟩ := δ.toStrategy.legal (δ.inf_sub hJ hs)
  cases y with
  | idle => exact ⟨s, hs, hps, hy⟩
  | wait q m => exact m.1.elim0
  | run g =>
    obtain ⟨s₀, x, rfl⟩ : ∃ s₀ x, s = s₀ ++ [x] := by
      rcases List.eq_nil_or_concat s with h | ⟨s₀, x, h⟩
      · subst h
        simp at hlen
      · exact ⟨s₀, x, by rw [h, List.concat_eq_append]⟩
    obtain ⟨y₀, hy₀, hst⟩ := Path.concat_iff.mp hy
    have hy₀' : y₀ = .idle := by
      cases hst with
      | ask => rfl
      | reply _ m _ => exact m.1.elim0
    subst hy₀'
    refine ⟨s₀, hI.of_prefix hs (List.prefix_append _ _), ?_, hy₀⟩
    rw [List.length_append, List.length_singleton] at hlen
    exact List.prefix_of_prefix_length_le hps (List.prefix_append _ _) (by omega)

/-! ## Chains -/

section Chains

variable {α : Type}

theorem lim_eq_of_cofinal {c d : GChain α} (h₁ : ∀ n, ∃ m, c n <+: d m)
    (h₂ : ∀ m, ∃ n, d m <+: c n) : c.lim = d.lim := by
  ext q
  constructor
  · rintro ⟨n, hq⟩
    obtain ⟨m, hm⟩ := h₁ n
    exact ⟨m, hq.trans hm⟩
  · rintro ⟨m, hq⟩
    obtain ⟨n, hn⟩ := h₂ m
    exact ⟨n, hq.trans hn⟩

theorem catC_succ (T : ℕ → List α) (n : ℕ) : catC T (n + 1) = catC T n ++ T n :=
  flatten_streamTake_succ T n

theorem catC_le (T : ℕ → List α) {a b : ℕ} (h : a ≤ b) : catC T a <+: catC T b :=
  flatten_prefix (streamTake_prefix T h)

/-- **The concatenations of `T`, when unbounded, are prefixes of one stream.** -/
theorem exists_flat_stream (T : ℕ → List α) (hu : ∀ k, ∃ n, k < (catC T n).length) :
    ∃ ζ : ℕ → α, ∀ n m, m ≤ (catC T n).length → streamTake ζ m = (catC T n).take m := by
  obtain ⟨ζ, hζ⟩ := exists_limit (catC T)
    (comparable_of_mono (fun a b h => catC_le T h)) hu
  exact ⟨ζ, fun n m hm => streamTake_eq_take (hζ n) hm⟩

theorem flatten_streamTake_single (ζ : ℕ → α) (n : ℕ) :
    (streamTake (fun k => [ζ k]) n).flatten = streamTake ζ n := by
  rw [streamTake_map (fun x => [x]) ζ n, flatten_map_singleton]

end Chains

/-! ## A strategy below serving infinitely many rounds -/

section Serve

variable {E F G : Sig.{0}}

/-- The hidden lower calls of the first `n` rounds of `W`, answered one after another. -/
def serveC (W : ℕ → CRound F G) : GChain (Move E F) :=
  fun n => twos ((streamTake W n).flatMap (·.cs))

theorem serveC_mono (W : ℕ → CRound F G) : (serveC (E := E) W).Mono := fun n =>
  twos_prefix (by
    rw [streamTake_snoc, List.flatMap_append]
    exact List.prefix_append _ _)

/-- **A strategy below serving infinitely many complete rounds**: when `σ` answers the lower
calls of the rounds `W` of `τ` one after another, each without calls of its own (finitely many
calls, or an infinite play of `σ`), the composite plays the rounds with their lower calls
hidden, forever. -/
theorem inf_comp_serve {σ : DStrategy E F} {τ : DStrategy F G} {W : ℕ → CRound F G}
    (hτ : (cch W).lim ∈ τ.inf) (hσ : ∀ n, serveC (E := E) W n ∈ σ.toStrategy)
    (hσi : (serveC (E := E) W).Unbounded → (serveC (E := E) W).lim ∈ σ.inf) :
    (cch fun k => (W k).hide (E := E)).lim ∈ (σ.comp τ).inf := by
  have e : ∀ n, cch (fun k => (W k).hide (E := E)) n =
      cplay ((streamTake W n).map (CRound.hide (E := E))) := fun n => by
    simp only [cch]
    rw [streamTake_map (CRound.hide (E := E)) W n]
  exact ⟨{ s := serveC W, t := cch W, p := cch fun k => (W k).hide (E := E)
           zip := fun n => by rw [e n]; exact zip_serve (streamTake W n)
           mem_s := hσ
           mem_t := fun n => τ.inf_sub hτ (Silmaril.Games.Chain.mem_lim_self _ n)
           mono_s := serveC_mono W, mono_t := cch_mono W, mono_p := cch_mono _
           unbounded := fun k => ⟨k, (cch_len W k).trans (Nat.le_add_left _ _)⟩
           lim_s := hσi
           lim_t := fun _ => hτ },
    cch_unbounded _, rfl⟩

end Serve

/-! ## The exporter serving the calls of infinitely many rounds -/

section Exp

variable {l : Linked2}

/-- The exporter's environment, as a divergence-observing strategy. -/
abbrev expEnvD (P : Profile) (l : Linked2) : DStrategy sigU sigU :=
  DStrategy.ext 0 (DStrategy.ofHandler (maskH 0)) (Node.denD (impSemD P) 0 l.expNode)

theorem expRunT_catC {P : Profile} {I : SInst} {T : ℕ → List (Round (sigN l.imp.imports.length))}
    {π : ℕ → Store Nat} (hT : ∀ k, Linked2.ExpRunT P l I (π k) (T k) (π (k + 1))) :
    ∀ n, Linked2.ExpRunT P l I (π 0) (catC T n) (π n)
  | 0 => .nil _
  | n + 1 => by
    rw [catC_succ]
    exact LinkedSessionRef.expRunT_append (expRunT_catC hT n) (hT n)

/-- **The exporter's environment plays the calls it serves** (every profile). -/
theorem exp_env_mem {P : Profile} (hl : l.Adequate) {Ie : SInst} (hIe : l.exp.mod.IsInst Ie)
    {ds : List (Round (sigN l.imp.imports.length))} {π' : Store Nat}
    (hrun : Linked2.ExpRunT P l Ie Ie.store ds π') :
    (twos (ds.map (wireRound l)) : List (Move sigU sigU)) ∈ (expEnvD P l).toStrategy := by
  obtain ⟨li, lc, hli, H, X⟩ :=
    LinkedSessionIR.expRunT_mem hl.expGood hIe hrun hIe.1.choose_spec.ok
  have h := expEnv_rounds hIe hli H X
  rw [← expObs_plays] at h
  exact h

theorem inf_expEnvD (P : Profile) (l : Linked2) :
    (expEnvD P l).inf = (Linked2.expObs (impSemD P) l).inf :=
  congrArg DObs.inf (obs_ext 0 _ _)

/-- **The exporter serving the import calls of infinitely many rounds, forever** (deterministic
profiles, under `Linked2.Adequate`): the call lists `T k`, served one after another along one
run from the exporter's store, when there are infinitely many calls, are an infinite play of
its environment. -/
theorem exp_env_inf_cat {o : GrowOracle} (hl : l.Adequate) {Ie : SInst}
    (hIe : l.exp.mod.IsInst Ie) {T : ℕ → List (Round (sigN l.imp.imports.length))}
    {π : ℕ → Store Nat} (h0 : π 0 = Ie.store)
    (hT : ∀ k, Linked2.ExpRunT (profile o) l Ie (π k) (T k) (π (k + 1)))
    (hu : Silmaril.Games.Chain.Unbounded fun n => (twos ((catC T n).map (wireRound l)) : List (Move sigU sigU))) :
    Silmaril.Games.Chain.lim (fun n => (twos ((catC T n).map (wireRound l)) : List (Move sigU sigU))) ∈
      (expEnvD (profile o) l).inf := by
  have hu' : ∀ k, ∃ n, k < (catC T n).length := fun k => by
    obtain ⟨n, hn⟩ := hu (2 * k + 2)
    refine ⟨n, ?_⟩
    rw [length_twos, List.length_map] at hn
    omega
  obtain ⟨ζ, hζ⟩ := exists_flat_stream T hu'
  have hrun : ∀ n, Linked2.ExpRunT (profile o) l Ie Ie.store (catC T n) (π n) := fun n =>
    h0 ▸ expRunT_catC hT n
  have hpre : ∀ n, ∃ π', Linked2.ExpRunT (profile o) l Ie Ie.store
      (streamTake (fun k => [ζ k]) n).flatten π' := by
    intro n
    obtain ⟨m, hm⟩ := hu' n
    rw [flatten_streamTake_single, hζ m n hm.le]
    have h := hrun m
    rw [← List.take_append_drop n (catC T m)] at h
    obtain ⟨π₁, h₁, -⟩ := expRunT_split _ _ h
    exact ⟨π₁, h₁⟩
  obtain ⟨S, hS0, hS⟩ := exists_expRunT_stream (fun k => [ζ k]) hpre
  have hE := exp_env_inf hl hIe hS0 hS
  rw [inf_expEnvD]
  convert hE using 1
  refine lim_eq_of_cofinal (fun n => ⟨(catC T n).length, ?_⟩) (fun m => ?_)
  · rw [cch_mk0, streamTake_map (wireRound l) ζ, hζ n _ le_rfl, List.take_length]
  · obtain ⟨n, hn⟩ := hu' m
    refine ⟨n, ?_⟩
    rw [cch_mk0, streamTake_map (wireRound l) ζ, hζ n m hn.le]
    exact twos_prefix (prefix_map _ (List.take_prefix _ _))

end Exp

/-! ## Infinitely many linked rounds -/

section Build

variable {o : GrowOracle} {l : Linked2}

theorem flatMap_wired_catC {Ii : SInst} (D : ℕ → LayerI l.imp Ii)
    {T : ℕ → List (Round (sigN l.imp.imports.length))} (hT : ∀ k, (D k).dss.flatten = T k) :
    ∀ n, (streamTake (fun k => (D k).wired) n).flatMap (·.cs) = (catC T n).map (wireRound l)
  | 0 => rfl
  | n + 1 => by
    rw [streamTake_snoc, List.flatMap_append, flatMap_wired_catC D hT n, catC_succ,
      List.map_append, List.flatMap_singleton]
    show _ ++ ((D n).dss.flatten.map (wireRound l)) = _
    rw [hT n]

/-- **Infinitely many linked rounds are an infinite play of the IR** (deterministic profiles,
under `Linked2.Adequate`): rounds `R k` of the importer, played one after another from its
store, whose import calls are served by the exporter one after another along one run from its
store, are an infinite play of `l.toComp.denD (impSemD (profile o))`. -/
theorem inf_denD_build (hl : l.Adequate) {Ie Ii : SInst} (hIe : l.exp.mod.IsInst Ie)
    (hIi : l.imp.mod.IsInst Ii) {R : ℕ → Linked2.SessRound l Ii} (hR : ∀ k, (R k).Ok)
    {u π : ℕ → Store Nat} (hu0 : u 0 = Ii.store) (hπ0 : π 0 = Ie.store)
    (hp : ∀ k, Ii.Path (profile o) (.idle (u k)) (R k).instMoves (.idle (u (k + 1))))
    (hr : ∀ k, Linked2.ExpRunT (profile o) l Ie (π k) (R k).dss.flatten (π (k + 1))) :
    Silmaril.Games.Chain.lim (fun n => (streamTake R n).flatMap Linked2.SessRound.linkMoves) ∈
      (l.toComp.denD (impSemD (profile o))).inf := by
  -- the layers of each round
  have hlay : ∀ k, ∃ D : LayerI l.imp Ii, D.Ok hIi ∧ D.r = LinkedSessionIR.SessRound.r (R k) ∧
      D.u = LinkedSessionIR.SessRound.u (R k) := fun k => by
    obtain ⟨xs, hxl, h₁, h₂, hrel⟩ := hR k
    exact layer_of hl.impGood hIi (j := (R k).j) (vs := (R k).vs)
      ⟨xs, (R k).dss, hxl, h₁, h₂, hrel, rfl⟩
  choose D hD hDr hDu using hlay
  have hdss : ∀ k, (D k).dss.flatten = (R k).dss.flatten := fun k => congrArg CRound.cs (hDu k)
  -- the importer's instance and IR
  have hpI : ∀ k, Ii.Path (profile o) (.idle (u k)) (cplay [(D k).r]) (.idle (u (k + 1))) :=
    fun k => by
      have e := LinkedSessionIR.cplay_r [R k]
      simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
        List.append_nil] at e
      rw [hDr k, e]
      exact hp k
  have hbot := inf_spullD_cpl hpI
  rw [hu0] at hbot
  have hv := imp_inf_cpl hIi hD hbot
  -- the importer's node
  have hwire : ∀ k, ∀ x ∈ (D k).dss.flatten,
      ∃ w : Fin l.exp.exports.length, l.wire[x.1.1.val]? = some w.val :=
    fun k x hx => LinkedSessionIR.expRunT_wire (hr k) x (by rw [← hdss k]; exact hx)
  have hN : (cch fun k => LayerI.wiredN (D k)).lim ∈
      (Node.denD (impSemD (profile o)) l.exp.exports.length l.impNode).inf := by
    have h := inf_below_cpl (oneCall_implsH _ _) (fun k => (.cons (hrounds_wire (hwire k)) .nil :
      HB (implsH l.exp.exports.length (wireArgs l)) [(D k).l₆] [LayerI.wiredN (D k)])) hv
    rw [Linked2.impNode, Node.denD]
    exact h
  -- the pairing and `splitH`
  have h₅ := inf_pair_cpl (DStrategy.id sigU) hN
  have h₄ := inf_top_cpl (h := splitH l.exp.exports.length) (U := fun k => (D k).wired)
    (fun k => .call (h := splitH _) (splitH_shift' _ _ _) rfl .nil) h₅
  -- the exporter's environment serves the import calls
  have hflat := flatMap_wired_catC D hdss
  have hser : serveC (E := sigU) (fun k => (D k).wired) =
      fun n => twos ((catC (fun k => (R k).dss.flatten) n).map (wireRound l)) :=
    funext fun n => by rw [serveC, hflat n]
  have hE := inf_comp_serve (σ := expEnvD (profile o) l) h₄
    (fun n => by
      rw [hser]
      exact exp_env_mem hl hIe (hπ0 ▸ expRunT_catC hr n))
    (fun hu => by
      rw [hser] at hu ⊢
      exact exp_env_inf_cat hl hIe hπ0 hr hu)
  -- the linked export handler
  have HE : ∀ k, HC (exportsH (l.exp.exports.length + l.imp.exports.length) l.toComp.exports)
      [LayerI.env (D k)] [((D k).wired).hide (E := sigU)] := fun k =>
    .call (h := exportsH _ _) (q := ((D k).j.val, .vals (D k).vs))
      (q' := (l.exp.exports.length + (D k).j.val, .vals (D k).vs)) (k := fun n => .pure n)
      (exportsH_toCompL l (D k).j.isLt _) rfl .nil
  have hU : (cch fun k => LayerI.env (D k)).lim ∈ (l.toComp.denUD (impSemD (profile o))).inf := by
    have h := inf_top_cpl HE hE
    rw [Linked2.toComp_eq, Comp.denUD]
    simp only [List.length_nil, denNodesD, Nat.zero_add, envAfter_link, expNode_width]
    exact h
  -- `widenH 0` and `narrowH`
  have hW := inf_below_cpl (oneCall_widenH 0)
    (fun k => (.cons .nil .nil : HB (widenH 0) [LayerI.env (D k)] [LayerI.top (D k)])) hU
  have hT := inf_top_cpl (h := narrowH l.toComp.exports.length)
    (U := fun k => Linked2.linkRound l (D k).u)
    (fun k => .call (h := narrowH _) rfl rfl .nil) hW
  have e : (cch fun k => Linked2.linkRound l (D k).u) =
      fun n => (streamTake R n).flatMap Linked2.SessRound.linkMoves := funext fun n => by
    simp only [cch, hDu]
    rw [streamTake_map (Linked2.linkRound l) (fun k => LinkedSessionIR.SessRound.u (R k)),
      streamTake_map LinkedSessionIR.SessRound.u R, LinkedSessionIR.cplay_link]
  rw [e] at hT
  exact hT

/-! ## From the coherent rounds of the linked triple -/

theorem sessMoves_append :
    ∀ (c₁ : List (Fin l.imp.exports.length × List IVal)) (o₁ : List (Option (List IVal)))
      (c₂ : List (Fin l.imp.exports.length × List IVal)) (o₂ : List (Option (List IVal))),
      c₁.length = o₁.length →
      Linked2.sessMoves l (c₁ ++ c₂) (o₁ ++ o₂) =
        Linked2.sessMoves l c₁ o₁ ++ Linked2.sessMoves l c₂ o₂
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | (j, vs) :: c₁, o :: o₁, c₂, o₂, h => by
    simp only [List.cons_append, Linked2.sessMoves, List.length_cons, Nat.add_right_cancel_iff]
      at h ⊢
    rw [sessMoves_append c₁ o₁ c₂ o₂ h]

theorem linkMoves_eq {Ii : SInst} (d : Linked2.SessRound l Ii) {o : Option (List IVal)}
    (h : d.ans = o.map .vals) : d.linkMoves = Linked2.sessMoves l [(d.j, d.vs)] [o] := by
  simp only [Linked2.SessRound.linkMoves, Linked2.sessMoves, h]

theorem sessMoves_streamTake {Ii : SInst} {R : ℕ → Linked2.SessRound l Ii}
    {a : ℕ → Fin l.imp.exports.length × List IVal} {out : ℕ → Option (List IVal)}
    (ha : ∀ k, a k = ((R k).j, (R k).vs)) (hans : ∀ k, (R k).ans = (out k).map .vals) :
    ∀ n, (streamTake R n).flatMap Linked2.SessRound.linkMoves =
      Linked2.sessMoves l (streamTake a n) (streamTake out n)
  | 0 => rfl
  | n + 1 => by
    rw [streamTake_snoc, streamTake_snoc, streamTake_snoc, List.flatMap_append,
      sessMoves_streamTake ha hans n, sessMoves_append _ _ _ _ (by simp), List.flatMap_singleton,
      linkMoves_eq _ (hans n), ha n]

/-- **The coherent rounds of the linked triple are an infinite play of the IR** (deterministic
profiles, under `Linked2.Adequate`, typed calls): the typed calls `a` answered by `out`, as
coherent rounds of `Linked2.compTripleS` from the instances' stores, are the infinite play
`Linked2.sessInfPlay l a out` of `l.toComp.denD (impSemD (profile o))`. -/
theorem inf_of_infRounds (hl : l.Adequate) {Ie Ii : SInst} (hIe : l.exp.mod.IsInst Ie)
    (hIi : l.imp.mod.IsInst Ii) (a : ℕ → Fin l.imp.exports.length × List IVal)
    (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList l.imp.exports[(a k).1].ty.params (a k).2 = true)
    {s : ℕ → Store Nat × Store Nat}
    (hs : InfRounds (Linked2.compTripleS (profile o) l Ie Ii) (Ie.store, Ii.store)
      (fun k => (((a k).1 : Nat), Payload.vals (a k).2)) (fun k => ([], outAns (out k))) s) :
    l.sessInfPlay a out ∈ (l.toComp.denD (impSemD (profile o))).inf := by
  have hspec : ∀ k, Linked2.SessSpec (profile o) l Ie Ii (s k).2 (s k).1 [((a k).1, (a k).2)]
      [out k] (s (k + 1)).2 (s (k + 1)).1 := fun k =>
    LinkedSessionObs.spec_stepL (hs.step k) (LinkedSessionEquiv.typedQ_typed (ht k))
  choose R hRj hRv hRok hRp hRr hRans using fun k => LinkedSessionObs.sessSpec_single (hspec k)
  have h₀ := hs.zero
  have hb := inf_denD_build hl hIe hIi hRok (u := fun k => (s k).2) (π := fun k => (s k).1)
    (by rw [h₀]) (by rw [h₀]) hRp hRr
  have e : (fun n => (streamTake R n).flatMap Linked2.SessRound.linkMoves) =
      fun n => Linked2.sessMoves l (streamTake a n) (streamTake out n) :=
    funext (sessMoves_streamTake (fun k => by rw [hRj k, hRv k]) hRans)
  rw [e] at hb
  exact hb

end Build

/-! ## The full injection -/

section Inj

variable {o : GrowOracle} {prof : ProfileKind}

theorem typedCalls_castL {l l' : Linked2} (len : l.imp.exports.length = l'.imp.exports.length)
    (hty : ∀ j : Fin l.imp.exports.length, l'.imp.exports[Fin.cast len j].ty = l.imp.exports[j].ty)
    {calls : List (Fin l.imp.exports.length × List IVal)} (ht : SimpleI.TypedCalls l.imp calls) :
    SimpleI.TypedCalls l'.imp (Linked2.castCalls len calls) := by
  intro q hq
  obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
  show ValTy.checkList l'.imp.exports[Fin.cast len q'.1].ty.params q'.2 = true
  rw [hty]
  exact ht q' hq'

theorem typed_castStreamL {l l' : Linked2} (len : l.imp.exports.length = l'.imp.exports.length)
    (hty : ∀ j : Fin l.imp.exports.length, l'.imp.exports[Fin.cast len j].ty = l.imp.exports[j].ty)
    {a : ℕ → Fin l.imp.exports.length × List IVal}
    (ht : ∀ k, ValTy.checkList l.imp.exports[(a k).1].ty.params (a k).2 = true) :
    ∀ k, ValTy.checkList l'.imp.exports[(Linked2.castStream len a k).1].ty.params
      (Linked2.castStream len a k).2 = true := fun k => by
  show ValTy.checkList l'.imp.exports[Fin.cast len (a k).1].ty.params (a k).2 = true
  rw [hty]
  exact ht k

theorem sessDivs_length {P : Profile} {l : Linked2}
    {calls : List (Fin l.imp.exports.length × List IVal)} {j : Fin l.imp.exports.length}
    {vs : List IVal} {outs : List (Option (List IVal))}
    (h : outs ∈ Linked2.sessDivs P l calls j vs) : calls.length = outs.length := by
  obtain ⟨_, _, _, _, _, _, hS, _⟩ := h
  exact LinkedSessionRef.sessSpec_length hS

/-- **The full injection, from the divergence and infinite-play iffs** (deterministic profiles):
given, for adequate linked components, the IR divergences after typed sessions as the
specification's (`Linked2.sessDivs`) and the infinite IR plays of typed streams as the productive
executions (under one host), `Linked2.RefSessEquivFull` is the same export types and the same
finite plays, divergences and infinite plays of the IR. -/
theorem refSessEquivFull_iff_of {l l' : Linked2} (hl : l.Adequate) (hl' : l'.Adequate)
    (hdiv : ∀ {m : Linked2}, m.Adequate →
      ∀ {calls : List (Fin m.imp.exports.length × List IVal)} {outs : List (Option (List IVal))}
        {j : Fin m.imp.exports.length} {vs : List IVal}, SimpleI.TypedCalls m.imp calls →
        calls.length = outs.length → ValTy.checkList m.imp.exports[j].ty.params vs = true →
        (Linked2.sessMoves m calls outs ++ [.inr (.ask (m.topQ j vs))] ∈
            (m.toComp.denD (impSemD (profile o))).div ↔
          outs ∈ Linked2.sessDivs (profile o) m calls j vs))
    (hinf : ∀ {m : Linked2}, m.Adequate →
      ∀ (a : ℕ → Fin m.imp.exports.length × List IVal) (out : ℕ → Option (List IVal)),
        (∀ k, ValTy.checkList m.imp.exports[(a k).1].ty.params (a k).2 = true) →
        (m.sessInfPlay a out ∈ (m.toComp.denD (impSemD (profile o))).inf ↔
          Linked2.RefSessProd (profile o) prof m
            (Silmaril.Wasm.Component.Canon.HostImpl.none (σ := PUnit)) PUnit.unit a out)) :
    Linked2.RefSessEquivFull (profile o) prof l l' ↔ Linked2.SameTypes l l' ∧
      pubPlays (l.toComp.denD (impSemD (profile o))).toStrategy =
        pubPlays (l'.toComp.denD (impSemD (profile o))).toStrategy ∧
      Linked2.IRDivEq (profile o) l l' ∧ Linked2.IRInfEq (profile o) l l' := by
  constructor
  · intro h
    obtain ⟨hty, hpub⟩ := (Linked2.sessEquiv_iffD (profile o) prof hl hl').1 h.toRefSessEquiv
    obtain ⟨_, hdv⟩ := (Linked2.RefSessEquivD.iff_sessDivs hl hl').1
      ((Linked2.RefSessEquivFull.iff_refSessEquivD (prof := prof) o hl hl').1 h)
    refine ⟨hty, hpub, ⟨h.len, fun calls outs j vs ht hlen hck => ?_⟩,
      ⟨h.len, fun a out ht => ?_⟩⟩
    · rw [hdiv hl ht hlen hck, hdiv hl' (typedCalls_castL h.len h.ty ht)
        (by simpa [Linked2.castCalls] using hlen) (by rw [h.ty]; exact hck), hdv calls j vs ht hck]
    · rw [hinf hl a out ht, hinf hl' _ out (typed_castStreamL h.len h.ty ht)]
      exact h.prod a out ht _ _
  · rintro ⟨hty, hpub, ⟨len, hdv⟩, -⟩
    have h := (Linked2.sessEquiv_iffD (profile o) prof hl hl').2 ⟨hty, hpub⟩
    refine (Linked2.RefSessEquivFull.iff_refSessEquivD o hl hl').2
      ((Linked2.RefSessEquivD.iff_sessDivs hl hl').2
        ⟨h, fun calls j vs ht hck => Set.ext fun outs => ?_⟩)
    by_cases hlen : calls.length = outs.length
    · rw [← hdiv hl ht hlen hck, ← hdiv hl' (typedCalls_castL h.len h.ty ht)
        (by simpa [Linked2.castCalls] using hlen) (by rw [h.ty]; exact hck)]
      exact hdv calls outs j vs ht hlen hck
    · refine ⟨fun hm => absurd (sessDivs_length hm) hlen, fun hm => absurd ?_ hlen⟩
      simpa [Linked2.castCalls] using sessDivs_length hm

end Inj

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq
