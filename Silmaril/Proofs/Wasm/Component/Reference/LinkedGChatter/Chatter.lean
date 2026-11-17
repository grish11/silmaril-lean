module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGChatter.Coherent

/-!
# Chatter of a linked component with an abstract exporter, read back at deterministic profiles

`chatterReadBack_profileG`: at `profile o`, for an exporter meeting `ExpSpec.Adeq` and
`ExpSpec.AdeqIC`, an IR divergence from chatter between the importer's node and the exporter's
environment (`chatterSrc`) after typed rounds `L` and a typed question is a session of
`g.toExp Ii` followed by a round of chatter (`LinkedG.Chatter`). This is
`LinkedSessionDAdeq.chatterReadBack_profile` over the exporter interface:

* **Stages** (`stage_readbackG`, the waiting part of `roundDivA_of_envDiv`): cutting the shared
  moves just after one of the node's calls (`chatter_stage`) gives a waiting play of the node
  layer, read back to the rounds `L`, the importer's core rounds and its core import calls so far;
* **the stages cohere** (`rounds_eqG`, `pend_prefixG`): at `profile o` the core rounds and the
  pending question are the same at every stage and the core calls grow, so they have limit
  streams (`exists_limit`);
* **the exporter serves them along one run** (`exp_plays_streamG`, by `AdeqIC`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGChatter

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Games.Abstract (streamTake)
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq
open Silmaril.Proofs.Wasm.Component.Reference.LinkedG
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

/-! ## The read-back of a stage -/

/-- **A stage of the exporter's environment and the node above it, read back** (every profile,
importer `Good` and `IsInst`, `WireTy`, typed rounds and a typed pending call): below the linked
export handler of the rounds `M` and the pending call, a play `tN` of the node layer waiting on
the call `m`, interacting with a play `sA` of the exporter's environment, is the node's rounds
`cl` (those of `M`) and the pending round with the lower calls `csN`; the environment served
them; and the importer's core instance plays rounds `ri` read back from `cl`, then the lowered
question `f` after core import calls `ics` related to `csN`, waiting on a call `e` that lifts. -/
theorem stage_readbackG {P : Profile} {g : LinkedG} {Ii : SInst} (hi : g.imp.Good)
    (hIi : g.imp.mod.IsInst Ii) (hw : g.WireTy) {M : List URound} (hM : ∀ m ∈ M, TopG g m)
    {j : Fin g.imp.exports.length} {vs : List IVal}
    (hck : ValTy.checkList g.imp.exports[j].ty.params vs = true)
    {d x : List (Move sigU sigU)} (h₃ : Zip d x (uMoves M ++ [.inr (.ask (j.val, .vals vs))]))
    (hx : x ∈ Strategy.ofHandler (exportsH (envAfter 0 [g.expNode, g.impNode]) g.toComp.exports))
    {sA tN : List (Move sigU sigU)} {gd m : sigU.Op} (hzA : Zip sA tN d) (hsA : NoInl sA)
    (htN : tN ∈ (DStrategy.extTop g.expNode.width
      (Node.denD (impSemD P) g.expNode.width g.impNode)).toStrategy)
    (htw : Path .idle tN (.wait gd m)) :
    ∃ (cl : List (CRound sigU sigU)) (csN : List (Round sigU)) (ri : List (CRound Ii.E Ii.F))
      (f : Ii.F.Op) (ics : List (Round Ii.E))
      (dss : List (List (Round (sigN g.imp.imports.length)))) (e : Ii.E.Op) (s' : Store Nat)
      (t' : Silmaril.Wasm.SingleThreaded.Thread),
      tN = rplay cl (g.exp.comp.exports.length + j.val, .vals vs) csN ++ [.inl (.ask m)] ∧
      sA = twos (cl.flatMap (·.cs) ++ csN) ++ [.inr (.ask m)] ∧
      List.Forall₂ (fun c m => CRound.toRound c = shiftG g m) cl M ∧
      List.Forall₂ (RdNG g Ii) ri cl ∧
      Ii.Path P (.idle Ii.store) (rplay ri f ics ++ [.inl (.ask e)]) (.waiting f s' t' e) ∧
      f.1.val = g.imp.exports[j].core ∧
      f.2.1 = (lowerArgs g.imp.exports[j].ty.params vs).map Silmaril.Wasm.SingleThreaded.ofFlat ∧
      List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel g.imp Ii) ics dss ∧
      csN = dss.flatten.map (wireRoundG g) ∧ LiftsI g.imp Ii e := by
  obtain ⟨cl, csP, rfl⟩ := exists_wplay htw
  obtain ⟨rfl, rfl⟩ := serve_wait hsA hzA
  -- the linked export handler
  obtain ⟨hLd, rfl⟩ := top_divU hM h₃ rfl hx
  have K : List.Forall₂ (fun c m => CRound.toRound c = shiftG g m) cl M :=
    forall₂_of_map_eq hLd
  have hge : ∀ r ∈ cl, g.exp.comp.exports.length ≤ r.q.1 := by
    intro r hr
    obtain ⟨m, hm⟩ := forall₂_mem_left K r hr
    have h₁ : r.q = (g.exp.comp.exports.length + m.1.1, m.1.2) := congrArg Sigma.fst hm
    rw [h₁]
    exact Nat.le_add_right _ _
  -- `splitH` and the pairing
  obtain ⟨a, ha, b, hb, hz₂⟩ := htN
  rw [expNode_widthG] at hb ha
  obtain ⟨yb, hyb⟩ := Strategy.mem_ofHandler.mp hb
  obtain ⟨xa, hxa⟩ := ((Strategy.id sigU).pair
    (Node.denD (impSemD P) g.exp.comp.exports.length g.impNode).toStrategy).legal ha
  obtain ⟨f₂, ha₂⟩ := wait_of_zip_top hz₂ hxa hyb (path_wplay _ _ _ _)
  obtain ⟨low₁, k₁, H₁, hk₁, rfl⟩ := hc_zip_wait (oneShot_splitH _) ha₂ hyb hz₂
  rw [hc_splitH_inv H₁ hge] at ha
  simp only [splitH, Nat.not_lt.mpr (Nat.le_add_right _ _), ↓reduceIte] at hk₁
  obtain ⟨hk₁, -⟩ := Prog.call.inj hk₁
  subst hk₁
  obtain ⟨-, -, haN⟩ := ha
  rw [halves_wplay_inr] at haN
  -- the importer's node forwards the pending import call
  rw [toStrategy_node_denD, forget_impSemD, LinkedG.impNode, Node.den] at haN
  obtain ⟨uN, huN, vB, hvB, hzN⟩ := haN
  obtain ⟨yN, hyN⟩ := Strategy.mem_ofHandler.mp huN
  obtain ⟨xv, hxv⟩ := (g.imp.toComp.denU (impSem P)).legal hvB
  obtain ⟨mB, hvw⟩ := wait_of_zip_below hzN hyN hxv (path_wplay _ _ _ _)
  obtain ⟨up₂, cs₂, rfl⟩ := exists_wplay hvw
  obtain ⟨low₂, csP', kN, H₂, H₂', hkN, he₂⟩ :=
    hb_zip_wait (oneShot_implsH _ _) hyN (path_wplay _ _ _ _) hzN
  obtain ⟨hlow₂, -, rfl, -⟩ := rplay_snoc_inj he₂
  subst hlow₂
  have G₂ : List.Forall₂ (fun x c => HBR (implsH g.exp.comp.exports.length (wireArgsG g)) x
      (downBy g.exp.comp.exports.length c)) up₂ cl := forall₂_map_right (hb_forall₂ H₂)
  have htop := topI_of hM K G₂
  -- the importer's IR, waiting
  rw [Nat.add_sub_cancel_left] at hvB
  obtain ⟨ri, f, ics, dss, e, s', t', nm, ft, ws, F, hpath, hf₁, hf₂, hF, hcs, hft, hlw,
    -⟩ := imp_wait_readback hi hIi htop hck hvB
  rw [hcs] at H₂'
  have hcsP := hrounds_wire_invG hw dss.flatten csP H₂'
  exact ⟨cl, csP, ri, f, ics, dss, e, s', t', rfl, rfl, K, forall₂_comp F G₂, hpath, hf₁, hf₂,
    hF, hcsP, nm, ft, ws, hft, hlw⟩

/-! ## The read-back of chatter -/

theorem impRel_length_le {c : SimpleI} {I : SInst}
    {ics : List (Σ e : I.E.Op, I.E.Ar e)} {dss : List (List (Round (sigN c.imports.length)))}
    (h : List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel c I) ics dss) :
    dss.flatten.length ≤ ics.length :=
  flatten_length_le h

/-- **Chatter read back at a deterministic profile** (exporter meeting `Adeq` and `AdeqIC`,
importer `Good` and `IsInst`, `WireTy`). -/
theorem chatterReadBack_profileG (o : GrowOracle) {g : LinkedG} {Ii : SInst}
    (he : g.exp.Adeq (profile o)) (hIC : g.exp.AdeqIC (profile o)) (hi : g.imp.Good)
    (hIi : g.imp.mod.IsInst Ii) (hw : g.WireTy) :
    LinkedG.Task.ChatterReadBack (profile o) g Ii := by
  intro L q hL hq h
  obtain ⟨j, vs, rfl, hck⟩ := typedQ_of hq
  have hM : ∀ m ∈ L, TopG g m := fun m hm => typedG_of (hL m hm)
  obtain ⟨d, x, h₃, hd, hx⟩ := h
  obtain ⟨I, hI, Lc, hLc, s₀, c₀, hz₀, hleg, hside, hid, hwk⟩ := hd
  -- the infinite plays of the exporter's environment and of the importer's node
  have hE : g.expObs (impSemD (profile o)) = DObs.of (DStrategy.ext 0
      (DStrategy.ofHandler (maskH 0)) (Node.denD (impSemD (profile o)) 0 g.expNode)) :=
    (obs_ext _ _ _).symm
  have hI' : I ∈ (DStrategy.ext 0 (DStrategy.ofHandler (maskH 0))
      (Node.denD (impSemD (profile o)) 0 g.expNode)).inf := by
    rw [hE] at hI
    exact hI
  have hIinf := (DStrategy.ext 0 (DStrategy.ofHandler (maskH 0))
    (Node.denD (impSemD (profile o)) 0 g.expNode)).inf_isInf hI'
  have hIpl : ∀ y ∈ I, y ∈ (g.expObs (impSemD (profile o))).plays := by
    intro y hy
    rw [hE]
    exact (DStrategy.ext 0 (DStrategy.ofHandler (maskH 0))
      (Node.denD (impSemD (profile o)) 0 g.expNode)).inf_sub hI' hy
  have hLinf := (Node.denD (impSemD (profile o)) g.expNode.width g.impNode).inf_isInf hLc
  have hLpl := (Node.denD (impSemD (profile o)) g.expNode.width g.impNode).inf_sub hLc
  have hnoinl : ∀ y ∈ (g.expObs (impSemD (profile o))).plays, NoInl y := by
    rw [expObs_playsG]
    exact noInl_comp (noInl_ofHandler_pure pure_maskH0)
  -- the shared moves, as one stream
  choose wk hwk using hwk
  have hinr : Function.Injective (Sum.inr : Ev sigU → Move sigU sigU) := Sum.inr_injective
  have hcomp : ∀ a b, wk a <+: wk b ∨ wk b <+: wk a := by
    intro a b
    rcases hIinf.total (hwk a).2.1 (hwk b).2.1 with hab | hab
    · exact .inl (prefix_of_map_prefix hinr ((List.prefix_append_right_inj _).mp hab))
    · exact .inr (prefix_of_map_prefix hinr ((List.prefix_append_right_inj _).mp hab))
  obtain ⟨W, hW⟩ := exists_limit wk hcomp fun k => ⟨k + 1, by have := (hwk (k + 1)).1; omega⟩
  have hWpre : ∀ n, streamTake W n <+: wk n := fun n => by
    rw [streamTake_eq_take (hW n) (hwk n).1]
    exact List.take_prefix _ _
  have hIn : ∀ n, s₀ ++ (streamTake W n).map .inr ∈ I := fun n =>
    hIinf.of_prefix (hwk n).2.1 ((List.prefix_append_right_inj _).mpr (prefix_map _ (hWpre n)))
  have hLn : ∀ n, (Split.halves false (c₀.map (splitRoute g.expNode.width))).2 ++
      (streamTake W n).map .inl ∈
        (Node.denD (impSemD (profile o)) g.expNode.width g.impNode).toStrategy := fun n =>
    hLpl (hLinf.of_prefix (hwk n).2.2
      ((List.prefix_append_right_inj _).mpr (prefix_map _ (hWpre n))))
  -- the node calls at least every other move
  have halt : ∀ i, (∃ m, W i = .ask m) ∨ (∃ m, W (i + 1) = .ask m) := by
    intro i
    obtain ⟨y, hy⟩ := (Node.denD (impSemD (profile o)) g.expNode.width
      g.impNode).toStrategy.legal (hLn (i + 1 + 1))
    have e : (Split.halves false (c₀.map (splitRoute g.expNode.width))).2 ++
        (streamTake W (i + 1 + 1)).map .inl =
          ((Split.halves false (c₀.map (splitRoute g.expNode.width))).2 ++
            (streamTake W i).map .inl) ++ [.inl (W i), .inl (W (i + 1))] := by
      rw [streamTake_snoc, streamTake_snoc]
      simp
    rw [e] at hy
    obtain ⟨y₀, -, hy₂⟩ := Path.of_append hy
    rcases hWi : W i with m | ⟨m, r⟩
    · exact .inl ⟨m, rfl⟩
    · rw [hWi] at hy₂
      cases hy₂ with
      | cons s₁ hy₃ =>
        cases s₁
        rcases hWi' : W (i + 1) with m' | ⟨m', r'⟩
        · exact .inr ⟨m', rfl⟩
        · rw [hWi'] at hy₃
          cases hy₃ with
          | cons s₂ _ => cases s₂
  have hτ : ∀ n, ∃ k, 2 * n ≤ k ∧ k ≤ 2 * n + 1 ∧ ∃ m, W k = .ask m := by
    intro n
    rcases halt (2 * n) with hm | hm
    · exact ⟨2 * n, le_rfl, by omega, hm⟩
    · exact ⟨2 * n + 1, by omega, le_rfl, hm⟩
  choose τ hτ₁ hτ₂ mk hmk using hτ
  have hX : ∀ n, streamTake W (τ n + 1) = streamTake W (τ n) ++ [Ev.ask (mk n)] := fun n => by
    rw [streamTake_snoc, hmk]
  have hsAn : ∀ n, s₀ ++ (streamTake W (τ n) ++ [Ev.ask (mk n)]).map .inr ∈ I := fun n => by
    rw [← hX]
    exact hIn _
  -- the stages, read back
  have hstage : ∀ n, ∃ (cl : List (CRound sigU sigU)) (csN : List (Round sigU))
      (ri : List (CRound Ii.E Ii.F)) (f : Ii.F.Op) (ics : List (Round Ii.E))
      (dss : List (List (Round (sigN g.imp.imports.length)))) (e : Ii.E.Op) (s' : Store Nat)
      (t' : Silmaril.Wasm.SingleThreaded.Thread),
      c₀ ++ (streamTake W (τ n) ++ [Ev.ask (mk n)]).map .inl =
        rplay cl (g.exp.comp.exports.length + j.val, .vals vs) csN ++ [.inl (.ask (mk n))] ∧
      s₀ ++ (streamTake W (τ n) ++ [Ev.ask (mk n)]).map .inr =
        twos (cl.flatMap (·.cs) ++ csN) ++ [.inr (.ask (mk n))] ∧
      List.Forall₂ (fun c m => CRound.toRound c = shiftG g m) cl L ∧
      List.Forall₂ (RdNG g Ii) ri cl ∧
      Ii.Path (profile o) (.idle Ii.store) (rplay ri f ics ++ [.inl (.ask e)])
        (.waiting f s' t' e) ∧
      f.1.val = g.imp.exports[j].core ∧
      f.2.1 = (lowerArgs g.imp.exports[j].ty.params vs).map Silmaril.Wasm.SingleThreaded.ofFlat ∧
      List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel g.imp Ii) ics dss ∧
      csN = dss.flatten.map (wireRoundG g) ∧ LiftsI g.imp Ii e := by
    intro n
    have hNn := hLn (τ n + 1)
    rw [hX] at hNn
    obtain ⟨htN, gd, htw⟩ := chatter_stage hleg hside hid hNn
    exact stage_readbackG hi hIi hw hM hck h₃ hx (zip_hidden hz₀ _)
      (hnoinl _ (hIpl _ (hsAn n))) htN htw
  choose cl csN ri f ics dss e s' t' hT hS hK hFG hpath hf₁ hf₂ hF hcsN hlift using hstage
  -- the node's rounds are the same at every stage, and its calls grow
  have hcl : ∀ n n', n ≤ n' → cl n = cl n' ∧ csN n <+: csN n' := by
    intro n n' hnn
    have hτle : τ n + 1 ≤ τ n' + 1 := by
      rcases Nat.eq_or_lt_of_le hnn with rfl | hlt
      · exact le_rfl
      · have := hτ₂ n
        have := hτ₁ n'
        omega
    obtain ⟨Y, hY⟩ := streamTake_prefix W hτle
    have e₁ := hT n'
    rw [← hX n', ← hY, List.map_append, ← List.append_assoc, hX n, hT n] at e₁
    obtain ⟨h₁, -, h₂⟩ := rplay_ext_inl e₁
    exact ⟨h₁, h₂⟩
  have hcl0 : ∀ n, cl n = cl 0 := fun n => ((hcl 0 n (Nat.zero_le n)).1).symm
  -- the importer's core rounds and question are the same at every stage
  have hcplay : ∀ n, ∃ z, Ii.Path (profile o) (.idle Ii.store) (cplay (ri n)) z := fun n => by
    have hp := hpath n
    simp only [rplay, List.append_assoc] at hp
    obtain ⟨z, hz, -⟩ := path_split_inst hp
    exact ⟨z, hz⟩
  have hri : ∀ n, ri n = ri 0 := fun n => by
    obtain ⟨z, hz⟩ := hcplay n
    obtain ⟨z', hz'⟩ := hcplay 0
    have F := hFG n
    rw [hcl0 n] at F
    exact rounds_eqG hw F (hFG 0) hz hz'
  have hf : ∀ n, f n = f 0 := fun n =>
    fop_ext ((hf₁ n).trans (hf₁ 0).symm) ((hf₂ n).trans (hf₂ 0).symm)
  have hpath' : ∀ n, Ii.Path (profile o) (.idle Ii.store)
      (rplay (ri 0) (f 0) (ics n) ++ [.inl (.ask (e n))]) (.waiting (f 0) (s' n) (t' n) (e n)) :=
    fun n => by
      have hp := hpath n
      rw [hri n, hf n] at hp
      exact hp
  -- its core calls grow
  have hics : ∀ n n', n ≤ n' → ics n <+: ics n' ∧ dss n <+: dss n' := by
    intro n n' hnn
    refine pend_prefixG (hpath' n) (hpath' n') (hlift n') (hF n) (hF n') ?_
    rw [← hcsN n, ← hcsN n']
    exact (hcl n n' hnn).2
  have hunb : ∀ k, ∃ n, k < (ics n).length := by
    intro k
    obtain ⟨n, hn⟩ : ∃ n, n = k + (cplay (cl 0)).length + 1 := ⟨_, rfl⟩
    refine ⟨n, ?_⟩
    have e₁ := congrArg List.length (hT n)
    rw [hcl0 n] at e₁
    simp only [List.length_append, List.length_map, length_streamTake, List.length_singleton,
      length_rplay] at e₁
    have e₂ : (csN n).length ≤ (ics n).length := by
      rw [hcsN, List.length_map]
      exact impRel_length_le (hF _)
    have := hτ₁ n
    omega
  have hlen_eq : ∀ n, (dss n).length = (ics n).length := fun n => (hF n).length_eq.symm
  obtain ⟨ζ, hζ⟩ := exists_limit ics (comparable_of_mono fun a b h => (hics a b h).1) hunb
  obtain ⟨δ, hδ⟩ := exists_limit dss (comparable_of_mono fun a b h => (hics a b h).2) fun k => by
    obtain ⟨n, hn⟩ := hunb k
    exact ⟨n, by rw [hlen_eq]; exact hn⟩
  -- the session, from the first stage
  obtain ⟨sds, hOk, hr, hcsA, hm, hWT⟩ := build_roundsG hw (hFG 0) (hK 0)
  have hp0 := hpath' 0
  rw [rplay_snoc_eq] at hp0
  obtain ⟨q₁, hp₁, hp₂₃⟩ := path_split_inst hp0
  obtain ⟨u₁, rfl⟩ := idle_of_path_cplay hp₁
  obtain ⟨q₂, hp₂, hp₃⟩ := path_split_inst hp₂₃
  obtain ⟨sB, tB, rfl⟩ : ∃ sB tB, q₂ = .running (f 0) sB tB := by
    cases hp₃ with
    | cons t₁ h₁ =>
      cases t₁ with
      | ucall run callout op =>
        cases h₁
        exact ⟨_, _, rfl⟩
  -- the importer's calls along one run
  have hQ : ∀ k, ∃ q, Ii.Path (profile o) (.idle u₁)
      (.inr (.ask (f 0)) :: callMoves (streamTake ζ k)) q := by
    intro k
    obtain ⟨n, hn⟩ := hunb k
    have hp := hpath' n
    rw [rplay_snoc_eq] at hp
    obtain ⟨q₁', hp₁', hp₂₃'⟩ := path_split_inst hp
    obtain rfl := Silmaril.Wasm.Game.ScalarInstance.Path.functional hp₁' hp₁
    have hsplit : ics n = streamTake ζ k ++ (ics n).drop k := by
      rw [streamTake_eq_take (hζ n) hn.le, List.take_append_drop]
    rw [hsplit, callMoves_app] at hp₂₃'
    have e₃ : ((.inr (.ask (f 0)) :: (callMoves (streamTake ζ k) ++ callMoves ((ics n).drop k))) ++
        [.inl (.ask (e n))] : List (Move Ii.E Ii.F)) =
          (.inr (.ask (f 0)) :: callMoves (streamTake ζ k)) ++
            (callMoves ((ics n).drop k) ++ [.inl (.ask (e n))]) := by
      simp
    rw [e₃] at hp₂₃'
    obtain ⟨q, hq, -⟩ := path_split_inst hp₂₃'
    exact ⟨q, hq⟩
  choose Q hQ using hQ
  have hQstep : ∀ m, Ii.Path (profile o) (Q m) (callMoves [ζ m]) (Q (m + 1)) := by
    intro m
    have hp := hQ (m + 1)
    rw [streamTake_snoc, callMoves_app, ← List.cons_append] at hp
    obtain ⟨q', h₁', h₂'⟩ := path_split_inst hp
    obtain rfl := Silmaril.Wasm.Game.ScalarInstance.Path.functional h₁' (hQ m)
    exact h₂'
  have hcs0 : streamTake ζ (ics 0).length = ics 0 := by
    rw [streamTake_eq_take (hζ 0) le_rfl, List.take_of_length_le le_rfl]
  have hQ0 : Q (ics 0).length = .running (f 0) sB tB := by
    have h₀ := hQ (ics 0).length
    rw [hcs0] at h₀
    exact Silmaril.Wasm.Game.ScalarInstance.Path.functional h₀ hp₂
  have hrel : ∀ k, Silmaril.Wasm.Component.Reference.ImpRel g.imp Ii (ζ k) (δ k) := by
    intro k
    obtain ⟨n, hn⟩ := hunb k
    have hn' : k < (dss n).length := by rw [hlen_eq]; exact hn
    have h₀ := forall₂_getElem (hF n) k hn hn'
    rw [hζ n k hn, hδ n k hn'] at h₀
    exact h₀
  -- the exporter serves them along one run
  have hwtrel : ∀ {x : Round Ii.E} {ds : List (Round (sigN g.imp.imports.length))},
      Silmaril.Wasm.Component.Reference.ImpRel g.imp Ii x ds → ∀ y ∈ ds, WTG g y := by
    intro x ds hx y hy
    obtain ⟨nm, ft, ws, hft, hp, hck'⟩ := impRel_typed hx y hy
    exact wtG_of hw hft hp hck'
  have hwt₀ : ∀ y ∈ (sds.flatMap fun d => d.dss.flatten) ++ (dss 0).flatten, WTG g y := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact hWT y hy
    · exact wtG_flatten hw (hF 0) y hy
  have hd0 : streamTake δ (ics 0).length = dss 0 := by
    rw [streamTake_eq_take (hδ 0) (hlen_eq 0).ge, ← hlen_eq 0, List.take_of_length_le le_rfl]
  have hplays : ∀ n, (twos ((((sds.flatMap fun d => d.dss.flatten) ++ (dss 0).flatten) ++
      (streamTake (fun k => δ ((ics 0).length + k)) n).flatten).map (wireRoundG g)) :
        List (Move sigU sigU)) ∈ (g.expObs (impSemD (profile o))).plays := by
    intro n
    obtain ⟨N₁, hN₁⟩ := hunb ((ics 0).length + n)
    have hadd := streamTake_add' δ (ics 0).length n
    rw [hd0] at hadd
    have hpre : (dss 0).flatten ++ (streamTake (fun k => δ ((ics 0).length + k)) n).flatten <+:
        (dss N₁).flatten := by
      rw [← List.flatten_append, ← hadd,
        streamTake_eq_take (hδ N₁) (by rw [hlen_eq]; exact hN₁.le)]
      exact flatten_prefix (List.take_prefix _ _)
    have hmap : (((sds.flatMap fun d => d.dss.flatten) ++ (dss 0).flatten) ++
        (streamTake (fun k => δ ((ics 0).length + k)) n).flatten).map (wireRoundG g) <+:
          (cl 0).flatMap (·.cs) ++ csN N₁ := by
      rw [List.append_assoc, List.map_append, hcsA, hcsN N₁]
      exact (List.prefix_append_right_inj _).mpr (prefix_map _ hpre)
    have hm' := hIpl _ (hsAn N₁)
    rw [hS N₁, hcl0 N₁] at hm'
    exact (g.expObs (impSemD (profile o))).plays.of_prefix hm'
      ((twos_prefix hmap).trans (List.prefix_append _ _))
  obtain ⟨st, hst0, hst⟩ := exp_plays_streamG he hIC _ (fun k => δ ((ics 0).length + k)) hwt₀
    (fun k => hwtrel (hrel _)) hplays
  obtain ⟨π, hrun₁, hrun₂⟩ := expRunG_split _ _ hst0
  have hp₁' := hp₁
  rw [← hr, cplay_rG] at hp₁'
  have hR := run_of_rounds_idle sds hOk hp₁' hrun₁
  rw [hm] at hR
  exact ⟨(u₁, π), hR, j, vs, rfl, ⟨j, vs, f 0, ics 0, dss 0⟩, sB, tB, st 0, rfl, rfl,
    ⟨lowerArgs g.imp.exports[j].ty.params vs, checkLower_of_check hck, hf₁ 0, hf₂ 0, hF 0⟩,
    hp₂, hrun₂, .inr (.inr ⟨fun k => Q ((ics 0).length + k), fun k => ζ ((ics 0).length + k),
      fun k => δ ((ics 0).length + k), st, hQ0, rfl,
      fun k => ⟨hQstep ((ics 0).length + k), hrel _, hst k⟩⟩)⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGChatter
