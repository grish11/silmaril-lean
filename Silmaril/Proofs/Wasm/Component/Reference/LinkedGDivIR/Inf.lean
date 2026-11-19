module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR.Build
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv.SimpleIR
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.Inf

/-!
# Infinite sessions of an exporter are infinite plays (`ExpSpec.AdeqI`)

* `simple_adeqI`: a simple exporter, at every profile (`exp_env_inf` of `LinkedSessionDAdeq`
  read at the component: `run_layers`, `inf_spullD_cpl`, `imp_inf_cpl`);
* `rechunk`: a stream of runs of lists of calls, unbounded, is one run of single calls along the
  concatenated stream (no determinism: the intermediate states are chosen per list);
* `exp_env_infG`, `exp_env_inf_catG`: the exporter's environment serving forever, from `AdeqI`;
* `toExp_adeqI`: a linked component meets `AdeqI` (`Linked2`'s `inf_denD_build` over `sigU`,
  with an abstract exporter, at every profile); `chain_adeqI`: so does every chain.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Games.Abstract (streamTake)
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq
open Silmaril.Proofs.Wasm.Component.Reference.LinkedG
open Silmaril.Wasm.Abstract.InstSession (spullD instSession)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

theorem lim_uMoves (r : ℕ → URound) :
    (fun n => uMoves (streamTake r n)) = cch (fun k => mk0 (E := sigU) (r k)) :=
  funext fun n => by rw [cch_mk0, uMoves_eq]

/-! ## A simple exporter -/

section Simple

variable {P : Profile} {c : Simple} {I : SInst}

theorem wf_of_step (hc : c.Good) (hI : c.mod.IsInst I) {s s' : Store Nat} {r : URound}
    (h : Simple.ExpStep c I P s r s') (hwf : I.WellFormed s) : I.WellFormed s' := by
  cases h with
  | ret hj hret => exact hret.wellFormed hI (hc.core _ (List.getElem_mem hj)) hwf
  | trap hj htrap => exact htrap.wellFormed hI (hc.core _ (List.getElem_mem hj)) hwf

/-- **A simple exporter meets `AdeqI`** (every profile). -/
theorem simple_adeqI (P : Profile) (hc : c.Good) (hI : c.mod.IsInst I) :
    (Simple.expSpec c I).AdeqI P := by
  intro r S hS0 hS
  have hwf : ∀ k, I.WellFormed (S k) := by
    intro k
    induction k with
    | zero => rw [hS0]; exact hI.1.choose_spec.ok
    | succ k ih => exact wf_of_step hc hI (hS k) ih
  have hlay : ∀ k, ∃ d : LayerI (SimpleI.ofSimple c) I, d.Ok (isInst_ofSimple hI) ∧
      I.Path P (.idle (S k)) (cplay [d.r]) (.idle (S (k + 1))) ∧ d.l₆ = mk0 (r k) := by
    intro k
    obtain ⟨L, hL, hp, hm⟩ :=
      Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv.run_layers hc hI
        (.cons (hS k) (.nil _)) (hwf k)
    rcases L with _ | ⟨d, _ | ⟨d', L⟩⟩
    · simp at hm
    · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hm
      exact ⟨d, hL d List.mem_cons_self, hp, hm⟩
    · simp at hm
  choose D hD hp hm using hlay
  have hbot := inf_spullD_cpl hp
  rw [hS0] at hbot
  have hv := imp_inf_cpl (isInst_ofSimple hI) hD hbot
  rw [show (fun k => (D k).l₆) = fun k => mk0 (r k) from funext hm] at hv
  rw [lim_uMoves]
  exact hv

end Simple

/-! ## Re-chunking a stream of runs -/

section Rechunk

variable {e : ExpSpec} {P : Profile}

/-- A run of an exporter, each call with the state it starts from. -/
inductive RunS (e : ExpSpec) (P : Profile) : e.St → List (URound × e.St) → e.St → Prop
  | nil (s : e.St) : RunS e P s [] s
  | cons {s s₁ s' : e.St} {r : URound} {l : List (URound × e.St)} :
      e.Step P s r s₁ → RunS e P s₁ l s' → RunS e P s ((r, s) :: l) s'

theorem runS_of_run : ∀ {s s' : e.St} {L : List URound}, e.Run P s L s' →
    ∃ l, RunS e P s l s' ∧ l.map Prod.fst = L
  | _, _, _, .nil s => ⟨[], .nil s, rfl⟩
  | _, _, _, .cons h hr => by
    obtain ⟨l, hl, hm⟩ := runS_of_run hr
    exact ⟨_ :: l, .cons h hl, by rw [List.map_cons, hm]⟩

theorem runS_append {s s₁ s₂ : e.St} {l l' : List (URound × e.St)} (h : RunS e P s l s₁)
    (h' : RunS e P s₁ l' s₂) : RunS e P s (l ++ l') s₂ := by
  induction h with
  | nil => exact h'
  | cons hs _ ih => exact .cons hs (ih h')

theorem runS_head : ∀ {s s' : e.St} {l : List (URound × e.St)}, RunS e P s l s' →
    ∀ h : 0 < l.length, (l[0]'h).2 = s
  | _, _, _, .nil _, h => by simp at h
  | _, _, _, .cons _ _, _ => rfl

theorem runS_step : ∀ {s s' : e.St} {l : List (URound × e.St)}, RunS e P s l s' →
    ∀ (i : Nat) (h : i + 1 < l.length), e.Step P (l[i]'(by omega)).2 (l[i]'(by omega)).1
      (l[i + 1]'h).2
  | _, _, _, .nil _, i, h => by simp at h
  | _, _, _, .cons (l := l) hs hl, 0, h => by
    have h' : 0 < l.length := by simp only [List.length_cons] at h; omega
    have e := runS_head hl h'
    simp only [List.getElem_cons_zero, List.getElem_cons_succ]
    rw [e]
    exact hs
  | _, _, _, .cons _ hl, i + 1, h => by
    simp only [List.getElem_cons_succ]
    exact runS_step hl i (by simp only [List.length_cons] at h; omega)

/-- **Re-chunking**: runs of the lists `T k` from `π k` to `π (k + 1)`, when the concatenations
are unbounded, are one run of single calls along a stream `ζ` whose prefixes are those of the
concatenations. -/
theorem rechunk {T : ℕ → List URound} {π : ℕ → e.St}
    (hT : ∀ k, e.Run P (π k) (T k) (π (k + 1))) (hu : ∀ m, ∃ n, m < (catC T n).length) :
    ∃ (ζ : ℕ → URound) (S : ℕ → e.St), S 0 = π 0 ∧
      (∀ i, e.Step P (S i) (ζ i) (S (i + 1))) ∧
      ∀ n m, m ≤ (catC T n).length → streamTake ζ m = (catC T n).take m := by
  choose C hC hCm using fun k => runS_of_run (hT k)
  have hcat : ∀ n, RunS e P (π 0) (catC C n) (π n) := by
    intro n
    induction n with
    | zero => exact .nil _
    | succ n ih =>
      rw [catC_succ]
      exact runS_append ih (hC n)
  have hmap : ∀ n, (catC C n).map Prod.fst = catC T n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [catC_succ, catC_succ, List.map_append, ih, hCm n]
  have hlen : ∀ n, (catC C n).length = (catC T n).length := fun n => by
    rw [← hmap n, List.length_map]
  obtain ⟨ζ', hζ'⟩ := exists_flat_stream C fun m => by
    obtain ⟨n, hn⟩ := hu m
    exact ⟨n, (hlen n).symm ▸ hn⟩
  have hget : ∀ n k (hk : k < (catC C n).length), ζ' k = (catC C n)[k] := by
    intro n k hk
    have h2 := hζ' n (k + 1) hk
    have h3 : (streamTake ζ' (k + 1))[k]'(by simp [streamTake]) = ζ' k := by
      simp only [streamTake, List.getElem_ofFn]
    rw [← h3, List.getElem_of_eq h2, List.getElem_take]
  refine ⟨fun i => (ζ' i).1, fun i => (ζ' i).2, ?_, fun i => ?_, fun n m hm => ?_⟩
  · obtain ⟨n, hn⟩ := hu 0
    rw [← hlen n] at hn
    show (ζ' 0).2 = π 0
    rw [hget n 0 hn]
    exact runS_head (hcat n) hn
  · obtain ⟨n, hn⟩ := hu (i + 1)
    rw [← hlen n] at hn
    show e.Step P (ζ' i).2 (ζ' i).1 (ζ' (i + 1)).2
    rw [hget n i (by omega), hget n (i + 1) hn]
    exact runS_step (hcat n) i hn
  · rw [← hmap n, ← List.map_take, ← hζ' n m (by rw [hlen]; exact hm)]
    simp [streamTake, List.map_ofFn]
    rfl

end Rechunk

/-! ## The exporter's environment serving forever -/

section Env

variable {P : Profile} {g : LinkedG}

/-- **The exporter's environment serving a stream of calls along one run** (from `AdeqI`). -/
theorem exp_env_infG (hI : g.exp.AdeqI P) {ζ : ℕ → URound} {S : ℕ → g.exp.St}
    (hS0 : S 0 = g.exp.init) (hS : ∀ k, g.exp.Step P (S k) (ζ k) (S (k + 1))) :
    (cch fun k => mk0 (E := sigU) (ζ k)).lim ∈ (g.expObs (impSemD P)).inf := by
  have hv := hI ζ S hS0 hS
  rw [lim_uMoves] at hv
  have hN : (cch fun k => mk0 (E := sigU) (ζ k)).lim ∈
      (Node.denD (impSemD P) 0 g.expNode).inf := by
    rw [LinkedG.expNode, Node.denD]
    exact inf_below_cpl (oneCall_implsH 0 []) (fun k => .cons .nil .nil) hv
  have h₅ := inf_pair_cpl (DStrategy.id sigU) hN
  have h₄ := inf_top_cpl (h := splitH 0) (fun k => .call
    (splitH_shift 0 (ζ k).1.1 (ζ k).1.2) rfl .nil) h₅
  have h₃ := inf_below_cpl (oneCall_maskH 0) (fun k => .cons .nil .nil) h₄
  rw [show g.expObs (impSemD P) = DObs.of (DStrategy.ext 0
      (DStrategy.ofHandler (maskH 0)) (Node.denD (impSemD P) 0 g.expNode)) from
    (obs_ext _ _ _).symm]
  exact h₃

theorem catC_map {α β : Type} (f : α → β) (T : ℕ → List α) :
    ∀ n, (catC T n).map f = catC (fun k => (T k).map f) n
  | 0 => rfl
  | n + 1 => by rw [catC_succ, catC_succ, List.map_append, catC_map f T n]

theorem expRunG_catC {T : ℕ → List (Round (sigN g.imp.imports.length))} {π : ℕ → g.exp.St}
    (hT : ∀ k, LinkedG.ExpRun P g (π k) (T k) (π (k + 1))) :
    ∀ n, LinkedG.ExpRun P g (π 0) (catC T n) (π n)
  | 0 => .nil _
  | n + 1 => by
    rw [catC_succ]
    exact expRunG_append (expRunG_catC hT n) (hT n)

/-- **The exporter serving the import calls of infinitely many rounds, forever** (from
`AdeqI`, every profile). -/
theorem exp_env_inf_catG (hI : g.exp.AdeqI P) {T : ℕ → List (Round (sigN g.imp.imports.length))}
    {π : ℕ → g.exp.St} (h0 : π 0 = g.exp.init)
    (hT : ∀ k, LinkedG.ExpRun P g (π k) (T k) (π (k + 1)))
    (hu : Chain.Unbounded fun n =>
      (twos ((catC T n).map (wireRoundG g)) : List (Move sigU sigU))) :
    Chain.lim (fun n => (twos ((catC T n).map (wireRoundG g)) : List (Move sigU sigU))) ∈
      (g.expObs (impSemD P)).inf := by
  simp only [catC_map] at hu ⊢
  have hu' : ∀ k, ∃ n, k < (catC (fun k => (T k).map (wireRoundG g)) n).length := fun k => by
    obtain ⟨n, hn⟩ := hu (2 * k + 2)
    refine ⟨n, ?_⟩
    rw [length_twos] at hn
    omega
  obtain ⟨ζ, S, hS0, hS, hζ⟩ := rechunk (fun k => expRunG_run (hT k)) hu'
  have hE := exp_env_infG hI (hS0.trans h0) hS
  convert hE using 1
  refine lim_eq_of_cofinal (fun n => ⟨(catC (fun k => (T k).map (wireRoundG g)) n).length, ?_⟩)
    (fun m => ?_)
  · rw [cch_mk0, hζ n _ le_rfl, List.take_length]
  · obtain ⟨n, hn⟩ := hu' m
    refine ⟨n, ?_⟩
    rw [cch_mk0, hζ n m hn.le]
    exact twos_prefix (List.take_prefix _ _)

end Env

/-! ## A linked component -/

section Linked

variable {P : Profile} {g : LinkedG} {Ii : SInst}

theorem flatMap_wiredG_catC (D : ℕ → LayerI g.imp Ii)
    {T : ℕ → List (Round (sigN g.imp.imports.length))} (hT : ∀ k, (D k).dss.flatten = T k) :
    ∀ n, (streamTake (fun k => wiredG (g := g) (D k)) n).flatMap (·.cs) =
      (catC T n).map (wireRoundG g)
  | 0 => rfl
  | n + 1 => by
    rw [streamTake_snoc, List.flatMap_append, flatMap_wiredG_catC D hT n, catC_succ,
      List.map_append, List.flatMap_singleton]
    show _ ++ ((D n).dss.flatten.map (wireRoundG g)) = _
    rw [hT n]

/-- **A linked component meets `AdeqI`** (`Adeq` and `AdeqI` exporter, importer `Good` and
`IsInst`, every profile). -/
theorem toExp_adeqI (he : g.exp.Adeq P) (hI : g.exp.AdeqI P) (hi : g.imp.Good)
    (hIi : g.imp.mod.IsInst Ii) : (g.toExp Ii).AdeqI P := by
  intro r S hS0 hS
  choose R hR hp hr hrR using hS
  -- the layers of each round
  have hlay : ∀ k, ∃ D : LayerI g.imp Ii, D.Ok hIi ∧ D.r = rG (R k) ∧ D.u = uG (R k) :=
    fun k => by
      obtain ⟨xs, hxl, h₁, h₂, hrel⟩ := hR k
      exact layer_of hi hIi (j := (R k).j) (vs := (R k).vs)
        ⟨xs, (R k).dss, hxl, h₁, h₂, hrel, rfl⟩
  choose D hD hDr hDu using hlay
  have hdss : ∀ k, (D k).dss.flatten = (R k).dss.flatten := fun k => congrArg CRound.cs (hDu k)
  -- the importer's instance and IR
  have hpI : ∀ k, Ii.Path P (.idle (S k).1) (cplay [(D k).r]) (.idle (S (k + 1)).1) :=
    fun k => by
      have e := cplay_rG (g := g) [R k]
      simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
        List.append_nil] at e
      rw [hDr k, e]
      exact hp k
  have hbot := inf_spullD_cpl hpI
  rw [show (S 0).1 = Ii.store from congrArg Prod.fst hS0] at hbot
  have hv := imp_inf_cpl hIi hD hbot
  -- the importer's node
  have hwire : ∀ k, ∀ x ∈ (D k).dss.flatten,
      ∃ w : Fin g.exp.comp.exports.length, g.wire[x.1.1.val]? = some w.val :=
    fun k x hx => expRunG_wire (hr k) x (by rw [← hdss k]; exact hx)
  have hN : (cch fun k => wiredNG (D k)).lim ∈
      (Node.denD (impSemD P) g.exp.comp.exports.length g.impNode).inf := by
    have h := inf_below_cpl (oneCall_implsH _ _) (fun k => (.cons (hrounds_wireG (hwire k)) .nil :
      HB (implsH g.exp.comp.exports.length (wireArgsG g)) [(D k).l₆] [wiredNG (D k)])) hv
    rw [LinkedG.impNode, Node.denD]
    exact h
  -- the pairing and `splitH`
  have h₅ := inf_pair_cpl (DStrategy.id sigU) hN
  have h₄ := inf_top_cpl (h := splitH g.exp.comp.exports.length) (U := fun k => wiredG (D k))
    (fun k => .call (h := splitH _) (splitH_shift' _ _ _) rfl .nil) h₅
  -- the exporter's environment serves the import calls
  have hflat := flatMap_wiredG_catC D hdss
  have hser : serveC (E := sigU) (fun k => wiredG (g := g) (D k)) =
      fun n => twos ((catC (fun k => (R k).dss.flatten) n).map (wireRoundG g)) :=
    funext fun n => by rw [serveC, hflat n]
  have hπ0 : (S 0).2 = g.exp.init := congrArg Prod.snd hS0
  have hE := inf_comp_serve (σ := DStrategy.ext 0 (DStrategy.ofHandler (maskH 0))
      (Node.denD (impSemD P) 0 g.expNode)) h₄
    (fun n => by
      rw [hser]
      have hr0 := expRunG_catC (π := fun k => (S k).2) hr n
      rw [hπ0] at hr0
      have h := expEnvG he hr0
      rw [← expObs_playsG, LinkedG.expObs, ← obs_ext] at h
      exact h)
    (fun hu => by
      rw [hser] at hu ⊢
      have h := exp_env_inf_catG (π := fun k => (S k).2) hI hπ0 hr hu
      rw [LinkedG.expObs, ← obs_ext] at h
      exact h)
  -- the linked export handler
  have HE : ∀ k, HC (exportsH (g.exp.comp.exports.length + g.imp.exports.length) g.toComp.exports)
      [⟨((D k).j.val, .vals (D k).vs), [], (D k).ans⟩] [(wiredG (D k)).hide (E := sigU)] :=
    fun k => .call (h := exportsH _ _) (q := ((D k).j.val, .vals (D k).vs))
      (q' := (g.exp.comp.exports.length + (D k).j.val, .vals (D k).vs)) (k := fun n => .pure n)
      (exportsH_toCompG g (D k).j.isLt _) rfl .nil
  have hU := inf_top_cpl HE hE
  have henv : ∀ k, (⟨((D k).j.val, .vals (D k).vs), [], (D k).ans⟩ : CRound sigU sigU) =
      mk0 (r k) := fun k => by
    have e : (⟨((D k).j.val, .vals (D k).vs), [], (D k).ans⟩ : CRound sigU sigU) =
        hideU (g := g) (D k).u := rfl
    rw [e, hDu k, hrR k]
    rfl
  rw [show (fun k => (⟨((D k).j.val, .vals (D k).vs), [], (D k).ans⟩ : CRound sigU sigU)) =
    fun k => mk0 (r k) from funext henv] at hU
  rw [lim_uMoves]
  show _ ∈ (g.toComp.denUD (impSemD P)).inf
  rw [toComp_eq_nodes, Comp.denUD]
  simp only [List.length_nil, denNodesD, Nat.zero_add, envAfter_linkG, expNode_widthG]
  exact hU

/-- **Chains meet `AdeqI`**, by induction. -/
theorem chain_adeqI (P : Profile) :
    ∀ (e : ExpSpec) (bs : List (SimpleI × List Nat)) (Is : List SInst), e.Adeq P →
      e.AdeqI P → ChainOk e bs Is → (chainExp e bs Is).AdeqI P
  | _, [], [], _, hI, _ => hI
  | _, (_, _) :: _, _ :: Is, he, hI, ⟨hb, hIb, hw, h⟩ =>
    chain_adeqI P _ _ Is (toExp_adeq he hb hIb hw) (toExp_adeqI he hI hb hIb) h
  | _, [], _ :: _, _, _, h => h.elim
  | _, _ :: _, [], _, _, h => h.elim

end Linked

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR
