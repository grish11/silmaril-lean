module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack.InfTree

/-!
# Productive runs: blocks, conditionals and handlers (proofs)

A block runs productively alone in its body; a conditional in its condition or in its chosen arm
(after the `if` step, a block); a `try_table` in its body (entered in its handler and label).
Every finished end is ruled out by `head_contraI`; a thrown exception is resolved by the clauses
(`Cfg.Region.catches_total`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Abstract.CallXP (POut)
open Silmaril.Wasm.Binaryen (BExpr liftInstrs)
open Shape (streamAppend)

variable {H : Type} {tags : List TagInst} {o : GrowOracle} {host : HostSemantics H}
  {s : Store H} {f : Frame} {stk : List Val} {ω : Nat → Call (wasmHostSig H)}

/-- **A block running productively alone**: in its body. -/
theorem headInf_block (hT : HostTyped host) (hH : HostSliceT host) (hE : HostSliceE tags host)
    {bt : BlockType} {body es : List BExpr} (ihB : InfG tags o host body)
    (ht : TypedP tags s f stk (.block bt body :: es))
    (hdv : CoreInf (profile o) host (pcfg s f stk [.block bt body]) ω) :
    InfOutX tags o host s f stk (.block bt body :: es) ω := by
  have ht1 := typedP_head ht
  obtain ⟨-, labels, ret, out, hS, hc, -, -, hts⟩ := id ht1
  obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
  obtain ⟨np, nr, ha, hp, -, -⟩ := chk1_blockE h1
  have har : Binaryen.arity f bt = some (np, nr) := (arity_eq f bt).trans ha
  have henter : Steps (profile o) NH (pcfg s f stk [.block bt body])
      ⟨s, f, vals (stk.drop np).reverse ++
        [.label nr [] (xcode (stk.take np) body)] ++ []⟩ := by
    show Steps _ _ ⟨s, f, xcode stk [.block bt body]⟩ _
    rw [xcode, code_block]
    exact steps_enter hp (step_block har) []
  have hdK := coreInf_through_dsteps henter hdv
  have htB := block_body_typedP har ht
  rcases coreInf_split_label hdK with hdb | ⟨cs₁, ω₂, cb, N₁, rfl, hb, hsb, hdc, -⟩
  · exact infOut_lift₀ (fun _ => InfLXP.block har) (fun _ _ => ReachLXP.block har)
      (link_cons ⟨_, lifts_label (stk.drop np).reverse nr [] [], henter⟩)
      (ihB s f _ ω htB hdb)
  exfalso
  obtain ⟨l, ⟨s₁, f₁, ob⟩, hd, hres, -⟩ := evRunN_back hT hH hE htB hb hsb hdc
  have hw := resW_of_back hres
  cases ob with
  | tail => exact head_contraI hH hE ht1 (.blockEsc har hd trivial) hw hdv
  | flow fl =>
    rcases flow_cases fl with ⟨vs, hvs⟩ | ⟨k, vs, rfl⟩ | hesc
    · exact head_contraI hH hE ht1 (.blockOk har hd hvs .nil) (resW_nil hw) hdv
    · exact head_contraI hH hE ht1 (.blockBrk har hd) hw hdv
    · exact head_contraI hH hE ht1 (.blockEsc har hd hesc) hw hdv

/-- **A conditional running productively alone**: in its condition, or in its chosen arm. -/
theorem headInf_if (hT : HostTyped host) (hH : HostSliceT host) (hE : HostSliceE tags host)
    {bt : BlockType} {c t el es : List BExpr} (ihC : InfG tags o host c)
    (ihA : ∀ b : Bool, InfG tags o host (if b then t else el))
    (ht : TypedP tags s f stk (.if_ bt c t el :: es))
    (hdv : CoreInf (profile o) host (pcfg s f stk [.if_ bt c t el]) ω) :
    InfOutX tags o host s f stk (.if_ bt c t el :: es) ω := by
  have ht1 := typedP_head ht
  have hdv₀ := hdv
  have hcode : xcode stk [.if_ bt c t el] = xcode stk c ++
      [.plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el))] := by
    rw [xcode, code_if]; simp
  have hX : (pcfg s f stk [.if_ bt c t el] : Config H) = ⟨s, f, xcode stk c ++
      [.plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el))]⟩ := by
    simp only [pcfg, hcode]
  rw [hX] at hdv
  rcases coreInf_split_seq hdv with hdc | ⟨cs₁, ω₂, ⟨s₁, f₁, k₁⟩, n₁, ws, rfl, hr₁, hw, hd₁⟩
  · exact infOut_lift₀ (fun _ => InfLXP.cond) (fun _ _ => ReachLXP.cond)
      (link_cons ⟨_, lifts_suffix _, rtg_of_eq hX⟩) (ihC s f stk ω (cond_typedP ht) hdc)
  dsimp only at hw hd₁
  subst hw
  obtain ⟨l₁, stk', hd, hq, rfl⟩ := evRunN_back_vals hT hH hE (cond_typedP ht) hr₁
  have hcons := consistent_of_coreInf hdv₀
  obtain ⟨-, labels, ret, out, hS, hck, -, hTM, hts⟩ := id ht1
  obtain ⟨o₁, h1, -⟩ := chk_consE.mp hck
  obtain ⟨oc, hco, hk1⟩ := chk1_ifE h1
  obtain ⟨hev, -⟩ := evalLXPh_evRun (P := profile o) hH hE hd hq hcons
  obtain ⟨t₁, hA, -⟩ := Silmaril.Wasm.Interp.HostEvalP.evalOXP_host_good (P := profile o) hH hE
    hev hts
  have hsite : Sim.ContextTyped ⟨s₁, f₁, vals stk'.reverse ++
      .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) :: []⟩ := by
    have h0 := typedP_ctx' ht1
    rw [hcode] at h0
    simpa using ContextTyped.steps_typed hT h0 (Steps.append [_] (evRunN_steps hr₁))
  have hlinkC : cs₁ = [] → Relation.ReflTransGen (Det.DStep o) (pcfg s f stk [.if_ bt c t el])
      ⟨s₁, f₁, vals stk'.reverse ++
        .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) :: []⟩ := by
    rintro rfl
    have := (lifts_suffix (o := o)
      [.plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el))]).rtg
      (evRunN_nil_dsteps hr₁)
    rw [hX]
    simpa using this
  obtain ⟨cv, stk₁, b, rfl, hb⟩ := truthy_progressH hsite
  obtain ⟨hoc, inv1⟩ := (arityE_of_arityP hA) hS hco
  obtain ⟨np, nr, ha, -, -, -, -⟩ := hk1 _ hoc
  have har : Binaryen.arity f₁ bt = some (np, nr) := by
    rw [arity_eq, inv1.2.1]; exact ha
  obtain ⟨-, hp, hbe, -⟩ := arity_if_pre (b := b) hS (arityE_of_arityP hA) har hck
  obtain ⟨ob, hb', -⟩ := endsAt_eq (chk_inv_endsAt inv1 hbe)
  have hif := steps_if_arm (o := o) (s := s₁) (f := f₁) (stk := stk₁) (bt := bt) (t := t)
    (el := el) (rest := []) hb
  have henter := steps_enter (P := profile o) (host := NH) (s := s₁) (f := f₁)
    (B := Binaryen.BExpr.lowerList (if b then t else el)) hp (step_block har) []
  have hpre := hif.trans henter
  have htK := hsite.steps hpre
  have hdK := coreInf_through_dsteps hpre (by simpa using hd₁)
  have htA : TypedP tags s₁ f₁ (stk₁.take np) (if b then t else el) :=
    ⟨[], nr :: labels, ret, ob, storeChk_inv inv1 hS, by rw [take_length_of_le hp]; exact hb',
      by simpa using Sim.ContextTyped.label htK, by rw [inv1.2.1]; exact hTM, t₁⟩
  rcases coreInf_split_label hdK with hda | ⟨cs₂₁, ω₃, cb, N₁, rfl, hbr, hsb, hdc, -⟩
  · exact infOut_lift (fun _ h => InfLXP.arm hd hb har h) (fun _ _ h => ReachLXP.arm hd hb har h)
      hq (fun h0 => link_cons ⟨_, lifts_label (stk₁.drop np).reverse nr [] [],
        (hlinkC h0).trans hpre⟩) (ihA b _ _ _ _ htA hda)
  exfalso
  obtain ⟨l₂, ⟨s₂, f₂, ob₂⟩, hd₂, hres₂, -⟩ := evRunN_back hT hH hE htA hbr hsb hdc
  have hw := resW_prepend hq (resW_of_back hres₂)
  have hdv₁ : CoreInf (profile o) host (pcfg s f stk [.if_ bt c t el])
      ((cs₁ ++ cs₂₁) ++ω ω₃) := by rw [Shape.streamAppend_append]; exact hdv₀
  cases ob₂ with
  | tail => exact head_contraI hH hE ht1 (.ifEsc hd hb har hd₂ trivial) hw hdv₁
  | flow fl =>
    rcases flow_cases fl with ⟨vs, hvs⟩ | ⟨k, vs, rfl⟩ | hesc
    · exact head_contraI hH hE ht1 (.ifOk hd hb har hd₂ hvs .nil) (resW_nil hw) hdv₁
    · exact head_contraI hH hE ht1 (.ifBrk hd hb har hd₂) hw hdv₁
    · exact head_contraI hH hE ht1 (.ifEsc hd hb har hd₂ hesc) hw hdv₁

/-- **A `try_table` running productively alone**: in its body. -/
theorem headInf_try (hT : HostTyped host) (hH : HostSliceT host) (hE : HostSliceE tags host)
    {bt : BlockType} {cl : List Catch} {body es : List BExpr} (ihB : InfG tags o host body)
    (ht : TypedP tags s f stk (.tryTable bt cl body :: es))
    (hdv : CoreInf (profile o) host (pcfg s f stk [.tryTable bt cl body]) ω) :
    InfOutX tags o host s f stk (.tryTable bt cl body :: es) ω := by
  have ht1 := typedP_head ht
  obtain ⟨-, labels, ret, out, hS, hc, -, -, hts⟩ := id ht1
  obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
  obtain ⟨ns, np, nr, -, ha, -, -, -, -⟩ := chk1_tryTableE h1
  have har : Binaryen.arity f bt = some (np, nr) := (arity_eq f bt).trans ha
  obtain ⟨-, -, -, hp, -, -⟩ := arity_try_pre har hc
  have henter : Steps (profile o) NH (pcfg s f stk [.tryTable bt cl body])
      ⟨s, f, vals (stk.drop np).reverse ++
        [.handler nr cl [.label nr [] (xcode (stk.take np) body)]] ++ []⟩ := by
    show Steps _ _ ⟨s, f, xcode stk [.tryTable bt cl body]⟩ _
    rw [xcode, code_tryTable]
    exact steps_try_enter har hp []
  have hdK := coreInf_through_dsteps henter hdv
  have htB := try_body_typedP har ht
  have fin : ∀ (cb : Config H) (N₁ : Nat) (cs₁ : List (Call (wasmHostSig H)))
      (ω₂ : Nat → Call (wasmHostSig H)),
      ω = cs₁ ++ω ω₂ → EvRunN (profile o) host N₁ ⟨s, f, xcode (stk.take np) body⟩ cs₁ cb →
      (∀ c', ¬ Step (profile o) Det.noHost cb c') → decompose? cb.store cb.code = none → False := by
    rintro cb N₁ cs₁ ω₂ rfl hb hsb hdc
    obtain ⟨l, ⟨s₁, f₁, ob⟩, hd, hres, -⟩ := evRunN_back hT hH hE htB hb hsb hdc
    have hw := resW_of_back hres
    cases ob with
    | tail => exact head_contraI hH hE ht1 (.tryEsc har hd trivial trivial) hw hdv
    | flow fl =>
      rcases fl with vs | ⟨_ | k, vs⟩ | vs | _ | a
      · exact head_contraI hH hE ht1 (.tryOk har hd rfl .nil) (resW_nil hw) hdv
      · exact head_contraI hH hE ht1 (.tryOk har hd rfl .nil) (resW_nil hw) hdv
      · exact head_contraI hH hE ht1 (.tryBrk har hd) hw hdv
      · exact head_contraI hH hE ht1 (.tryEsc har hd trivial trivial) hw hdv
      · exact head_contraI hH hE ht1 (.tryEsc har hd trivial trivial) hw hdv
      · obtain ⟨rr, hrr⟩ := Cfg.Region.catches_total s₁ f₁ a cl
        cases rr with
        | none => exact head_contraI hH hE ht1 (.tryRethrow har hd hrr) hw hdv
        | some p =>
          obtain ⟨us, l'⟩ := p
          exact head_contraI hH hE ht1 (.tryCatch har hd hrr) hw hdv
  rcases coreInf_handler_seq_split hdK with hdH | ⟨csA, ωB, cH, N₁, rfl, hH₁, hsH, hdcH, -⟩
  · have hdH' : CoreInf (profile o) host
        ⟨s, f, vals [] ++ [.label nr [] (xcode (stk.take np) body)] ++ []⟩ ω := by
      simpa [vals] using hdH
    rcases coreInf_split_label hdH' with hdb | ⟨cs₁, ω₂, cb, N₂, rfl, hb, hsb, hdc, -⟩
    · refine infOut_lift₀ (fun _ => InfLXP.handler har) (fun _ _ => ReachLXP.handler har)
        (link_cons ⟨_, (lifts_handler (stk.drop np).reverse nr cl []).comp
          (lifts_label [] nr [] []), ?_⟩) (ihB s f _ ω htB hdb)
      show Steps (profile o) NH _ _
      simpa [vals] using henter
    · exact (fin cb N₂ cs₁ ω₂ rfl hb hsb hdc).elim
  · exfalso
    have hH₁' : EvRunN (profile o) host N₁
        ⟨s, f, vals [] ++ [.label nr [] (xcode (stk.take np) body)] ++ []⟩ csA cH := by
      simpa [vals] using hH₁
    obtain ⟨cb, N₂, csA₁, csA₂, rfl, -, hb, hsb, -, hx⟩ := evRunN_label_seq_split hH₁' hsH
    have hdc : decompose? cb.store cb.code = none := by
      cases hdc' : decompose? cb.store cb.code with
      | none => rfl
      | some x =>
        exfalso
        obtain ⟨-, rfl⟩ := hx (by rw [hdc']; rfl)
        obtain ⟨E, a, hh, us⟩ := x
        have := decompose?_label_some (n := nr) (cont := []) hdc'
        simp only [vals, List.map_nil, List.nil_append, List.append_nil] at hdcH
        rw [this] at hdcH
        cases hdcH
    exact fin cb N₂ csA₁ (csA₂ ++ω ωB) (by rw [Shape.streamAppend_append]) hb hsb hdc

end Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack
