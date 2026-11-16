module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack.DivTree

/-!
# Divergence after a nonempty log: conditionals, handlers and the whole run (proofs)

* `headDiv_if`, `headDiv_try`: a conditional diverging alone does so in its condition or its
  chosen arm (after the `if` step, a block); a `try_table` in its body (entered in its handler
  and label). Every finished end is ruled out by `head_contra`; a thrown exception is resolved by
  the clauses (`Cfg.Region.catches_total`).
* `div_all`: `DivG n es` and `CallDivG n` for every `n` and `es`, by strong induction on the
  measure of `EvDiv`, then the size of the trees. With no event left, host-free divergence
  (`divOut_nil`); otherwise the head tree diverges alone (the head cases) or runs to values
  (`evRunN_back_vals`) and the trees after it go on (`head_cons`, `cont_typedH`).
* `evRun_div`: a Core run of a typed invocation with the host events `cs`, then host-free
  divergence, is `(cs, div)` in `wasmEvFunDXP` (the invocation in its `call_ref` form,
  `CallDivG`).
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

variable {H : Type} {tags : List TagInst} {o : GrowOracle} {host : HostSemantics H}
  {s : Store H} {f : Frame} {stk : List Val} {cs : List (Call (wasmHostSig H))} {n : Nat}

/-! ## Conditionals and handlers -/

/-- **A conditional diverging alone**: in its condition, or in its chosen arm. -/
theorem headDiv_if (hT : HostTyped host) (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {bt : BlockType} {c t el es : List BExpr} (ihC : DivG tags o host n c)
    (ihA : ∀ b : Bool, ∀ m ≤ n, DivG tags o host m (if b then t else el))
    (ht : TypedP tags s f stk (.if_ bt c t el :: es))
    (hdv : EvDiv (profile o) host n ⟨s, f, xcode stk [.if_ bt c t el]⟩ cs) :
    DivOut s f stk (.if_ bt c t el :: es) cs := by
  have ht1 := typedP_head ht
  have hdv₀ := hdv
  have hcode : xcode stk [.if_ bt c t el] = xcode stk c ++
      [.plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el))] := by
    rw [xcode, code_if]; simp
  rw [hcode] at hdv
  rcases evDiv_seq_split hdv with hdc | ⟨⟨s₁, f₁, k₁⟩, n₁, m, cs₁, cs₂, ws, rfl, hm, hr₁, hw, hd₁⟩
  · exact divOut_lift₀ (fun _ => LogDivXP.cond) (fun _ _ => ReachLXP.cond)
      (ihC s f stk cs (cond_typedP ht) hdc)
  dsimp only at hw hd₁
  subst hw
  obtain ⟨l₁, stk', hd, hq, rfl⟩ := evRunN_back_vals hT hH hE (cond_typedP ht) hr₁
  have hcons := consistent_append (evDiv_consistent hdv₀)
  obtain ⟨-, labels, ret, out, hS, hck, -, hTM, hts⟩ := id ht1
  obtain ⟨o₁, h1, -⟩ := chk_consE.mp hck
  obtain ⟨oc, hco, hk1⟩ := chk1_ifE h1
  obtain ⟨hev, -⟩ := evalLXPh_evRun (P := profile o) hH hE hd hq hcons.1
  obtain ⟨t₁, hA, -⟩ := Silmaril.Wasm.Interp.HostEvalP.evalOXP_host_good (P := profile o) hH hE
    hev hts
  have hsite : Sim.ContextTyped ⟨s₁, f₁, vals stk'.reverse ++
      .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) :: []⟩ := by
    have h0 := typedP_ctx' ht1
    rw [hcode] at h0
    simpa using ContextTyped.steps_typed hT h0 (Steps.append [_] (evRunN_steps hr₁))
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
  have hdK := evDiv_through_steps hpre hsite (by simpa using hd₁)
  have htA : TypedP tags s₁ f₁ (stk₁.take np) (if b then t else el) :=
    ⟨[], nr :: labels, ret, ob, storeChk_inv inv1 hS, by rw [take_length_of_le hp]; exact hb',
      by simpa using Sim.ContextTyped.label htK, by rw [inv1.2.1]; exact hTM, t₁⟩
  rcases evDiv_label_seq_split hdK with hda | ⟨cb, N₁, mm, cs₂₁, cs₂₂, rfl, -, hbr, hsb, hdc, -⟩
  · exact divOut_lift (fun _ h => LogDivXP.arm hd hb har h) (fun _ _ h => ReachLXP.arm hd hb har h)
      hq (ihA b m hm _ _ _ _ htA hda)
  exfalso
  obtain ⟨l₂, ⟨s₂, f₂, ob₂⟩, hd₂, hres₂, -⟩ := evRunN_back hT hH hE htA hbr hsb hdc
  have hw := resW_prepend hq (resW_of_back hres₂)
  have hdv₁ : EvDiv (profile o) host n ⟨s, f, xcode stk [.if_ bt c t el]⟩
      ((cs₁ ++ cs₂₁) ++ cs₂₂) := by rw [List.append_assoc]; exact hdv₀
  cases ob₂ with
  | tail => exact head_contra hT hH hE ht1 (.ifEsc hd hb har hd₂ trivial) hw hdv₁
  | flow fl =>
    rcases flow_cases fl with ⟨vs, hvs⟩ | ⟨k, vs, rfl⟩ | hesc
    · exact head_contra hT hH hE ht1 (.ifOk hd hb har hd₂ hvs .nil) (resW_nil hw) hdv₁
    · exact head_contra hT hH hE ht1 (.ifBrk hd hb har hd₂) hw hdv₁
    · exact head_contra hT hH hE ht1 (.ifEsc hd hb har hd₂ hesc) hw hdv₁

/-- **A `try_table` diverging alone**: in its body. -/
theorem headDiv_try (hT : HostTyped host) (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {bt : BlockType} {cl : List Catch} {body es : List BExpr} (ihB : DivG tags o host n body)
    (ht : TypedP tags s f stk (.tryTable bt cl body :: es))
    (hdv : EvDiv (profile o) host n ⟨s, f, xcode stk [.tryTable bt cl body]⟩ cs) :
    DivOut s f stk (.tryTable bt cl body :: es) cs := by
  have ht1 := typedP_head ht
  obtain ⟨-, labels, ret, out, hS, hc, -, -, hts⟩ := id ht1
  obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
  obtain ⟨ns, np, nr, -, ha, -, -, -, -⟩ := chk1_tryTableE h1
  have har : Binaryen.arity f bt = some (np, nr) := (arity_eq f bt).trans ha
  obtain ⟨-, -, -, hp, -, -⟩ := arity_try_pre har hc
  have henter : Steps (profile o) NH ⟨s, f, xcode stk [.tryTable bt cl body]⟩
      ⟨s, f, vals (stk.drop np).reverse ++
        [.handler nr cl [.label nr [] (xcode (stk.take np) body)]] ++ []⟩ := by
    rw [xcode, code_tryTable]
    exact steps_try_enter har hp []
  have hdK := evDiv_through_steps henter (typedP_ctx' ht1) hdv
  have htB := try_body_typedP har ht
  have fin : ∀ (cb : Config H) (N₁ : Nat) (cs₁ cs₂ : List (Call (wasmHostSig H))),
      cs = cs₁ ++ cs₂ → EvRunN (profile o) host N₁ ⟨s, f, xcode (stk.take np) body⟩ cs₁ cb →
      (∀ c', ¬ Step (profile o) Det.noHost cb c') → decompose? cb.store cb.code = none → False := by
    rintro cb N₁ cs₁ cs₂ rfl hb hsb hdc
    obtain ⟨l, ⟨s₁, f₁, ob⟩, hd, hres, -⟩ := evRunN_back hT hH hE htB hb hsb hdc
    have hw := resW_of_back hres
    cases ob with
    | tail => exact head_contra hT hH hE ht1 (.tryEsc har hd trivial trivial) hw hdv
    | flow fl =>
      rcases fl with vs | ⟨_ | k, vs⟩ | vs | _ | a
      · exact head_contra hT hH hE ht1 (.tryOk har hd rfl .nil) (resW_nil hw) hdv
      · exact head_contra hT hH hE ht1 (.tryOk har hd rfl .nil) (resW_nil hw) hdv
      · exact head_contra hT hH hE ht1 (.tryBrk har hd) hw hdv
      · exact head_contra hT hH hE ht1 (.tryEsc har hd trivial trivial) hw hdv
      · exact head_contra hT hH hE ht1 (.tryEsc har hd trivial trivial) hw hdv
      · obtain ⟨rr, hrr⟩ := Cfg.Region.catches_total s₁ f₁ a cl
        cases rr with
        | none => exact head_contra hT hH hE ht1 (.tryRethrow har hd hrr) hw hdv
        | some p =>
          obtain ⟨us, l'⟩ := p
          exact head_contra hT hH hE ht1 (.tryCatch har hd hrr) hw hdv
  rcases evDiv_handler_seq_split hdK with hdH | ⟨cH, N₁, mH, csA, csB, rfl, -, hH₁, hsH, hdcH, -⟩
  · have hdH' : EvDiv (profile o) host n
        ⟨s, f, vals [] ++ [.label nr [] (xcode (stk.take np) body)] ++ []⟩ cs := by
      simpa [vals] using hdH
    rcases evDiv_label_seq_split hdH' with hdb | ⟨cb, N₂, mm, cs₁, cs₂, rfl, -, hb, hsb, hdc, -⟩
    · exact divOut_lift₀ (fun _ => LogDivXP.handler har) (fun _ _ => ReachLXP.handler har)
        (ihB s f _ cs htB hdb)
    · exact (fin cb N₂ cs₁ cs₂ rfl hb hsb hdc).elim
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
    exact fin cb N₂ csA₁ (csA₂ ++ csB) (by simp) hb hsb hdc

/-! ## The whole run -/

/-- **The divergent backward simulation**, for divergences cut within every number of steps: by
strong induction on the measure of `EvDiv`, then the size of the trees. -/
theorem div_all (hT : HostTyped host) (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    (n : Nat) : (∀ es, DivG tags o host n es) ∧ CallDivG tags o host n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have hC : CallDivG tags o host n :=
    callDiv_step hT hH hE (fun m hm => (ih m hm).1) (fun m hm => (ih m hm).2)
  have hCle : ∀ m ≤ n, CallDivG tags o host m := fun m hm => by
    rcases Nat.lt_or_eq_of_le hm with h | rfl
    · exact (ih m h).2
    · exact hC
  refine ⟨?_, hC⟩
  suffices key : ∀ k, ∀ es : List BExpr, sizeOf es < k → DivG tags o host n es from
    fun es => key _ es (Nat.lt_succ_self _)
  intro k
  induction k with
  | zero => intro es h; omega
  | succ k ihk =>
    intro es hes s f stk cs ht hdv
    have ihle : ∀ es', sizeOf es' < sizeOf es → ∀ m ≤ n, DivG tags o host m es' :=
      fun es' hlt m hm => by
        rcases Nat.lt_or_eq_of_le hm with h | rfl
        · exact (ih m h).1 es'
        · exact ihk es' (by omega)
    by_cases hcs : cs = []
    · subst hcs
      exact divOut_nil ht hdv
    rcases es with _ | ⟨e, es⟩
    · refine (evDiv_stuck (fun c' h => ?_) hdv).elim
      exact Sim.Step.not_vals (by simpa [xcode, expression] using h)
    have hcode : xcode stk (e :: es) = xcode stk [e] ++
        expression (Binaryen.BExpr.lowerList es) := by
      simp
    rw [hcode] at hdv
    rcases evDiv_seq_split hdv with hdh | ⟨⟨s₂, f₂, k₂⟩, n₁, m, cs₁, cs₂, ws, rfl, hm, hr₁, hw, hd₁⟩
    · rcases e with ⟨i, args⟩ | ⟨bt, body⟩ | ⟨bt, body⟩ | ⟨bt, c, t, el⟩ | ⟨bt, cl, body⟩
      · exact headDiv_op hT hH hE (ihle _ size_args n le_rfl) hCle ht hdh
      · exact headDiv_block hT hH hE (ihle _ size_block n le_rfl) ht hdh
      · exact headDiv_loop hT hH hE (ihle _ size_loop) (fun m hm => (ih m hm).1 _) ht hcs hdh
      · exact headDiv_if hT hH hE (ihle _ size_cond n le_rfl) (fun b => ihle _ (size_arm b)) ht hdh
      · exact headDiv_try hT hH hE (ihle _ size_try n le_rfl) ht hdh
    dsimp only at hw hd₁
    subst hw
    obtain ⟨l₁, stk₂, hd, hq, rfl⟩ := evRunN_back_vals hT hH hE (typedP_head ht) hr₁
    have hcons := consistent_append (evDiv_consistent hdv)
    have hst : Steps (profile o) host ⟨s, f, xcode stk (e :: es)⟩ ⟨s₂, f₂, xcode stk₂ es⟩ := by
      rw [hcode]
      exact Steps.append _ (evRunN_steps hr₁)
    have htk := cont_typedH hT hH hE ht hd hq hcons.1 hst
    obtain ⟨hl, hr⟩ := head_cons hd es
    exact divOut_lift hl hr hq (ihle es size_tail m hm s₂ f₂ stk₂ cs₂ htk hd₁)

/-- **A Core run of a typed invocation with the host events `cs`, then host-free divergence, is
`(cs, div)` in `wasmEvFunDXP`** (deterministic profile). -/
theorem evRun_div (hT : HostTyped host) (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {a : Nat} {vs : List Val} {c' : Config H} (hs : StoreOk s) (hS : StoreChkE (ehExt tags) s.funcs)
    (hts : TagsOk tags s) (hok : InvokeOk s a vs)
    (hrun : EvRun (profile o) host (invoke s a vs) cs c')
    (hd : Diverges (profile o) (fun _ _ _ _ => False) c') :
    (cs, .div) ∈ wasmEvFunDXP s (a, vs) := by
  obtain ⟨n, hn⟩ := evDiv_of_evRun hrun hd
  have hct := invoke_callTyped hs hok hS hts
  obtain ⟨⟨-, -, fi, ps, rs, hfi, hty, hlen⟩, -⟩ := id hct
  obtain ⟨_, _, _, _, _, hcfg⟩ := invoke_ok hs hok
  have hctx := Sim.ContextTyped.of_configOk hcfg
  have hinv : invoke s a vs = ⟨s, {}, Interp.callCode [] vs a (.callRefType fi.type) []⟩ := by
    rw [invoke_eqP hfi]; simp [Interp.callCode, vals]
  rw [hinv] at hn hctx
  exact (div_all (o := o) hT hH hE n).2 s {} [] vs a (.callRefType fi.type) cs trivial hct.1 hctx hn

end Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack
