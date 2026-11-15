module

public import Silmaril.Proofs.Wasm.Abstract.HostEval.CallWasm
public import Silmaril.Wasm.Abstract.HostCall.Thms

/-!
# The whole-run backward simulation with host calls (proofs)

`back_whole`: in the deterministic profile `SingleThreaded.profile o`, for a host
with typed answers (`HostTyped`) in the native host slice
(`Interp.NativeHostSlice`), every Core run of lowered, arity-checked, typed trees
to a stuck end is the end of an `EvalH` run (`EndsAs`) or is blocked at a host call
with no outcome (`Pending`).

The proof is a well-founded induction on the run length, then the tree size
(`BackGoal`). The constructor cases (`back_nil`, `back_op_flat`, `back_op_call`
with `back_call_host`/`back_call_wasm`, `back_block_tree`, `back_loop_tree`,
`back_if_tree`) are applied with their hypotheses discharged:

* the induction hypotheses, at a run no longer than the whole on a smaller tree,
  or strictly shorter (callee bodies, loop re-entry);
* the forward simulation (`Interp.evalH_good`): every `EvalH` result satisfies the
  arity check's `FlowOk` and keeps the store check (`EvalInv`), and is a Core run,
  which carries typing to the intermediate configurations
  (`HostCall.ContextTyped.steps_typed`);
* typed native progress (`Interp.evalFlat_progressH`, `Interp.truthy_progressH`);
* the host slice (result arity, no exceptions).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostEval

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core (Outcome)
open Silmaril.Wasm.SingleThreaded

variable {H : Type} {host : HostSemantics H}

/-- The statement of the backward simulation for `n` steps of the trees `es`. -/
def BackGoal (o : GrowOracle) (host : HostSemantics H) (n : Nat) (es : List Binaryen.BExpr) : Prop :=
  ∀ (s : Store H) (f : Frame) (stk : List Val) (labels : List Nat) (ret : Nat) (out : Option Nat)
    (c : Config H), Interp.StoreChk s.funcs →
    Interp.chk s.funcs f.module f.locals.length ret labels (some stk.length) es = some out →
    Sim.ContextTyped ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ →
    StepsN (profile o) host n ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ c →
    (∀ c', ¬ Step (profile o) host c c') → BackOut host s f stk es c

variable {o : GrowOracle}

/-- A normal native run of checked trees is a Core run to its values. -/
theorem run_of_evalH (hH : Interp.NativeHostSlice host) {s s₁ : Store H} {f f₁ : Frame}
    {stk stk₁ : List Val} {xs : List Binaryen.BExpr} {labels : List Nat} {ret : Nat}
    {out : Option Nat} (hev : EvalH host s f stk xs (s₁, f₁, .normal stk₁))
    (hS : Interp.StoreChk s.funcs)
    (hc : Interp.chk s.funcs f.module f.locals.length ret labels (some stk.length) xs = some out) :
    Steps (profile o) host ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList xs)⟩
      ⟨s₁, f₁, vals stk₁.reverse⟩ := by
  obtain ⟨c', o', hrun, he, hm⟩ :=
    Interp.run_of_wp ((Interp.evalH_good (P := profile o) hH hev).2 hS hc)
  rw [← Interp.ends_normal hm he]
  exact hrun

/-- **The operator case** other than a call. -/
theorem case_op_flat (hT : HostTyped host) (hH : Interp.NativeHostSlice host) {n : Nat}
    {i : Instr} {args es : List Binaryen.BExpr} (hi : ∀ x, i ≠ .call x)
    (ihle : ∀ m ≤ n, ∀ es', sizeOf es' < sizeOf (Binaryen.BExpr.op i args :: es) →
      BackGoal o host m es') :
    BackGoal o host n (.op i args :: es) := by
  intro s f stk labels ret out c hS hc ht hrun hend
  obtain ⟨o₁, h1, h2⟩ := Interp.chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := Interp.chk1_opE h1
  have hcode := Interp.code_op stk i args es
  have hta : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList args)⟩ :=
    Sim.ContextTyped.suffix (hcode ▸ ht)
  -- typing after the arguments
  have htyped : ∀ s₁ f₁ stk₁, EvalH host s f stk args (s₁, f₁, .normal stk₁) →
      Sim.ContextTyped ⟨s₁, f₁, vals stk₁.reverse ++ .plain i ::
        expression (Binaryen.BExpr.lowerList es)⟩ := by
    intro s₁ f₁ stk₁ hev
    have hr := Silmaril.Wasm.Logic.Core.Steps.append (.plain i :: expression (Binaryen.BExpr.lowerList es))
      (run_of_evalH (o := o) hH hev hS ha)
    exact ContextTyped.steps_typed hT (hcode ▸ ht) hr
  refine back_op_flat hi hrun hend ?_ ?_ ?_
  · intro m hm c₁ h₁ hs₁
    exact ihle m hm args Interp.size_args s f stk labels ret oa c₁ hS ha hta h₁ hs₁
  · intro s₁ f₁ stk₁ hev
    obtain ⟨hf, -⟩ := Interp.arity_args hS (Interp.evalH_good (P := profile o) hH hev).1 h1
    exact ⟨Interp.evalFlat_progressH hf hi (htyped s₁ f₁ stk₁ hev),
      _, _, _, _, _, _, hf⟩
  · intro s₁ f₁ stk₁ s₂ f₂ stk₂ m hm hev hfl hrun₂
    obtain ⟨hf, inv1⟩ := Interp.arity_args hS (Interp.evalH_good (P := profile o) hH hev).1 h1
    obtain ⟨ho, inv2⟩ := Interp.flat_normal (ext := Interp.noExt) hfl hf
    have inv12 : Interp.EvalInv s f (s₂, f₂, .normal stk₂) := inv1.trans inv2
    have h2' : Interp.chk s₂.funcs f₂.module f₂.locals.length ret labels (some stk₂.length) es =
        some out := by
      rw [← ho]; exact Interp.chk_inv inv12 h2
    have hst := Interp.steps_flat_normal (P := profile o) (host := host) hi hf hfl
      (expression (Binaryen.BExpr.lowerList es))
    have ht₂ : Sim.ContextTyped ⟨s₂, f₂, vals stk₂.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ :=
      ContextTyped.steps_typed hT (htyped s₁ f₁ stk₁ hev) hst
    exact ihle m hm es Interp.size_tail s₂ f₂ stk₂ labels ret out c (Interp.storeChk_inv inv12 hS) h2'
      ht₂ hrun₂ hend

/-- **The block case.** -/
theorem case_block (hT : HostTyped host) (hH : Interp.NativeHostSlice host) {n : Nat}
    {bt : BlockType} {body es : List Binaryen.BExpr}
    (ihle : ∀ m ≤ n, ∀ es', sizeOf es' < sizeOf (Binaryen.BExpr.block bt body :: es) →
      BackGoal o host m es') :
    BackGoal o host n (.block bt body :: es) := by
  intro s f stk labels ret out c hS hc ht hrun hend
  obtain ⟨o₁, h1, h2⟩ := Interp.chk_consE.mp hc
  obtain ⟨np, nr, hba, hp, hbody, rfl⟩ := Interp.chk1_blockE h1
  have har : Binaryen.arity f bt = some (np, nr) := (Interp.arity_eq f bt).trans hba
  obtain ⟨ob, hb, hob⟩ := Interp.endsAt_eq hbody
  have hb' : Interp.chk s.funcs f.module f.locals.length ret (nr :: labels)
      (some (stk.take np).length) body = some ob := by
    rw [Interp.take_length_of_le hp]; exact hb
  have hcode := Interp.code_block (body := body) stk bt es
  -- typing of the body, inside the entered label
  have htb : Sim.ContextTyped ⟨s, f, vals (stk.take np).reverse ++
      expression (Binaryen.BExpr.lowerList body)⟩ := by
    have henter := Interp.steps_enter (P := profile o) (host := Det.noHost) (s := s) (f := f)
      (B := Binaryen.BExpr.lowerList body) hp (Interp.step_block har)
      (expression (Binaryen.BExpr.lowerList es))
    exact Sim.ContextTyped.label (Sim.ContextTyped.steps (hcode ▸ ht) henter)
  refine back_block_tree har hp hrun hend ?_ ?_ ?_
  · intro m hm cb h hs
    exact ihle m hm body Interp.size_block s f (stk.take np) (nr :: labels) ret ob cb hS hb' htb h hs
  · intro r hev vs hvs
    obtain ⟨hok, -⟩ := (Interp.evalH_good (P := profile o) hH hev).1 hS hb'
    exact ⟨Interp.blockVals_length hok hob hvs, fun ws hws => by
      rw [hws] at hok; exact Interp.length_of_ends hok hob⟩
  · intro s₁ f₁ fl vs m hm hev hvs hk
    obtain ⟨hok, inv1⟩ := (Interp.evalH_good (P := profile o) hH hev).1 hS hb'
    have hnr := Interp.blockVals_length hok hob hvs
    have hnorm : ∀ ws, fl = .normal ws → ws.length = nr := by
      rintro ws rfl; exact Interp.length_of_ends hok hob
    have h2' := Interp.chk_after (ext := Interp.noExt) inv1 hp hnr h2
    -- the forward run to the continuation
    obtain ⟨c', o', hbr, he, hm'⟩ :=
      Interp.run_of_wp ((Interp.evalH_good (P := profile o) hH hev).2 hS hb')
    have htg := Interp.tg_block_vals (P := profile o) (host := host)
      (rest := expression (Binaryen.BExpr.lowerList es)) har hp hbr he hm' hvs hnr hnorm
    have ht₁ := ContextTyped.steps_typed hT (hcode ▸ ht) htg.to_reflTransGen
    exact ihle m hm es Interp.size_tail s₁ f₁ _ labels ret out c (Interp.storeChk_inv inv1 hS) h2'
      ht₁ hk hend

/-- **The loop case.** -/
theorem case_loop (hT : HostTyped host) (hH : Interp.NativeHostSlice host) {n : Nat}
    {bt : BlockType} {body es : List Binaryen.BExpr}
    (ihlt : ∀ m < n, ∀ es', BackGoal o host m es')
    (ihle : ∀ m ≤ n, ∀ es', sizeOf es' < sizeOf (Binaryen.BExpr.loop bt body :: es) →
      BackGoal o host m es') :
    BackGoal o host n (.loop bt body :: es) := by
  intro s f stk labels ret out c hS hc ht hrun hend
  obtain ⟨o₁, h1, h2⟩ := Interp.chk_consE.mp hc
  obtain ⟨np, nr, hba, hp, hbody, rfl⟩ := Interp.chk1_loopE h1
  have har : Binaryen.arity f bt = some (np, nr) := (Interp.arity_eq f bt).trans hba
  obtain ⟨ob, hb, hob⟩ := Interp.endsAt_eq hbody
  have hb' : Interp.chk s.funcs f.module f.locals.length ret (np :: labels)
      (some (stk.take np).length) body = some ob := by
    rw [Interp.take_length_of_le hp]; exact hb
  have hcode := Interp.code_loop (body := body) stk bt es
  have henter := Interp.steps_enter (P := profile o) (host := host) (s := s) (f := f)
    (B := Binaryen.BExpr.lowerList body) hp (Interp.step_loop har)
    (expression (Binaryen.BExpr.lowerList es))
  have htb : Sim.ContextTyped ⟨s, f, vals (stk.take np).reverse ++
      expression (Binaryen.BExpr.lowerList body)⟩ :=
    Sim.ContextTyped.label (ContextTyped.steps_typed hT (hcode ▸ ht) henter)
  -- the forward run of the body inside the loop's label
  have hinner : ∀ s₁ f₁ fl, EvalH host s f (stk.take np) body (s₁, f₁, fl) →
      ∃ c' o', Steps (profile o) host ⟨s, f, vals stk.reverse ++ expression
          (Binaryen.BExpr.lowerList (.loop bt body :: es))⟩
        ⟨s₁, f₁, vals (stk.drop np).reverse ++
          [.label np [.loop bt (Binaryen.BExpr.lowerList body)] c'] ++
          expression (Binaryen.BExpr.lowerList es)⟩ ∧ o'.Ends c' ∧ Interp.FlowMatch fl o' := by
    intro s₁ f₁ fl hev
    obtain ⟨c', o', hbr, he, hm'⟩ :=
      Interp.run_of_wp ((Interp.evalH_good (P := profile o) hH hev).2 hS hb')
    refine ⟨c', o', ?_, he, hm'⟩
    rw [hcode]
    exact henter.trans (Silmaril.Wasm.Logic.Core.Steps.ctx _ _
      (Silmaril.Wasm.Logic.Core.Steps.label np _ hbr))
  refine back_loop_tree har hp hrun hend ?_ ?_ ?_ ?_
  · intro m hm cb h hs
    exact ihle m hm.le body Interp.size_loop s f (stk.take np) (np :: labels) ret ob cb hS hb' htb h hs
  · intro r hev
    obtain ⟨hok, -⟩ := (Interp.evalH_good (P := profile o) hH hev).1 hS hb'
    refine ⟨fun ws hws => ?_, fun vs hvs => ?_⟩
    · rw [hws] at hok; exact Interp.length_of_ends hok hob
    · rw [hvs] at hok
      obtain ⟨k, hk, hkl⟩ := hok
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      omega
  · intro s₁ f₁ vs m hm hev hk
    obtain ⟨hok, inv1⟩ := (Interp.evalH_good (P := profile o) hH hev).1 hS hb'
    have hlen : vs.length = nr := Interp.length_of_ends hok hob
    have h2' := Interp.chk_after (ext := Interp.noExt) (vs := vs) inv1 hp hlen.ge h2
    obtain ⟨c', o', hst, he, hm'⟩ := hinner s₁ f₁ _ hev
    have hx := Interp.exit_normal (P := profile o) (host := host) (s₁ := s₁) (f₁ := f₁) (n := np)
      (cont := [.loop bt (Binaryen.BExpr.lowerList body)]) he hm' (stk.drop np).reverse
      (expression (Binaryen.BExpr.lowerList es))
    have htake : vs.take nr = vs := List.take_of_length_le hlen.le
    have ht₁ : Sim.ContextTyped ⟨s₁, f₁, vals (vs.take nr ++ stk.drop np).reverse ++
        expression (Binaryen.BExpr.lowerList es)⟩ := by
      have := ContextTyped.steps_typed hT ht (hst.trans hx)
      rw [htake]
      simpa [List.reverse_append, List.append_assoc] using this
    exact ihle m hm.le es Interp.size_tail s₁ f₁ _ labels ret out c (Interp.storeChk_inv inv1 hS)
      h2' ht₁ hk hend
  · intro s₁ f₁ vs m hm hev hk
    obtain ⟨hok, inv1⟩ := (Interp.evalH_good (P := profile o) hH hev).1 hS hb'
    have hnp : np ≤ vs.length := by
      obtain ⟨k, hk, hkl⟩ := hok
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      omega
    obtain ⟨c', o', hst, he, hm'⟩ := hinner s₁ f₁ _ hev
    have hx := Interp.exit_br0 (P := profile o) (host := host) (s₁ := s₁) (f₁ := f₁) (n := np)
      (cont := [.loop bt (Binaryen.BExpr.lowerList body)]) he hm' hnp (stk.drop np).reverse
      (expression (Binaryen.BExpr.lowerList es))
    have ht₁ : Sim.ContextTyped ⟨s₁, f₁, vals (vs.take np ++ stk.drop np).reverse ++
        expression (Binaryen.BExpr.lowerList (.loop bt body :: es))⟩ := by
      have := ContextTyped.steps_typed hT ht (hst.trans hx)
      rw [Interp.code_loop]
      simpa [List.reverse_append, List.append_assoc, expression] using this
    have hlen : (vs.take np ++ stk.drop np).length = stk.length := by
      simp only [List.length_append, List.length_take, List.length_drop]; omega
    have hc' : Interp.chk s₁.funcs f₁.module f₁.locals.length ret labels
        (some (vs.take np ++ stk.drop np).length) (.loop bt body :: es) = some out := by
      rw [hlen]; exact Interp.chk_inv inv1 hc
    exact ihlt m hm _ s₁ f₁ _ labels ret out c (Interp.storeChk_inv inv1 hS) hc' ht₁ hk hend

/-- **The `if` case.** -/
theorem case_if (hT : HostTyped host) (hH : Interp.NativeHostSlice host) {n : Nat}
    {bt : BlockType} {cnd t el es : List Binaryen.BExpr}
    (ihle : ∀ m ≤ n, ∀ es', sizeOf es' < sizeOf (Binaryen.BExpr.if_ bt cnd t el :: es) →
      BackGoal o host m es') :
    BackGoal o host n (.if_ bt cnd t el :: es) := by
  intro s f stk labels ret out c hS hc ht hrun hend
  obtain ⟨o₁, h1, h2⟩ := Interp.chk_consE.mp hc
  obtain ⟨oc, hco, hk1⟩ := Interp.chk1_ifE h1
  have hcode := Interp.code_if stk bt cnd t el es
  have htc : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList cnd)⟩ :=
    Sim.ContextTyped.suffix (hcode ▸ ht)
  -- after the condition: the Core run, its typing, and the block arity of `bt`
  have hafter : ∀ s₁ f₁ stk', EvalH host s f stk cnd (s₁, f₁, .normal stk') →
      Steps (profile o) host ⟨s, f, vals stk.reverse ++ expression
          (Binaryen.BExpr.lowerList (.if_ bt cnd t el :: es))⟩
        ⟨s₁, f₁, vals stk'.reverse ++
          .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) ::
          expression (Binaryen.BExpr.lowerList es)⟩ := by
    intro s₁ f₁ stk' hev
    rw [hcode]
    exact Silmaril.Wasm.Logic.Core.Steps.append _ (run_of_evalH (o := o) hH hev hS hco)
  have harity : ∀ s₁ f₁ stk', EvalH host s f stk cnd (s₁, f₁, .normal stk') →
      ∃ np nr, Binaryen.arity f₁ bt = some (np, nr) := by
    intro s₁ f₁ stk' hev
    obtain ⟨hoc, inv1⟩ := (Interp.evalH_good (P := profile o) hH hev).1 hS hco
    obtain ⟨np, nr, ha, -⟩ := hk1 _ hoc
    exact ⟨np, nr, by rw [Interp.arity_eq, inv1.2.1]; exact ha⟩
  -- the facts after the condition, for a chosen arm
  have hinfo : ∀ s₁ f₁ cv stk₁ b np nr, EvalH host s f stk cnd (s₁, f₁, .normal (cv :: stk₁)) →
      Binaryen.truthy cv = some b → Binaryen.arity f₁ bt = some (np, nr) →
      Interp.EvalInv s f (s₁, f₁, .normal (cv :: stk₁)) ∧ np ≤ stk₁.length ∧
      (∃ ob, (ob = none ∨ ob = some nr) ∧
        Interp.chk s₁.funcs f₁.module f₁.locals.length ret (nr :: labels)
          (some (stk₁.take np).length) (if b then t else el) = some ob) ∧
      Interp.chk s₁.funcs f₁.module f₁.locals.length ret labels
        (some (stk₁.length - np + nr)) es = some out ∧
      Sim.ContextTyped ⟨s₁, f₁, vals (stk₁.take np).reverse ++
        expression (Binaryen.BExpr.lowerList (if b then t else el))⟩ := by
    intro s₁ f₁ cv stk₁ b np nr hev hb har
    obtain ⟨inv1, hp, hendArm, h2'⟩ :=
      Interp.arity_if_pre (b := b) hS (Interp.evalH_good (P := profile o) hH hev).1 har hc
    obtain ⟨ob, hb', hob⟩ := Interp.endsAt_eq (Interp.chk_inv_endsAt inv1 hendArm)
    have hb'' : Interp.chk s₁.funcs f₁.module f₁.locals.length ret (nr :: labels)
        (some (stk₁.take np).length) (if b then t else el) = some ob := by
      rw [Interp.take_length_of_le hp]; exact hb'
    have ht₁ := ContextTyped.steps_typed hT ht (hafter _ _ _ hev)
    have hif := Interp.step_if_arm (o := o) (s := s₁) (f := f₁) (stk := stk₁) (bt := bt) (t := t)
      (el := el) (rest := expression (Binaryen.BExpr.lowerList es)) hb
    have henter := Interp.steps_enter (P := profile o) (host := Det.noHost) (s := s₁) (f := f₁)
      (B := Binaryen.BExpr.lowerList (if b then t else el)) hp (Interp.step_block har)
      (expression (Binaryen.BExpr.lowerList es))
    refine ⟨inv1, hp, ⟨ob, hob, hb''⟩, Interp.chk_inv inv1 h2', ?_⟩
    exact Sim.ContextTyped.label (Sim.ContextTyped.steps (Sim.ContextTyped.step ht₁ hif) henter)
  refine back_if_tree hrun hend ?_ ?_ ?_ ?_
  · intro m hm c₁ h hs
    exact ihle m hm cnd Interp.size_cond s f stk labels ret oc c₁ hS hco htc h hs
  · intro s₁ f₁ stk' hev
    obtain ⟨np, nr, har⟩ := harity s₁ f₁ stk' hev
    obtain ⟨cv, stk₁, b, rfl, hb⟩ :=
      Interp.truthy_progressH (ContextTyped.steps_typed hT ht (hafter _ _ _ hev))
    obtain ⟨inv1, hp, ⟨ob, hob, hb'⟩, -, -⟩ := hinfo s₁ f₁ cv stk₁ b np nr hev hb har
    refine ⟨cv, stk₁, b, np, nr, rfl, hb, har, hp, fun r hevb vs hvs => ?_⟩
    obtain ⟨hok, -⟩ :=
      (Interp.evalH_good (P := profile o) hH hevb).1 (Interp.storeChk_inv inv1 hS) hb'
    exact ⟨Interp.blockVals_length hok hob hvs, fun ws hws => by
      rw [hws] at hok; exact Interp.length_of_ends hok hob⟩
  · intro s₁ f₁ cv stk₁ b np nr m hm hev hb har cb h hs
    obtain ⟨inv1, hp, ⟨ob, hob, hb'⟩, -, htarm⟩ := hinfo s₁ f₁ cv stk₁ b np nr hev hb har
    exact ihle m hm _ (Interp.size_arm b) s₁ f₁ (stk₁.take np) (nr :: labels) ret ob cb
      (Interp.storeChk_inv inv1 hS) hb' htarm h hs
  · intro s₁ f₁ cv stk₁ b np nr s₂ f₂ fl vs m hm hev hb har hevb hvs hk
    obtain ⟨inv1, hp, ⟨ob, hob, hb'⟩, h2₁, -⟩ := hinfo s₁ f₁ cv stk₁ b np nr hev hb har
    have hS₁ := Interp.storeChk_inv inv1 hS
    obtain ⟨hok, inv2⟩ := (Interp.evalH_good (P := profile o) hH hevb).1 hS₁ hb'
    have hnr := Interp.blockVals_length hok hob hvs
    have hnorm : ∀ ws, fl = .normal ws → ws.length = nr := by
      rintro ws rfl; exact Interp.length_of_ends hok hob
    have h2₂ := Interp.chk_after (ext := Interp.noExt) inv2 hp hnr h2₁
    obtain ⟨c', o', hbr, he, hm'⟩ :=
      Interp.run_of_wp ((Interp.evalH_good (P := profile o) hH hevb).2 hS₁ hb')
    have htg := Interp.tg_block_vals (P := profile o) (host := host)
      (rest := expression (Binaryen.BExpr.lowerList es)) har hp hbr he hm' hvs hnr hnorm
    have hif := Interp.step_if_arm (o := o) (s := s₁) (f := f₁) (stk := stk₁) (bt := bt) (t := t)
      (el := el) (rest := expression (Binaryen.BExpr.lowerList es)) hb
    have hrun₂ := (hafter _ _ _ hev).trans
      ((Relation.ReflTransGen.single (Step.of_noHost host hif)).trans htg.to_reflTransGen)
    exact ihle m hm es Interp.size_tail s₂ f₂ _ labels ret out c
      (Interp.storeChk_inv (inv1.trans inv2) hS) h2₂ (ContextTyped.steps_typed hT ht hrun₂) hk hend

end Silmaril.Proofs.Wasm.Abstract.HostEval
