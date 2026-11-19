module

public import Silmaril.Proofs.Wasm.Cfg.MachineLProd

@[expose] public section

/-!
# Productive machine runs are productive native runs (H2, proofs)

`machine_infL`: a productive run of the machine (`ProdL`) from the CFG entry is a productive run of
the body (`InfLXP`) with the same stream. By strong induction on the size of the remaining
code (`pb_step`, `pa_step`), over positions of the run that never leave their sequence: an arm the
run never leaves is a descent; an arm it leaves forward is a finished instruction (`infL_cons`, its
native run read by `MachineLRel.arm_fwd`); a loop re-entered infinitely often is `loopInf`, its
iterations read by `arm_fwd`; finitely many re-entries are `loopBack`.
-/

namespace Silmaril.Wasm.Cfg.Proofs.MachineLProdB

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.Shape
open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Abstract (EvalLXPS EvalLXPh SCall OCall InfLXP evalLXPS_canonical)
open Silmaril.Wasm.Abstract.CallXP (POut)
open Silmaril.Wasm.Cfg.Proofs.MachineLBwd (lift_op lift_if nil_inv)
open Silmaril.Wasm.Cfg.Proofs.MachineLLogDivB (nil_normal canon)

variable {H : Type}

/-! ## A finished instruction, then a productive rest -/

/-- **One instruction run natively to a normal end, then a productive rest**, is a productive run
with the head's log in front (the `…K` constructors, and `loopBack` for loop iterations). -/
theorem infL_cons {s : Store H} {f : Frame} {N : List Val} {es : List BExpr}
    {l : List (SCall H)} {r : Store H × Frame × POut} (h : EvalLXPS s f N es l r) :
    ∀ {e : Instr} {rest : List BExpr} {s₂ : Store H} {f₂ : Frame} {N₂ : List Val}
      {ω₂ : ℕ → OCall H}, es = [liftInstr e] → r = (s₂, f₂, .flow (.normal N₂)) →
      InfLXP s₂ f₂ N₂ rest ω₂ →
      ∃ L₁, l = L₁.map OCall.toS ∧ InfLXP s f N (liftInstr e :: rest) (L₁ ++ω ω₂) := by
  induction h with
  | @callRet s s₁ s₂ f f₁ stk stk₁ ws x args es a fi ps rs l₁ l₂ r hargs hfi hty hk _ _ =>
    intro e rest s₂' f₂ N₂ ω₂ hes hr hL
    obtain ⟨hhd, rfl⟩ := List.cons.inj hes
    obtain ⟨-, rfl, -⟩ := lift_op hhd.symm
    rw [← hhd]
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_normal hargs
    subst hr
    obtain ⟨rfl, rfl, h3, rfl⟩ := nil_inv hk
    simp only [POut.flow.injEq, Flow.normal.injEq] at h3; subst h3
    exact ⟨[OCall.mk a (stk.take ps.length).reverse s (.inl ws) s₂'], by simp,
      by simpa using InfLXP.callK .nil hfi hty hL⟩
  | @indRet s s₁ s₂ f f₁ stk stk₁ ws x y args es ad iv fa fi ps rs l₁ l₂ r hargs hres hfi hty hy hk
      _ _ =>
    intro e rest s₂' f₂ N₂ ω₂ hes hr hL
    obtain ⟨hhd, rfl⟩ := List.cons.inj hes
    obtain ⟨-, rfl, -⟩ := lift_op hhd.symm
    rw [← hhd]
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_normal hargs
    subst hr
    obtain ⟨rfl, rfl, h3, rfl⟩ := nil_inv hk
    simp only [POut.flow.injEq, Flow.normal.injEq] at h3; subst h3
    exact ⟨[OCall.mk fa (stk₁.take ps.length).reverse s (.inl ws) s₂'], by simp,
      by simpa using InfLXP.indK .nil hres hfi hty hy hL⟩
  | @refRet s s₁ s₂ f f₁ stk stk₁ ws y args es fa fi ps rs l₁ l₂ r hargs hfi hty hy hk _ _ =>
    intro e rest s₂' f₂ N₂ ω₂ hes hr hL
    obtain ⟨hhd, rfl⟩ := List.cons.inj hes
    obtain ⟨-, rfl, -⟩ := lift_op hhd.symm
    rw [← hhd]
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_normal hargs
    subst hr
    obtain ⟨rfl, rfl, h3, rfl⟩ := nil_inv hk
    simp only [POut.flow.injEq, Flow.normal.injEq] at h3; subst h3
    exact ⟨[OCall.mk fa (stk₁.take ps.length).reverse s (.inl ws) s₂'], by simp,
      by simpa using InfLXP.refK .nil hfi hty hy hL⟩
  | opOk hi hargs hflat hk _ _ =>
    intro e rest s₂' f₂ N₂ ω₂ hes hr hL
    obtain ⟨hhd, rfl⟩ := List.cons.inj hes
    obtain ⟨-, rfl, -⟩ := lift_op hhd.symm
    rw [← hhd]
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_normal hargs
    subst hr
    obtain ⟨rfl, rfl, h3, rfl⟩ := nil_inv hk
    simp only [POut.flow.injEq, Flow.normal.injEq] at h3; subst h3
    exact ⟨[], by simp, by simpa using InfLXP.opK hi .nil hflat hL⟩
  | blockOk har hbody hvs hk _ _ =>
    intro e rest s₂' f₂ N₂ ω₂ hes hr hL
    obtain ⟨hhd, rfl⟩ := List.cons.inj hes
    rw [← hhd]
    subst hr
    obtain ⟨rfl, rfl, h3, rfl⟩ := nil_inv hk
    simp only [POut.flow.injEq, Flow.normal.injEq] at h3; subst h3
    obtain ⟨L₁, rfl, h₁⟩ := canon hbody hvs
    exact ⟨L₁, by simp, .blockK har h₁ hvs hL⟩
  | loopOk har hbody hk _ _ =>
    intro e rest s₂' f₂ N₂ ω₂ hes hr hL
    obtain ⟨hhd, rfl⟩ := List.cons.inj hes
    rw [← hhd]
    subst hr
    obtain ⟨rfl, rfl, h3, rfl⟩ := nil_inv hk
    simp only [POut.flow.injEq, Flow.normal.injEq] at h3; subst h3
    obtain ⟨L₁, rfl, h₁⟩ := canon hbody (vs := _) rfl
    exact ⟨L₁, by simp, .loopK har h₁ hL⟩
  | loopBack har hbody hk _ ihk =>
    intro e rest s₂' f₂ N₂ ω₂ hes hr hL
    obtain ⟨hhd, rfl⟩ := List.cons.inj hes
    obtain ⟨L₁', rfl, hL'⟩ := ihk hes hr hL
    rw [← hhd] at hL' ⊢
    obtain ⟨L₁, rfl, h₁⟩ := canon hbody (vs := _) rfl
    exact ⟨L₁ ++ L₁', by simp, by simpa [streamAppend_append] using InfLXP.loopBack har h₁ hL'⟩
  | ifOk hc hb har harm hvs hk _ _ _ =>
    intro e rest s₂' f₂ N₂ ω₂ hes hr hL
    obtain ⟨hhd, rfl⟩ := List.cons.inj hes
    obtain ⟨t₀, e₀, -, rfl, rfl, rfl⟩ := lift_if hhd.symm
    rw [← hhd]
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_normal hc
    subst hr
    obtain ⟨rfl, rfl, h3, rfl⟩ := nil_inv hk
    simp only [POut.flow.injEq, Flow.normal.injEq] at h3; subst h3
    obtain ⟨L₁, rfl, h₁⟩ := canon harm hvs
    exact ⟨L₁, by simp, by simpa using InfLXP.ifK .nil hb har h₁ hvs hL⟩
  | tryOk har hbody hvs hk _ _ =>
    intro e rest s₂' f₂ N₂ ω₂ hes hr hL
    obtain ⟨hhd, rfl⟩ := List.cons.inj hes
    rw [← hhd]
    subst hr
    obtain ⟨rfl, rfl, h3, rfl⟩ := nil_inv hk
    simp only [POut.flow.injEq, Flow.normal.injEq] at h3; subst h3
    obtain ⟨L₁, rfl, h₁⟩ := canon hbody hvs
    exact ⟨L₁, by simp, .tryK har h₁ hvs hL⟩
  | blockEsc _ _ ho _ | loopEsc _ _ ho _ | ifEsc _ _ _ _ ho _ _ | tryEsc _ _ ho _ _ =>
    intro e rest s₂' f₂ N₂ ω₂ hes hr
    simp only [Prod.mk.injEq] at hr
    obtain ⟨-, -, rfl⟩ := hr
    exact absurd ho (by simp [POut.Escapes, Flow.Escapes])
  | ifAbort _ ho _ =>
    intro e rest s₂' f₂ N₂ ω₂ hes hr
    simp only [Prod.mk.injEq] at hr
    obtain ⟨-, -, rfl⟩ := hr
    exact absurd trivial ho
  | argsAbort _ ho _ =>
    intro e rest s₂' f₂ N₂ ω₂ hes hr
    simp only [Prod.mk.injEq] at hr
    obtain ⟨-, -, rfl⟩ := hr
    exact absurd trivial ho
  | opStop _ _ _ hfl _ =>
    intro e rest s₂' f₂ N₂ ω₂ hes hr
    simp only [Prod.mk.injEq, POut.flow.injEq] at hr
    obtain ⟨-, -, rfl⟩ := hr
    exact absurd trivial hfl
  | nil => intro e rest s₂' f₂ N₂ ω₂ hes; simp at hes
  | _ => intro e rest s₂' f₂ N₂ ω₂ hes hr; simp at hr


/-! ## Tails of the run's stream -/

open Silmaril.Wasm.Cfg.Proofs.MachineLLogDivP (segLog segLog_add segLog_one)
open Silmaril.Wasm.Cfg.Proofs.MachineLProd (flatMap_range segLog_prefix toSS)

section Tails

variable (lg : ℕ → List (SCall H)) (ν : ℕ → SCall H)

/-- The stream from step `k` on. -/
def tail (k : ℕ) : ℕ → SCall H := fun i => ν ((segLog lg 0 k).length + i)

theorem tail_zero : tail lg ν 0 = ν := by funext i; simp [tail, segLog]

variable {lg ν}

theorem tail_succ (hν : StreamConcat lg ν) (k : ℕ) : tail lg ν k = lg k ++ω tail lg ν (k + 1) := by
  funext i
  have hp := hν.1 (k + 1)
  rw [flatMap_range, segLog_add lg 0 k 1, segLog_one, zero_add] at hp
  simp only [tail, streamAppend]
  split
  · next hi =>
    rw [hp _ (by simp; omega)]
    simp [List.getElem_append_right]
  · next hi =>
    congr 1
    rw [segLog_add lg 0 k 1, segLog_one]
    simp; omega

theorem tail_seg (hν : StreamConcat lg ν) (a : ℕ) :
    ∀ n, tail lg ν a = segLog lg a n ++ω tail lg ν (a + n)
  | 0 => by simp [segLog, streamAppend_nil]
  | n + 1 => by
    rw [tail_seg hν a n, tail_succ hν (a + n), ← streamAppend_append, segLog_add lg a n 1,
      segLog_one, show a + (n + 1) = a + n + 1 by omega]

theorem segLog_length_mono {a b : ℕ} (h : a ≤ b) :
    (segLog lg 0 a).length ≤ (segLog lg 0 b).length :=
  (segLog_prefix lg h).length_le

end Tails

/-! ## Sizes of code -/

theorem sizeOf_append_lt {l₁ l₂ : List Instr} (h : l₁ ≠ []) : sizeOf l₂ < sizeOf (l₁ ++ l₂) := by
  induction l₁ with
  | nil => exact absurd rfl h
  | cons a l ih =>
    simp only [List.cons_append, List.cons.sizeOf_spec]
    rcases l with _ | ⟨b, l⟩
    · simp
    · have := ih (by simp); omega

theorem sizeOf_armOf {t : Instr} {a : Nat} {c : List Instr} (h : armOf t a = some c) :
    sizeOf c < sizeOf t := by
  match t, a, h with
  | .block _ b, 0, h => simp only [armOf, Option.some.injEq] at h; subst h; simp
  | .loop _ b, 0, h => simp only [armOf, Option.some.injEq] at h; subst h; simp
  | .tryTable _ _ b, 0, h => simp only [armOf, Option.some.injEq] at h; subst h; simp
  | .if_ _ t _, 0, h => simp only [armOf, Option.some.injEq] at h; subst h; simp; omega
  | .if_ _ _ e, 1, h => simp only [armOf, Option.some.injEq] at h; subst h; simp

/-! ## Positions of a productive run -/

open Silmaril.Wasm.Cfg.Proofs.Machine (restAt_cons restAt_end restAt_zero lookup_eq)
open Silmaril.Wasm.Cfg.Proofs.MachineLFwd
open Silmaril.Wasm.Cfg.Proofs.MachineLBwd (Pos pos_next pos_term isStruct_terminator lift_block
  lift_loop lift_try seg_wf armOf_if armOf_if' liftInstrs_ite)
open Silmaril.Wasm.Cfg.Proofs.MachineLRel (MStepS DispS MRunS ExitB arm_fwd run_props)
open Silmaril.Wasm.Cfg.Proofs.MachineLDivI (gotoN_lbls gotoN_contRev_block gotoN_entry_block
  dispS_own wrap_one pos_start lift_rest seg_of_lookup')
open Silmaril.Wasm.Cfg.Proofs.MachineLLogDivP (StaysT ResT resT_of mrunS_of)
open Silmaril.Wasm.Cfg.Proofs.MachineLDivB (gotoN_entry)
open Silmaril.Wasm.Cfg.Proofs.MachineLLogDiv (ne_trap_of_blockVals)

/-- A loop's arm, or any structured instruction's arm, entered: the descent constructor. -/
theorem descendI {s : Store H} {f : Frame} {W V' : List Val} {t : Instr} {bt : BlockType}
    {loop tryT : Bool} {cs : List Catch} {a : Nat} {c' : List Instr} {np nr : Nat}
    {rest : List BExpr} {ω : ℕ → OCall H} (hk : StructKind t bt loop tryT cs)
    (hsel : ArmSel t W a V') (harm : armOf t a = some c') (har : arity f bt = some (np, nr))
    (hd : InfLXP s f (V'.take np) (liftInstrs c') ω) :
    InfLXP s f W (liftInstr t :: rest) ω := by
  cases hk with
  | block =>
    cases hsel
    simp only [armOf, Option.some.injEq] at harm; subst harm
    exact .block har hd
  | loop =>
    cases hsel
    simp only [armOf, Option.some.injEq] at harm; subst harm
    exact .loop har hd
  | tryTable =>
    cases hsel
    simp only [armOf, Option.some.injEq] at harm; subst harm
    exact .handler har hd
  | if_ =>
    cases hsel with
    | cond hb =>
      have hc' := armOf_if harm; subst hc'
      rw [← liftInstrs_ite] at hd
      simpa [liftInstr, streamAppend_nil] using InfLXP.arm .nil hb har hd
    | plain hi => exact absurd rfl (hi _ _ _)

section Run

variable (body : Expr) (g : ℕ → MState H) (lg : ℕ → List (SCall H)) (ν : ℕ → SCall H)

/-- **The B claim at size `μ`**: at a block of a sequence the run never leaves, the rest of the
sequence runs productively with the step's remaining log then the later steps' logs. -/
def PBC (μ : Nat) : Prop :=
  ∀ (n : Nat) (post : List Instr) (p : List SeqStep) (c : List Instr) (i : Nat) (sg : Segment)
    (pre : List Instr) (ls : List LFrame) (s : Store H) (f : Frame) (W : List Val)
    (l' : List (SCall H)), sizeOf (post ++ restAt c (i + 1)) = μ →
    Pos body p c i sg pre post → FramesOk body p.reverse ls →
    (∀ m, n < m → StaysT body g lg p.length m) → ResT body g n p i sg post ls s f W l' →
    ∃ ω, InfLXP s f W (liftInstrs post ++ liftInstrs (restAt c (i + 1))) ω ∧
      l' ++ω tail lg ν (n + 1) = toSS ω

/-- **The A claim at size `μ`**: at the entry of an arm of a structured instruction, in a sequence
the run never leaves, the instruction and the rest run productively with the later logs. -/
def PAC (μ : Nat) : Prop :=
  ∀ (n : Nat) (p : List SeqStep) (c : List Instr) (i : Nat) (sg : Segment) (pre : List Instr)
    (t : Instr) (bt : BlockType) (loop tryT : Bool) (cs : List Catch) (a : Nat) (c' : List Instr)
    (V' : List Val) (np nr : Nat) (ls : List LFrame) (s : Store H) (f : Frame) (W : List Val),
    sizeOf (t :: restAt c (i + 1)) = μ →
    Pos body p c i sg pre [t] → StructKind t bt loop tryT cs → FramesOk body p.reverse ls →
    ArmSel t W a V' → armOf t a = some c' → arity f bt = some (np, nr) →
    gotoN (entry body (p ++ [(i, a)]) 0) (p.length + 1)
      (⟨if loop then np else nr, (V'.drop np).reverse, loop, tryT, cs, bt⟩ :: ls)
      (V'.take np).reverse s f = some (g n) →
    p.length ≤ (g n).lbls.length → (∀ m, n ≤ m → StaysT body g lg p.length m) →
    ∃ ω, InfLXP s f W (liftInstr t :: liftInstrs (restAt c (i + 1))) ω ∧ tail lg ν n = toSS ω

end Run

theorem staysT_block {body : Expr} {g : ℕ → MState H} {lg : ℕ → List (SCall H)} {δ m : ℕ}
    (h : StaysT body g lg δ m) : ∃ b, (g m).node = .block b := by
  obtain ⟨b, _, _, _, _, hb⟩ := h.2.block
  exact ⟨b, by rw [hb]⟩

/-- **A block start at time `m`, the run never leaving its sequence**: the B claim there. -/
theorem blk_at_inf {body : Expr} {g : ℕ → MState H} {lg : ℕ → List (SCall H)}
    {ν : ℕ → SCall H} (hν : StreamConcat lg ν) {μ m : ℕ} {p : List SeqStep} {c : List Instr}
    {j : Nat} {sg : Segment} {W : List Val} {ls : List LFrame} {s : Store H} {f : Frame}
    (hB : PBC body g lg ν μ) (hμ : sizeOf (restAt c j) = μ)
    (hgm : g m = ⟨.block ⟨p, j⟩, W.reverse, ls, s, f⟩) (hc : seqAt body p = some c)
    (hsg : (segment c)[j]? = some sg) (hok : FramesOk body p.reverse ls)
    (hstay : ∀ k, m ≤ k → StaysT body g lg p.length k) :
    ∃ ω, InfLXP s f W (liftInstrs (restAt c j)) ω ∧ tail lg ν m = toSS ω := by
  have hls : ls.length = p.length := by simpa using Proofs.Machine.framesOk_length _ _ hok
  have hlk : lookup body ⟨p, j⟩ = some sg := by rw [lookup_eq]; simp [hc, hsg]
  have hres := resT_of hgm hls hlk (hstay m le_rfl)
  rw [List.reverse_reverse] at hres
  obtain ⟨ω, hd, hω⟩ := hB m sg.instrs p c j sg [] ls s f W (lg m)
    (by rw [← hμ, restAt_cons hsg]) (pos_start hc hsg) hok (fun k hk => hstay k (by omega)) hres
  refine ⟨ω, by rwa [lift_rest hsg], ?_⟩
  rw [tail_succ hν m]; exact hω

theorem sizeOf_cons_lt (e : Instr) (l : List Instr) : sizeOf l < sizeOf (e :: l) := by
  simp

/-- **The B step**: the B claim at `μ`, from the A claim at `μ` and the B claim below `μ`. -/
theorem pb_step {body : Expr} {g : ℕ → MState H} {lg : ℕ → List (SCall H)} {ν : ℕ → SCall H}
    (hν : StreamConcat lg ν) {μ : Nat}
    (hA : PAC body g lg ν μ) (ihB : ∀ μ' < μ, PBC body g lg ν μ') : PBC body g lg ν μ := by
  intro n post p c i sg pre ls s f W l' hμ hp hok hstay hres
  have hls : ls.length = p.length := by simpa using Proofs.Machine.framesOk_length _ _ hok
  rcases post with _ | ⟨e, post'⟩
  · exact absurd rfl hp.hpost
  simp only [liftInstrs, List.cons_append]
  simp only [List.cons_append] at hμ
  rcases hres with ⟨r', hr', ht, hd⟩ |
    ⟨X, t, s₁, f₁, V, a, c', V', np, nr, bt, loop, tryT, cs, hpost, hterm, hk, hX, hsel, harm,
      har, hgo, hdep⟩
  · obtain ⟨s', f', o⟩ := r'
    have hse : ¬ Instr.IsStruct e := fun h => ht e (pos_term hp (isStruct_terminator h)).1 h
    have hsp := MachineLSeq.split [liftInstr e] (liftInstrs post') (by simpa [liftInstrs] using hr')
    rcases hsp with ⟨s₂, f₂, N₂, l₁, l₂, h₁, h₂, rfl⟩ | ⟨-, hn'⟩
    · cases post' with
      | cons e' post'' =>
        obtain ⟨ω₂, hd₂, hω₂⟩ := ihB _ (by rw [← hμ]; exact sizeOf_cons_lt e _) n (e' :: post'')
          p c i sg (pre ++ [e]) ls s₂ f₂ N₂ l₂ rfl (pos_next hp hse) hok hstay
          (.inl ⟨_, h₂, ht, hd⟩)
        obtain ⟨L₁, rfl, hd₁⟩ := infL_cons h₁ rfl rfl hd₂
        exact ⟨L₁ ++ω ω₂, hd₁, by
          rw [Proofs.MachineLProd.toSS_append, ← hω₂, streamAppend_append]⟩
      | nil =>
        obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_inv (by simpa [liftInstrs] using h₂)
        cases hd with
        | next hg hδ =>
          obtain ⟨hlk, hgn⟩ := gotoN_entry_block hg (staysT_block (hstay (n + 1) (by omega))) hδ hls
          obtain ⟨sg', hsg'⟩ := Option.isSome_iff_exists.mp hlk
          obtain ⟨ω₂, hd₂, hω₂⟩ := blk_at_inf hν
            (ihB _ (by rw [← hμ]; exact sizeOf_cons_lt e _)) rfl hgn hp.hc
            (seg_of_lookup' hp.hc hsg') hok (fun k hk => hstay k (by omega))
          obtain ⟨L₁, rfl, hd₁⟩ := infL_cons h₁ rfl rfl hd₂
          exact ⟨L₁ ++ω ω₂, by simpa [liftInstrs] using hd₁, by
            rw [Proofs.MachineLProd.toSS_append, ← hω₂]; simp⟩
    · rw [← hls] at hd; exact absurd (dispS_own hd) hn'
  · cases X with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hpost
      obtain ⟨rfl, rfl⟩ := hpost
      obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_normal (by simpa [liftInstrs] using hX)
      obtain ⟨ω, hd, hω⟩ := hA (n + 1) p c i sg pre e bt loop tryT cs a c' V' np nr ls s f W
        (by simpa using hμ) hp hk hok hsel harm har hgo hdep (fun m hm => hstay m (by omega))
      exact ⟨ω, by simpa [liftInstrs] using hd, by simpa [streamAppend_nil] using hω⟩
    | cons e₀ X' =>
      simp only [List.cons_append, List.cons.injEq] at hpost
      obtain ⟨rfl, rfl⟩ := hpost
      have hse : ¬ Instr.IsStruct e := by
        intro h
        have hterm' := isStruct_terminator h
        have hbody : e ∈ sg.body := by
          have h1 := hp.hinstrs
          simp only [Segment.instrs, hterm, Option.toList_some] at h1
          have h2 : sg.body = pre ++ e :: X' := by
            have h3 : sg.body ++ [t] = (pre ++ e :: X') ++ [t] := by simpa using h1
            exact List.append_cancel_right h3
          rw [h2]; simp
        have := (seg_wf hp.hsg).1 e hbody
        rw [hterm'] at this; cases this
      have hsp := MachineLSeq.split [liftInstr e] (liftInstrs X') (by simpa [liftInstrs] using hX)
      rcases hsp with ⟨s₂, f₂, N₂, l₁, l₂, h₁, h₂, rfl⟩ | ⟨-, hn'⟩
      · obtain ⟨e', post'', heq⟩ : ∃ e' post'', X' ++ [t] = e' :: post'' := by
          cases X' with
          | nil => exact ⟨t, [], rfl⟩
          | cons x xs => exact ⟨x, xs ++ [t], rfl⟩
        have hp' := hp
        rw [heq] at hp'
        obtain ⟨ω₂, hd₂, hω₂⟩ := ihB _ (by rw [← hμ, heq]; exact sizeOf_cons_lt e _) n (e' :: post'')
          p c i sg (pre ++ [e]) ls s₂ f₂ N₂ l₂ rfl (pos_next hp' hse) hok hstay
          (.inr ⟨X', t, s₁, f₁, V, a, c', V', np, nr, bt, loop, tryT, cs, heq.symm, hterm, hk, h₂,
            hsel, harm, har, hgo, hdep⟩)
        obtain ⟨L₁, rfl, hd₁⟩ := infL_cons h₁ rfl rfl hd₂
        refine ⟨L₁ ++ω ω₂, by rw [heq]; exact hd₁, ?_⟩
        rw [Proofs.MachineLProd.toSS_append, ← hω₂, streamAppend_append]
      · exact absurd trivial hn'

/-- **The first step leaving an arm**: it finishes the instruction forward (the claim at the arm's
entry), or, for a loop, re-enters it (a native iteration, then the arm's entry again). -/
theorem first_leave {body : Expr} {g : ℕ → MState H} {lg : ℕ → List (SCall H)}
    {ν : ℕ → SCall H} (hν : StreamConcat lg ν) {μ : Nat} (hB' : ∀ μ' < μ, PBC body g lg ν μ')
    {p : List SeqStep} {c : List Instr} {i : Nat} {sg sg₀ : Segment} {pre : List Instr}
    {t : Instr} {bt : BlockType} {loop tryT : Bool} {cs : List Catch} {a : Nat}
    {c' : List Instr} {V' : List Val} {np nr : Nat} {ls : List LFrame} {s : Store H} {f : Frame}
    {W : List Val} {r m : ℕ}
    (hμ : sizeOf (t :: restAt c (i + 1)) = μ) (hp : Pos body p c i sg pre [t])
    (hk : StructKind t bt loop tryT cs) (hok : FramesOk body p.reverse ls)
    (hsel : ArmSel t W a V') (harm : armOf t a = some c') (har : arity f bt = some (np, nr))
    (hsg₀ : (segment c')[0]? = some sg₀)
    (hgr : g r = ⟨.block ⟨p ++ [(i, a)], 0⟩, (V'.take np).reverse,
      ⟨if loop then np else nr, (V'.drop np).reverse, loop, tryT, cs, bt⟩ :: ls, s, f⟩)
    (hstay : ∀ k, r ≤ k → StaysT body g lg p.length k) (hrm : r ≤ m)
    (hin : ∀ k, r ≤ k → k < m → StaysT body g lg (p.length + 1) k)
    (hout : ¬ StaysT body g lg (p.length + 1) m) :
    (∃ ω, InfLXP s f W (liftInstr t :: liftInstrs (restAt c (i + 1))) ω ∧
      tail lg ν r = Proofs.MachineLProd.toSS ω) ∨
    (loop = true ∧ ∃ (vs : List Val) (s' : Store H) (f' : Frame) (l : List (OCall H)),
      EvalLXPh s f (V'.take np) (liftInstrs c') l (s', f', .flow (.brk 0 vs)) ∧
      segLog lg r (m + 1 - r) = l.map OCall.toS ∧ arity f' bt = some (np, nr) ∧
      g (m + 1) = ⟨.block ⟨p ++ [(i, a)], 0⟩, ((vs.take np ++ V'.drop np).take np).reverse,
        ⟨np, ((vs.take np ++ V'.drop np).drop np).reverse, true, tryT, cs, bt⟩ :: ls, s', f'⟩) := by
  obtain ⟨ht, -, rfl⟩ := pos_term hp (isStruct_terminator ⟨_, _, _, _, hk⟩)
  have hls : ls.length = p.length := by simpa using Proofs.Machine.framesOk_length _ _ hok
  have hcA : seqAt body (p ++ [(i, a)]) = some c' := by
    rw [Proofs.Machine.seqAt_append]; simp [hp.hc, hp.hsg, ht, harm]
  set L : LFrame := ⟨if loop then np else nr, (V'.drop np).reverse, loop, tryT, cs, bt⟩ with hLdef
  have hokA : FramesOk body ((i, a) :: p.reverse) (L :: ls) := by
    simpa using MachineLBwd.arm_ok hp hk harm hok (if loop then np else nr) (V'.drop np).reverse
  have hrun₁ := mrunS_of (body := body) (G := g) (lg := lg) (δ := p.length + 1) (a := r)
    (m - r) (fun k h1 h2 => (hin k h1 (by omega)).2)
  rw [show r + (m - r) = m by omega] at hrun₁
  obtain ⟨-, hD⟩ := hstay m hrm
  have hok₀ : MInv body (g r) := by
    rw [hgr]; show FramesOk body (p ++ [(i, a)]).reverse (L :: ls); simpa using hokA
  have hd₀ : p.length + 1 ≤ (g r).lbls.length := by rw [hgr]; simp [hls]
  obtain ⟨-, hdm⟩ := run_props hrun₁ hok₀ hd₀
  have hnot : ¬ MStepS body (p.length + 1) (g m) (lg m) (g (m + 1)) := fun h => hout ⟨hdm, h⟩
  rw [hgr] at hrun₁
  obtain ⟨r₀, hrun₀, hex₀⟩ := arm_fwd hcA hokA hrun₁ hD hnot
  rw [List.reverse_reverse] at hrun₀
  obtain ⟨s', f', o⟩ := r₀
  have har₀ : arity f' bt = some (np, nr) :=
    (arity_congr (MachineLSeq.module_eq hrun₀) _).trans har
  have hstay1 : ∀ k, m + 1 ≤ k → StaysT body g lg p.length k := fun k hk => hstay k (by omega)
  have hblk1 := staysT_block (hstay1 (m + 1) le_rfl)
  have hdep1 := hD.depth
  have htl : tail lg ν r = (segLog lg r (m - r) ++ lg m) ++ω tail lg ν (m + 1) := by
    rw [tail_seg hν r (m - r + 1), segLog_add lg r (m - r) 1, segLog_one,
      show r + (m - r) = m by omega, show r + (m - r + 1) = m + 1 by omega]
  have hsz : sizeOf (restAt c (i + 1)) < μ := by rw [← hμ]; exact sizeOf_cons_lt t _
  rcases hex₀ with ⟨ws, ho, hgo⟩ | ⟨ws, L', ho, hL', hbr⟩
  · left
    simp only at ho hgo; subst ho
    rw [show ((i, a) :: p.reverse).length = p.reverse.length + 1 by simp] at hgo
    obtain ⟨np', nr', har', hgo'⟩ :=
      gotoN_cons (Proofs.Machine.depth_contRev_cons body i a _) hgo
    obtain ⟨hlk, hgn1⟩ := gotoN_contRev_block hgo' hblk1 (by simpa using hdep1)
      (by simpa using hls)
    simp only [List.reverse_reverse] at hlk hgn1
    have hw : WrapL L t [] (s', f', .flow (.normal ws)) []
        (s', f', .flow (.normal (L.outer ++ topVals nr' ws.reverse).reverse)) := by
      simpa using wrap_fall (W := ws.reverse) (t := t) (rest := []) har'
        (by simpa [liftInstrs] using
          @EvalLXPS.nil H s' f' (L.outer ++ topVals nr' ws.reverse).reverse)
    have hone := wrap_one hk hsel harm har hrun₀ hw
    obtain ⟨sg', hsg'⟩ := Option.isSome_iff_exists.mp hlk
    obtain ⟨ω₂, hd₂, hω₂⟩ := blk_at_inf hν (hB' _ hsz) rfl
      (by rw [hgn1, List.reverse_reverse]) hp.hc (seg_of_lookup' hp.hc hsg') hok hstay1
    obtain ⟨L₁, hL₁, hd₁⟩ := infL_cons hone rfl rfl hd₂
    refine ⟨L₁ ++ω ω₂, hd₁, ?_⟩
    rw [htl, Proofs.MachineLProd.toSS_append, ← hω₂, ← hL₁]; simp
  · simp only at ho hbr; subst ho
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hL'; subst hL'
    have hlev := Proofs.Machine.levelLoop_of_framesOk 0 _ _ hokA rfl
    simp only [levelLoop, List.drop_zero] at hlev
    simp only [branchR, Option.bind_eq_some_iff] at hbr
    obtain ⟨⟨np', nr'⟩, har', hbr⟩ := hbr
    rw [Proofs.Machine.labelsRev_getD 0 ((i, a) :: p.reverse) rfl] at hbr
    simp only [List.reverse_reverse] at hlev hbr
    rw [hlev] at hbr
    cases hloop : loop with
    | false =>
      left
      simp only [hLdef, hloop, Bool.false_eq_true, ↓reduceIte, List.length_cons,
        Nat.add_sub_cancel] at hbr
      obtain ⟨hlk, hgn1⟩ := gotoN_contRev_block (rp := p.reverse) (by simpa using hbr) hblk1
        (by simpa using hdep1) (by simpa using hls)
      simp only [List.reverse_reverse] at hlk hgn1
      have hw : WrapL L t [] (s', f', .flow (.brk 0 ws)) []
          (s', f', .flow (.normal (ws.take nr' ++ L.outer.reverse))) :=
        .ok (by simp [hLdef, hloop]) har' rfl
          (by simpa [liftInstrs] using @EvalLXPS.nil H s' f' (ws.take nr' ++ L.outer.reverse))
      have hone := wrap_one hk hsel harm har hrun₀ hw
      obtain ⟨sg', hsg'⟩ := Option.isSome_iff_exists.mp hlk
      obtain ⟨ω₂, hd₂, hω₂⟩ := blk_at_inf hν (hB' _ hsz) (W := ws.take nr' ++ L.outer.reverse)
        (s := s') (f := f') rfl (by rw [hgn1]; simp [hLdef]) hp.hc (seg_of_lookup' hp.hc hsg') hok
        hstay1
      obtain ⟨L₁, hL₁, hd₁⟩ := infL_cons hone rfl rfl hd₂
      refine ⟨L₁ ++ω ω₂, hd₁, ?_⟩
      rw [htl, Proofs.MachineLProd.toSS_append, ← hω₂, ← hL₁]; simp
    | true =>
      right
      refine ⟨rfl, ?_⟩
      rw [har₀] at har'; simp only [Option.some.injEq, Prod.mk.injEq] at har'
      obtain ⟨rfl, rfl⟩ := har'
      simp only [hLdef, hloop, ↓reduceIte, List.length_cons, Nat.sub_zero,
        List.reverse_reverse] at hbr
      obtain ⟨l, hl, hb'⟩ := evalLXPS_canonical hrun₀ (by simp)
      have hc0 := hsg₀
      have hg2 := gotoN_entry hcA hsg₀
        (⟨np, ((ws.take np ++ V'.drop np).drop np).reverse, true, tryT, cs, bt⟩ :: ls)
        ((ws.take np ++ V'.drop np).take np).reverse s' f'
      rw [List.length_append, List.length_singleton] at hg2
      refine ⟨ws, s', f', l, hb', ?_, har₀, ?_⟩
      · rw [← hl, show m + 1 - r = (m - r) + 1 by omega, segLog_add, segLog_one,
          show r + (m - r) = m by omega]
      · have := hbr
        simp only [List.length_reverse, zero_add, List.drop_one, List.tail_cons] at this
        rw [hg2] at this
        simpa using this.symm

/-- Two streams concatenating the same segments are equal. -/
theorem streamConcat_unique {α : Type _} {l : ℕ → List α} {ω₁ ω₂ : ℕ → α}
    (h₁ : StreamConcat l ω₁) (h₂ : StreamConcat l ω₂) : ω₁ = ω₂ := by
  funext i
  obtain ⟨n, hn⟩ := h₁.2 (i + 1)
  have hi : i < ((List.range n).flatMap l).length := by omega
  rw [h₁.1 n i hi, h₂.1 n i hi]

/-- **An arm entered at `r`, the run never leaving the enclosing sequence**: the claim at `r`, or,
for a loop, one native iteration branching back to the arm's entry at a later time. -/
theorem arm_step {body : Expr} {g : ℕ → MState H} {lg : ℕ → List (SCall H)}
    {ν : ℕ → SCall H} (hν : StreamConcat lg ν) {μ : Nat} (hB' : ∀ μ' < μ, PBC body g lg ν μ')
    {p : List SeqStep} {c : List Instr} {i : Nat} {sg sg₀ : Segment} {pre : List Instr}
    {t : Instr} {bt : BlockType} {loop tryT : Bool} {cs : List Catch} {a : Nat}
    {c' : List Instr} {V' : List Val} {np nr : Nat} {ls : List LFrame} {s : Store H} {f : Frame}
    {W : List Val} {r : ℕ}
    (hμ : sizeOf (t :: restAt c (i + 1)) = μ) (hp : Pos body p c i sg pre [t])
    (hk : StructKind t bt loop tryT cs) (hok : FramesOk body p.reverse ls)
    (hsel : ArmSel t W a V') (harm : armOf t a = some c') (har : arity f bt = some (np, nr))
    (hsg₀ : (segment c')[0]? = some sg₀)
    (hgr : g r = ⟨.block ⟨p ++ [(i, a)], 0⟩, (V'.take np).reverse,
      ⟨if loop then np else nr, (V'.drop np).reverse, loop, tryT, cs, bt⟩ :: ls, s, f⟩)
    (hstay : ∀ k, r ≤ k → StaysT body g lg p.length k) :
    (∃ ω, InfLXP s f W (liftInstr t :: liftInstrs (restAt c (i + 1))) ω ∧
      tail lg ν r = toSS ω) ∨
    (loop = true ∧ ∃ m, r ≤ m ∧
      ∃ (vs : List Val) (s' : Store H) (f' : Frame) (l : List (OCall H)),
      EvalLXPh s f (V'.take np) (liftInstrs c') l (s', f', .flow (.brk 0 vs)) ∧
      segLog lg r (m + 1 - r) = l.map OCall.toS ∧ arity f' bt = some (np, nr) ∧
      g (m + 1) = ⟨.block ⟨p ++ [(i, a)], 0⟩, ((vs.take np ++ V'.drop np).take np).reverse,
        ⟨np, ((vs.take np ++ V'.drop np).drop np).reverse, true, tryT, cs, bt⟩ :: ls, s', f'⟩) := by
  obtain ⟨ht, -, -⟩ := pos_term hp (isStruct_terminator ⟨_, _, _, _, hk⟩)
  have hcA : seqAt body (p ++ [(i, a)]) = some c' := by
    rw [Proofs.Machine.seqAt_append]; simp [hp.hc, hp.hsg, ht, harm]
  have hokA : FramesOk body ((i, a) :: p.reverse)
      (⟨if loop then np else nr, (V'.drop np).reverse, loop, tryT, cs, bt⟩ :: ls) := by
    simpa using MachineLBwd.arm_ok hp hk harm hok (if loop then np else nr) (V'.drop np).reverse
  by_cases hall : ∀ k, r ≤ k → StaysT body g lg (p.length + 1) k
  · left
    have hsz : sizeOf (restAt c' 0) < μ := by
      rw [restAt_zero, ← hμ]; have := sizeOf_armOf harm; simp; omega
    obtain ⟨ω, hd, hω⟩ := blk_at_inf hν (hB' _ hsz) rfl (p := p ++ [(i, a)]) (j := 0)
      (W := V'.take np) hgr hcA hsg₀ (by simpa using hokA) (fun k hk => by simpa using hall k hk)
    rw [restAt_zero] at hd
    exact ⟨ω, descendI hk hsel harm har hd, hω⟩
  · push Not at hall
    classical
    have hex : ∃ m, r ≤ m ∧ ¬ StaysT body g lg (p.length + 1) m := hall
    have hm₀ := Nat.find_spec hex
    have hin : ∀ k, r ≤ k → k < Nat.find hex → StaysT body g lg (p.length + 1) k :=
      fun k h1 h2 => by
        by_contra hc
        exact Nat.find_min hex h2 ⟨h1, hc⟩
    rcases first_leave hν hB' hμ hp hk hok hsel harm har hsg₀ hgr hstay hm₀.1 hin hm₀.2 with
      h | ⟨hl, h⟩
    · exact .inl h
    · exact .inr ⟨hl, _, hm₀.1, h⟩

/-- **The A step**: the A claim at `μ`, from the B claim below `μ`. A loop re-entered infinitely
often, the claim failing at each re-entry, would be `loopInf` with the run's stream. -/
theorem pa_step {body : Expr} {g : ℕ → MState H} {lg : ℕ → List (SCall H)} {ν : ℕ → SCall H}
    (hν : StreamConcat lg ν) {μ : Nat} (ihB : ∀ μ' < μ, PBC body g lg ν μ') :
    PAC body g lg ν μ := by
  intro n p c i sg pre t bt loop tryT cs a c' V' np nr ls s f W hμ hp hk hok hsel harm har hg hdn
    hstay
  obtain ⟨ht, -, -⟩ := pos_term hp (isStruct_terminator ⟨_, _, _, _, hk⟩)
  have hls : ls.length = p.length := by simpa using Proofs.Machine.framesOk_length _ _ hok
  have hcA : seqAt body (p ++ [(i, a)]) = some c' := by
    rw [Proofs.Machine.seqAt_append]; simp [hp.hc, hp.hsg, ht, harm]
  have hsz : sizeOf (restAt c (i + 1)) < μ := by rw [← hμ]; exact sizeOf_cons_lt t _
  cases hseg : (segment c')[0]? with
  | none =>
    have hc0 : c' = [] := by rw [← restAt_zero c', restAt_end hseg]
    subst hc0
    set L : LFrame := ⟨if loop then np else nr, (V'.drop np).reverse, loop, tryT, cs, bt⟩
      with hLdef
    have hnone : ¬ (lookup body ⟨p ++ [(i, a)], 0⟩).isSome := by rw [lookup_eq, hcA]; simp [hseg]
    unfold entry at hg
    simp only [hnone, Bool.false_eq_true, ↓reduceIte] at hg
    rw [cont, List.reverse_append, List.reverse_singleton, List.singleton_append,
      show p.length + 1 = p.reverse.length + 1 by simp] at hg
    obtain ⟨np', nr', har', hg'⟩ := gotoN_cons (Proofs.Machine.depth_contRev_cons body i a _) hg
    obtain ⟨hlk, hgn⟩ := gotoN_contRev_block hg' (staysT_block (hstay n le_rfl))
      (by simpa using hdn) (by simpa using hls)
    simp only [List.reverse_reverse] at hlk hgn
    have hw : WrapL L t [] (s, f, .flow (.normal (V'.take np))) []
        (s, f, .flow (.normal (L.outer ++ topVals nr' (V'.take np).reverse).reverse)) := by
      simpa using wrap_fall (W := (V'.take np).reverse) (t := t) (rest := []) har'
        (by simpa [liftInstrs] using
          @EvalLXPS.nil H s f (L.outer ++ topVals nr' (V'.take np).reverse).reverse)
    have hone := wrap_one hk hsel harm har (by simpa [liftInstrs] using EvalLXPS.nil) hw
    obtain ⟨sg', hsg'⟩ := Option.isSome_iff_exists.mp hlk
    obtain ⟨ω₂, hd₂, hω₂⟩ := blk_at_inf hν (ihB _ hsz) rfl (by rw [hgn, List.reverse_reverse])
      hp.hc (seg_of_lookup' hp.hc hsg') hok hstay
    obtain ⟨L₁, hL₁, hd₁⟩ := infL_cons hone rfl rfl hd₂
    have : L₁ = [] := by simpa using hL₁.symm
    subst this
    exact ⟨ω₂, by simpa [streamAppend_nil] using hd₁, by simpa [streamAppend_nil] using hω₂⟩
  | some sg₀ =>
    have hg0 := gotoN_entry hcA hseg
      (⟨if loop then np else nr, (V'.drop np).reverse, loop, tryT, cs, bt⟩ :: ls)
      (V'.take np).reverse s f
    rw [List.length_append, List.length_singleton] at hg0
    rw [hg0] at hg; simp only [Option.some.injEq] at hg
    rcases arm_step hν ihB hμ hp hk hok hsel harm har hseg hg.symm hstay with h | ⟨hl, -⟩
    · exact h
    subst hl
    cases hk with
    | loop =>
    rename_i b₀
    cases hsel
    simp only [armOf, Option.some.injEq] at harm; subst harm
    by_contra hQ0
    let Ent : ℕ × (Store H × Frame × List Val) → Prop := fun x =>
      n ≤ x.1 ∧ arity x.2.2.1 bt = some (np, nr) ∧
      g x.1 = ⟨.block ⟨p ++ [(i, 0)], 0⟩, (x.2.2.2.take np).reverse,
        ⟨np, (x.2.2.2.drop np).reverse, true, false, [], bt⟩ :: ls, x.2.1, x.2.2.1⟩
    let Q : ℕ × (Store H × Frame × List Val) → Prop := fun x =>
      ∃ ω, InfLXP x.2.1 x.2.2.1 x.2.2.2 (liftInstr (.loop bt b₀) :: liftInstrs (restAt c (i + 1)))
        ω ∧ tail lg ν x.1 = toSS ω
    have hstep : ∀ x : {x // Ent x ∧ ¬ Q x}, ∃ y : {x // Ent x ∧ ¬ Q x},
        ∃ (l : List (OCall H)) (vs : List Val), x.1.1 < y.1.1 ∧
        EvalLXPh x.1.2.1 x.1.2.2.1 (x.1.2.2.2.take np) (liftInstrs b₀) l
          (y.1.2.1, y.1.2.2.1, .flow (.brk 0 vs)) ∧
        y.1.2.2.2 = vs.take np ++ x.1.2.2.2.drop np ∧
        segLog lg x.1.1 (y.1.1 - x.1.1) = l.map OCall.toS := by
      rintro ⟨⟨r, s₀, f₀, W₀⟩, ⟨hnr, har₀, hgr⟩, hnQ⟩
      rcases arm_step hν ihB hμ hp StructKind.loop hok (ArmSel.plain (fun _ _ _ h => nomatch h))
        (by simp [armOf]) har₀ hseg (by simpa using hgr) (fun k hk => hstay k (by omega)) with
        h | ⟨-, m, hrm, vs, s', f', l, hev, hsl, har', hgm⟩
      · exact absurd h hnQ
      · have hnQ' : ¬ Q (m + 1, s', f', vs.take np ++ W₀.drop np) := by
          rintro ⟨ω', hd', hω'⟩
          apply hnQ
          refine ⟨l ++ω ω', ?_, ?_⟩
          · exact InfLXP.loopBack har₀ hev hd'
          · show tail lg ν r = _
            rw [tail_seg hν r (m + 1 - r), hsl, show r + (m + 1 - r) = m + 1 by omega,
              Proofs.MachineLProd.toSS_append]
            exact congrArg _ hω'
        refine ⟨⟨(m + 1, s', f', vs.take np ++ W₀.drop np), ⟨by omega, har', ?_⟩, hnQ'⟩, l, vs,
          by show r < m + 1; omega, hev, rfl, hsl⟩
        simpa using hgm
    choose F l vs hlt hev hst hsl using hstep
    let x0 : {x // Ent x ∧ ¬ Q x} := ⟨(n, s, f, V'), ⟨le_rfl, har, by simpa using hg.symm⟩, hQ0⟩
    let X : ℕ → {x // Ent x ∧ ¬ Q x} := fun k => F^[k] x0
    have hX : ∀ k, X (k + 1) = F (X k) := fun k => Function.iterate_succ_apply' F k x0
    let rr : ℕ → ℕ := fun k => (X k).1.1
    let cs' : ℕ → List (SCall H) := fun k => (l (X k)).map OCall.toS
    have hrr : ∀ k, rr k < rr (k + 1) := fun k => by
      show (X k).1.1 < (X (k + 1)).1.1; rw [hX]; exact hlt _
    have hrr0 : ∀ k, rr 0 + k ≤ rr k := by
      intro k; induction k with
      | zero => exact le_rfl
      | succ k ih => have := hrr k; omega
    have hcs : ∀ k, segLog lg (rr k) (rr (k + 1) - rr k) = cs' k := fun k => by
      show segLog lg (X k).1.1 ((X (k + 1)).1.1 - (X k).1.1) = _
      rw [hX]; exact hsl _
    have hchain : ∀ k, (List.range k).flatMap cs' = segLog lg (rr 0) (rr k - rr 0) := by
      intro k; induction k with
      | zero => simp [segLog]
      | succ k ih =>
        have h1 := hrr k; have h2 := hrr0 k
        rw [List.range_succ, List.flatMap_append, ih, List.flatMap_singleton, ← hcs k,
          show rr (k + 1) - rr 0 = (rr k - rr 0) + (rr (k + 1) - rr k) by omega, segLog_add,
          show rr 0 + (rr k - rr 0) = rr k by omega]
    have hu : ∀ N, ∃ k, N ≤ ((List.range k).flatMap cs').length := by
      intro N
      obtain ⟨M, hM⟩ := hν.2 (N + (segLog lg 0 (rr 0)).length)
      refine ⟨M, ?_⟩
      rw [flatMap_range] at hM
      rw [hchain]
      have h1 := segLog_length_mono (lg := lg) (a := M) (b := rr 0 + (rr M - rr 0))
        (by have := hrr0 M; omega)
      have h3 := segLog_add lg 0 (rr 0) (rr M - rr 0)
      rw [zero_add] at h3
      rw [h3, List.length_append] at h1
      omega
    have hlen : ∀ k, ((List.range k).flatMap cs').length = ((List.range k).flatMap
        (fun k => l (X k))).length := by
      intro k; simp [cs', List.length_flatMap]
    obtain ⟨ω, hω⟩ := exists_streamConcat (fun k => l (X k))
      (fun N => by obtain ⟨k, hk⟩ := hu N; exact ⟨k, by rw [← hlen]; exact hk⟩)
    have h1 : StreamConcat cs' (toSS ω) := streamConcat_map OCall.toS hω
    have h2 : StreamConcat cs' (tail lg ν (rr 0)) := by
      refine streamConcat_of_chain (w := fun k => tail lg ν (rr k)) (fun k => ?_) hu
      rw [tail_seg hν (rr k) (rr (k + 1) - rr k), hcs k,
        show rr k + (rr (k + 1) - rr k) = rr (k + 1) by have := hrr k; omega]
    apply hQ0
    refine ⟨ω, ?_, streamConcat_unique h2 h1⟩
    refine InfLXP.loopInf (fun k => (X k).1.2) (fun k => l (X k)) (by rfl)
      (fun k => (X k).2.1.2.1) (fun k => ⟨vs (X k), ?_, ?_⟩) hω
    · show EvalLXPh _ _ _ _ _ ((X (k + 1)).1.2.1, (X (k + 1)).1.2.2.1, _)
      rw [hX]; exact hev _
    · show (X (k + 1)).1.2.2.2 = _
      rw [hX]; exact hst _


/-- **Both claims at every size**, by strong induction on the size of the remaining code. -/
theorem claims {body : Expr} {g : ℕ → MState H} {lg : ℕ → List (SCall H)} {ν : ℕ → SCall H}
    (hν : StreamConcat lg ν) (μ : ℕ) : PBC body g lg ν μ ∧ PAC body g lg ν μ := by
  induction μ using Nat.strong_induction_on with
  | _ μ ih =>
    have ihB : ∀ μ' < μ, PBC body g lg ν μ' := fun μ' h => (ih μ' h).1
    have hA := pa_step hν ihB
    exact ⟨pb_step hν hA ihB, hA⟩

/-- **A productive run of the machine from the CFG entry is a productive run of the body** with the
same stream of answered calls. -/
theorem machine_infL {body : Expr} {s : Store H} {f : Frame} {ν : ℕ → SCall H}
    (h : ProdL body (initial body s f) ν) :
    ∃ ω, InfLXP s f [] (liftInstrs body) ω ∧ ν = toSS ω := by
  obtain ⟨g, lg, h0, hg, hν⟩ := h
  have hblk : ∀ m, ∃ b, (g m).node = .block b := fun m => MachineLDivI.mstepL_block (hg m)
  have hstay0 : ∀ k, 0 ≤ k → StaysT body g lg ([] : List SeqStep).length k := fun k _ =>
    ⟨Nat.zero_le _, MachineLDivI.mstepS_zero (hg k) (hblk (k + 1))⟩
  have hie := initial_eq body s f
  rw [← h0] at hie
  obtain ⟨hlk, hgn⟩ := gotoN_entry_block hie (hblk 0) (Nat.zero_le _) rfl
  obtain ⟨sg₀, hsg₀⟩ := Option.isSome_iff_exists.mp hlk
  obtain ⟨ω, hd, hω⟩ := blk_at_inf hν (claims hν _).1 rfl (p := []) (j := 0) (c := body)
    (W := []) (ls := []) (by simpa using hgn) rfl (seg_of_lookup' rfl hsg₀) (by simp [FramesOk])
    hstay0
  exact ⟨ω, by simpa [restAt_zero] using hd, by simpa [tail_zero] using hω⟩

end Silmaril.Wasm.Cfg.Proofs.MachineLProdB
