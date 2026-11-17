module

public import Silmaril.Proofs.Wasm.Cfg.MachineLLogDivB

@[expose] public section

/-!
# A logged run to a diverging position is divergence after its log (H2, proofs)

A finite run `G 0 → ⋯ → G N` of the logged machine (`lg k` the log of step `k`), ending at a
**point** (`PointT`): a block whose sequence's rest diverges natively, or the entry of a loop's arm
whose loop diverges natively. Then the code of the run's start diverges after the run's log
(`LogDivXP`, the log read back by `OCall.toS`).

By strong induction on the time left, over positions as `MachineLDivI` (`ptAB`): a block of a
sequence the run does not leave before `N` (the B clause), or the entry of an arm (the A clause).
Each finished instruction is a `…K` constructor (`MachineLLogDivB.logDiv_cons`); an arm the run
never leaves before `N` is a descent (`block`, `loop`, `handler`, `arm`); an arm left at a first
step is a native run of the arm (`MachineLRel.arm_fwd`), continuing the sequence or re-entering
its loop (`loopBack`).
-/

namespace Silmaril.Wasm.Cfg.Proofs.MachineLLogDivP

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Abstract (EvalLXPS EvalLXPh SCall OCall LogDivXP evalLXPS_canonical)
open Silmaril.Wasm.Abstract.CallXP (POut EvalOXP)
open Silmaril.Wasm.Abstract.XDivergeP (EvalDivXP FunDivXP)
open Silmaril.Wasm.Cfg.Proofs.Machine (restAt_cons restAt_end restAt_zero seg_of_lookup lookup_eq)
open Silmaril.Wasm.Cfg.Proofs.MachineLFwd
open Silmaril.Wasm.Cfg.Proofs.MachineLBwd (Pos pos_next pos_term isStruct_terminator lift_op
  lift_block lift_loop lift_if lift_try nil_inv nil_inv_normal seg_wf armOf_if armOf_if'
  liftInstrs_ite)
open Silmaril.Wasm.Cfg.Proofs.MachineLRel (MStepS DispS MRunS ExitB arm_fwd run_props)
open Silmaril.Wasm.Cfg.Proofs.MachineLDivI (gotoN_lbls gotoN_contRev_block gotoN_entry_block
  dispS_own wrap_one pos_start lift_rest seg_of_lookup' mrunS_snoc)
open Silmaril.Wasm.Cfg.Proofs.MachineLLogDivB (logDiv_cons canon)

variable {H : Type}

/-! ## Logs of an indexed run -/

/-- The logs of the `k` steps from time `a`. -/
def segLog (lg : ℕ → List (SCall H)) (a : ℕ) : ℕ → List (SCall H)
  | 0 => []
  | k + 1 => lg a ++ segLog lg (a + 1) k

theorem segLog_add (lg : ℕ → List (SCall H)) :
    ∀ (a j k : ℕ), segLog lg a (j + k) = segLog lg a j ++ segLog lg (a + j) k
  | a, 0, k => by simp [segLog]
  | a, j + 1, k => by
    rw [show j + 1 + k = (j + k) + 1 by omega]
    simp only [segLog]
    rw [segLog_add lg (a + 1) j k, show a + 1 + j = a + (j + 1) by omega, List.append_assoc]

theorem segLog_one (lg : ℕ → List (SCall H)) (a : ℕ) : segLog lg a 1 = lg a := by simp [segLog]

/-! ## The run and its point -/

section Run

variable (body : Expr) (G : ℕ → MState H) (lg : ℕ → List (SCall H)) (N : ℕ)

/-- Step `m` of the run stays at depth `δ`, from a state at least that deep. -/
def StaysT (δ m : ℕ) : Prop := δ ≤ (G m).lbls.length ∧ MStepS body δ (G m) (lg m) (G (m + 1))

/-- **The point** at time `N`: a block whose sequence's rest diverges natively, or the entry of a
loop's arm (as entering or re-entering it on `V` leaves it) whose loop diverges natively. -/
def PointT : Prop :=
  (∃ (p : List SeqStep) (c : List Instr) (i : Nat) (stk : List Val) (ls : List LFrame)
    (s : Store H) (f : Frame), G N = ⟨.block ⟨p, i⟩, stk, ls, s, f⟩ ∧ seqAt body p = some c ∧
      EvalDivXP s f stk.reverse (liftInstrs (restAt c i))) ∨
  (∃ (p : List SeqStep) (c : List Instr) (i : Nat) (sg : Segment) (bt : BlockType)
    (b₀ : List Instr) (ls : List LFrame) (np nr : Nat) (V : List Val) (s : Store H) (f : Frame),
    Pos body p c i sg sg.body [.loop bt b₀] ∧ arity f bt = some (np, nr) ∧
      G N = ⟨.block ⟨p ++ [(i, 0)], 0⟩, (V.take np).reverse,
        ⟨np, (V.drop np).reverse, true, false, [], bt⟩ :: ls, s, f⟩ ∧
      EvalDivXP s f V (liftInstr (.loop bt b₀) :: liftInstrs (restAt c (i + 1))))

/-- **What step `n` does from `(s, f, W)`**, the code `post` of its block left, with the log `l'`
of that part. -/
def ResT (n : Nat) (p : List SeqStep) (i : Nat) (sg : Segment) (post : List Instr)
    (ls : List LFrame) (s : Store H) (f : Frame) (W : List Val) (l' : List (SCall H)) : Prop :=
  (∃ r', EvalLXPS s f W (liftInstrs post) l' r' ∧ (∀ t, sg.term = some t → ¬ Instr.IsStruct t) ∧
    DispS body p.length ⟨p, i⟩ ls r' (G (n + 1))) ∨
  (∃ (X : List Instr) (t : Instr) (s₁ : Store H) (f₁ : Frame) (V : List Val) (a : Nat)
    (c' : List Instr) (V' : List Val) (np nr : Nat) (bt : BlockType) (loop tryT : Bool)
    (cs : List Catch),
    post = X ++ [t] ∧ sg.term = some t ∧ StructKind t bt loop tryT cs ∧
      EvalLXPS s f W (liftInstrs X) l' (s₁, f₁, .flow (.normal V)) ∧
      ArmSel t V a V' ∧ armOf t a = some c' ∧ arity f₁ bt = some (np, nr) ∧
      gotoN (entry body (p ++ [(i, a)]) 0) (p.length + 1)
        (⟨if loop then np else nr, (V'.drop np).reverse, loop, tryT, cs, bt⟩ :: ls)
        (V'.take np).reverse s₁ f₁ = some (G (n + 1)) ∧ p.length ≤ (G (n + 1)).lbls.length)

/-- **The B clause at time `n`**: from a block of a sequence the run does not leave before `N`,
the rest of the sequence diverges after the step's remaining log then the later steps' logs. -/
def BClause (n : Nat) : Prop :=
  ∀ (post : List Instr) (p : List SeqStep) (c : List Instr) (i : Nat) (sg : Segment)
    (pre : List Instr) (ls : List LFrame) (s : Store H) (f : Frame) (W : List Val)
    (l' : List (SCall H)), Pos body p c i sg pre post → FramesOk body p.reverse ls →
    (∀ m, n < m → m < N → StaysT body G lg p.length m) → ResT body G n p i sg post ls s f W l' →
    ∃ L, l' ++ segLog lg (n + 1) (N - (n + 1)) = L.map OCall.toS ∧
      LogDivXP s f W (liftInstrs post ++ liftInstrs (restAt c (i + 1))) L

/-- **The A clause at time `n`**: at the entry of an arm of a structured instruction entered from
`(s, f, W)`, in a sequence the run does not leave before `N`, the instruction and the rest of the
sequence diverge after the later steps' logs. -/
def AClause (n : Nat) : Prop :=
  ∀ (p : List SeqStep) (c : List Instr) (i : Nat) (sg : Segment) (pre : List Instr) (t : Instr)
    (bt : BlockType) (loop tryT : Bool) (cs : List Catch) (a : Nat) (c' : List Instr)
    (V' : List Val) (np nr : Nat) (ls : List LFrame) (s : Store H) (f : Frame) (W : List Val),
    Pos body p c i sg pre [t] → StructKind t bt loop tryT cs → FramesOk body p.reverse ls →
    ArmSel t W a V' → armOf t a = some c' → arity f bt = some (np, nr) →
    gotoN (entry body (p ++ [(i, a)]) 0) (p.length + 1)
      (⟨if loop then np else nr, (V'.drop np).reverse, loop, tryT, cs, bt⟩ :: ls)
      (V'.take np).reverse s f = some (G n) →
    p.length ≤ (G n).lbls.length → (∀ m, n ≤ m → m < N → StaysT body G lg p.length m) →
    ∃ L, segLog lg n (N - n) = L.map OCall.toS ∧
      LogDivXP s f W (liftInstr t :: liftInstrs (restAt c (i + 1))) L

end Run

theorem point_block {body : Expr} {G : ℕ → MState H} {N : ℕ} (h : PointT body G N) :
    ∃ b, (G N).node = .block b := by
  rcases h with ⟨p, c, i, stk, ls, s, f, hG, -⟩ | ⟨p, c, i, sg, bt, b₀, ls, np, nr, V, s, f, -, -, hG, -⟩
  · exact ⟨_, by rw [hG]⟩
  · exact ⟨_, by rw [hG]⟩

theorem resT_of {body : Expr} {G : ℕ → MState H} {lg : ℕ → List (SCall H)} {n : Nat}
    {p : List SeqStep} {j : Nat} {sg : Segment} {stk : List Val} {ls : List LFrame} {s : Store H}
    {f : Frame} (hgn : G n = ⟨.block ⟨p, j⟩, stk, ls, s, f⟩) (hls : ls.length = p.length)
    (hlk : lookup body ⟨p, j⟩ = some sg) (hS : StaysT body G lg p.length n) :
    ResT body G n p j sg sg.instrs ls s f stk.reverse (lg n) := by
  obtain ⟨-, hS⟩ := hS
  rw [hgn] at hS
  cases hS with
  | run hb ht hr hd =>
    rw [hlk] at hb; cases hb
    exact .inl ⟨_, by simpa [codeOf_eq] using hr, ht, hd⟩
  | abort hb hr hn hd =>
    rw [← hls] at hd
    exact absurd (dispS_own hd) hn
  | @enter _ _ _ V V' _ _ s₁ _ f₁ i a c bt np nr loop tryT cs _ _ hb ht harm hkind hr hsel har hg _ =>
    rw [hlk] at hb; cases hb
    exact .inr ⟨sg.body, i, s₁, f₁, V, a, c, V', np, nr, bt, loop, tryT, cs,
      by simp [Segment.instrs, ht], ht, hkind, hr, hsel, harm, har, hg, by assumption⟩

theorem mrunS_of {body : Expr} {G : ℕ → MState H} {lg : ℕ → List (SCall H)} {δ a : ℕ} :
    ∀ k, (∀ m, a ≤ m → m < a + k → MStepS body δ (G m) (lg m) (G (m + 1))) →
      MRunS body δ (G a) (segLog lg a k) (G (a + k))
  | 0, _ => by simpa [segLog] using MRunS.refl (body := body) (δ := δ) (G a)
  | k + 1, h => by
    have := mrunS_snoc (mrunS_of k (fun m h1 h2 => h m h1 (by omega))) (h (a + k) (by omega) (by omega))
    rw [show segLog lg a (k + 1) = segLog lg a k ++ lg (a + k) by
      rw [segLog_add lg a k 1, segLog_one], show a + (k + 1) = a + k + 1 by omega]
    exact this

/-- **A block start at time `m`**: the point itself at `N`, else the B clause at `m`. -/
theorem blk_at {body : Expr} {G : ℕ → MState H} {lg : ℕ → List (SCall H)} {N m : ℕ}
    (hpt : PointT body G N) (hm : m ≤ N) (hBm : m < N → BClause body G lg N m)
    {p : List SeqStep} {c : List Instr} {j : Nat} {sg : Segment} {W : List Val}
    {ls : List LFrame} {s : Store H} {f : Frame}
    (hgm : G m = ⟨.block ⟨p, j⟩, W.reverse, ls, s, f⟩) (hc : seqAt body p = some c)
    (hsg : (segment c)[j]? = some sg) (hok : FramesOk body p.reverse ls)
    (hna : m < N ∨ p = [] ∨ j ≠ 0) (hstay : ∀ k, m ≤ k → k < N → StaysT body G lg p.length k) :
    ∃ L, segLog lg m (N - m) = L.map OCall.toS ∧ LogDivXP s f W (liftInstrs (restAt c j)) L := by
  have hls : ls.length = p.length := by simpa using Proofs.Machine.framesOk_length _ _ hok
  rcases Nat.lt_or_ge m N with hlt | hge
  · have hlk : lookup body ⟨p, j⟩ = some sg := by rw [lookup_eq]; simp [hc, hsg]
    have hres := resT_of hgm hls hlk (hstay m le_rfl hlt)
    rw [List.reverse_reverse] at hres
    obtain ⟨L, hL, hd⟩ := hBm hlt sg.instrs p c j sg [] ls s f W (lg m) (pos_start hc hsg) hok
      (fun k hk hk' => hstay k (by omega) hk') hres
    refine ⟨L, ?_, by rwa [lift_rest hsg]⟩
    rw [← hL, show N - m = 1 + (N - (m + 1)) by omega, segLog_add, segLog_one]
  · have hmN : m = N := by omega
    subst hmN
    rcases hpt with ⟨p₁, c₁, i₁, stk₁, ls₁, s₁, f₁, hG, hc₁, hd⟩ |
      ⟨p₁, c₁, i₁, sg₁, bt₁, b₁, ls₁, np₁, nr₁, V₁, s₁, f₁, -, -, hG, -⟩
    · rw [hgm] at hG
      simp only [MState.mk.injEq, Target.block.injEq, BlockId.mk.injEq] at hG
      obtain ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl⟩ := hG
      rw [hc] at hc₁; cases hc₁
      exact ⟨[], by simp [segLog], .div (by simpa using hd)⟩
    · rw [hgm] at hG
      simp only [MState.mk.injEq, Target.block.injEq, BlockId.mk.injEq] at hG
      obtain ⟨⟨rfl, rfl⟩, -⟩ := hG
      rcases hna with h | h | h
      · omega
      · simp at h
      · exact absurd rfl h

open Silmaril.Wasm.Cfg.Proofs.MachineLLogDivB (nil_normal)
open Silmaril.Wasm.Cfg.Proofs.MachineLDivB (gotoN_entry)

theorem blk_succ {body : Expr} {G : ℕ → MState H} {lg : ℕ → List (SCall H)} {N m : ℕ}
    (hpt : PointT body G N) (hm : m ≤ N) (hstay : ∀ k, m ≤ k → k < N → ∃ δ, StaysT body G lg δ k) :
    ∃ b, (G m).node = .block b := by
  rcases Nat.lt_or_ge m N with h | h
  · obtain ⟨δ, -, hS⟩ := hstay m le_rfl h
    obtain ⟨b, _, _, _, _, hb⟩ := hS.block
    exact ⟨b, by rw [hb]⟩
  · have : m = N := by omega
    subst this; exact point_block hpt

/-- **The B clause at `n`, from the clauses later.** -/
theorem b_step {body : Expr} {G : ℕ → MState H} {lg : ℕ → List (SCall H)} {N n : ℕ}
    (hpt : PointT body G N) (hn : n < N) (hA1 : AClause body G lg N (n + 1))
    (hB1 : n + 1 < N → BClause body G lg N (n + 1)) : BClause body G lg N n := by
  intro post
  induction post with
  | nil => intro p c i sg pre ls s f W l' hp; exact absurd rfl hp.hpost
  | cons e post' ihp =>
    intro p c i sg pre ls s f W l' hp hok hstay hres
    have hls : ls.length = p.length := by simpa using Proofs.Machine.framesOk_length _ _ hok
    simp only [liftInstrs, List.cons_append]
    rcases hres with ⟨r', hr', ht, hd⟩ |
      ⟨X, t, s₁, f₁, V, a, c', V', np, nr, bt, loop, tryT, cs, hpost, hterm, hk, hX, hsel, harm,
        har, hg, hdep⟩
    · obtain ⟨s', f', o⟩ := r'
      have hse : ¬ Instr.IsStruct e := fun h => ht e (pos_term hp (isStruct_terminator h)).1 h
      have hsp := MachineLSeq.split [liftInstr e] (liftInstrs post') (by simpa [liftInstrs] using hr')
      rcases hsp with ⟨s₂, f₂, N₂, l₁, l₂, h₁, h₂, rfl⟩ | ⟨-, hn'⟩
      · cases post' with
        | cons e' post'' =>
          obtain ⟨L₂, hL₂, hd₂⟩ := ihp p c i sg (pre ++ [e]) ls s₂ f₂ N₂ l₂ (pos_next hp hse) hok
            hstay (.inl ⟨_, h₂, ht, hd⟩)
          obtain ⟨L₁, rfl, hd₁⟩ := logDiv_cons h₁ rfl rfl hd₂
          exact ⟨L₁ ++ L₂, by simp [← hL₂], hd₁⟩
        | nil =>
          obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_inv (by simpa [liftInstrs] using h₂)
          cases hd with
          | next hg hδ =>
            have hblk := blk_succ hpt (m := n + 1) (by omega)
              (fun k hk hk' => ⟨_, hstay k (by omega) hk'⟩)
            obtain ⟨hlk, hgn⟩ := gotoN_entry_block hg hblk hδ hls
            obtain ⟨sg', hsg'⟩ := Option.isSome_iff_exists.mp hlk
            have hsgc := seg_of_lookup' hp.hc hsg'
            obtain ⟨L₂, hL₂, hd₂⟩ := blk_at hpt (m := n + 1) (by omega) hB1 hgn hp.hc hsgc hok
              (.inr (.inr (by omega))) (fun k hk hk' => hstay k (by omega) hk')
            obtain ⟨L₁, rfl, hd₁⟩ := logDiv_cons h₁ rfl rfl hd₂
            exact ⟨L₁ ++ L₂, by simp [← hL₂], by simpa [liftInstrs] using hd₁⟩
      · rw [← hls] at hd; exact absurd (dispS_own hd) hn'
    · cases X with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at hpost
        obtain ⟨rfl, rfl⟩ := hpost
        obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_normal (by simpa [liftInstrs] using hX)
        obtain ⟨L, hL, hd⟩ := hA1 p c i sg pre e bt loop tryT cs a c' V' np nr ls s f W hp hk hok
          hsel harm har hg hdep (fun m hm hm' => hstay m (by omega) hm')
        exact ⟨L, by simpa using hL, by simpa [liftInstrs] using hd⟩
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
          obtain ⟨L₂, hL₂, hd₂⟩ := ihp p c i sg (pre ++ [e]) ls s₂ f₂ N₂ l₂
            (by rw [heq]; exact pos_next hp' hse) hok hstay (.inr ⟨X', t, s₁, f₁, V, a, c', V', np, nr, bt, loop, tryT, cs, rfl, hterm, hk, h₂,
              hsel, harm, har, hg, hdep⟩)
          obtain ⟨L₁, rfl, hd₁⟩ := logDiv_cons h₁ rfl rfl hd₂
          exact ⟨L₁ ++ L₂, by simp [← hL₂], hd₁⟩
        · exact absurd trivial hn'

/-- A logged run of a structured instruction's native arm, carried by the descent constructor. -/
theorem descend {s : Store H} {f : Frame} {W V' : List Val} {t : Instr} {bt : BlockType}
    {loop tryT : Bool} {cs : List Catch} {a : Nat} {c' : List Instr} {np nr : Nat}
    {rest : List BExpr} {L : List (OCall H)} (hk : StructKind t bt loop tryT cs)
    (hsel : ArmSel t W a V') (harm : armOf t a = some c') (har : arity f bt = some (np, nr))
    (hd : LogDivXP s f (V'.take np) (liftInstrs c') L) :
    LogDivXP s f W (liftInstr t :: rest) L := by
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
      simpa [liftInstr] using LogDivXP.arm .nil hb har hd
    | plain hi => exact absurd rfl (hi _ _ _)

/-- **The A clause at `n`, from the B clause at `n` and the clauses later.** -/
theorem a_step {body : Expr} {G : ℕ → MState H} {lg : ℕ → List (SCall H)} {N n : ℕ}
    (hG : ∀ k, k < N → MStepL body (G k) (lg k) (G (k + 1)))
    (hpt : PointT body G N) (hnN : n ≤ N) (hBn : n < N → BClause body G lg N n)
    (hA' : ∀ m, n < m → m ≤ N → AClause body G lg N m)
    (hB' : ∀ m, n < m → m < N → BClause body G lg N m) : AClause body G lg N n := by
  intro p c i sg pre t bt loop tryT cs a c' V' np nr ls s f W hp hk hok hsel harm har hg hdn hstay
  obtain ⟨ht, -, rfl⟩ := pos_term hp (isStruct_terminator ⟨_, _, _, _, hk⟩)
  have hls : ls.length = p.length := by simpa using Proofs.Machine.framesOk_length _ _ hok
  have hcA : seqAt body (p ++ [(i, a)]) = some c' := by
    rw [Proofs.Machine.seqAt_append]; simp [hp.hc, hp.hsg, ht, harm]
  set L : LFrame := ⟨if loop then np else nr, (V'.drop np).reverse, loop, tryT, cs, bt⟩ with hLdef
  have hokA : FramesOk body ((i, a) :: p.reverse) (L :: ls) := by
    simpa using MachineLBwd.arm_ok hp hk harm hok (if loop then np else nr) (V'.drop np).reverse
  have hblkn := blk_succ hpt hnN (fun k hk hk' => ⟨_, hstay k hk hk'⟩)
  cases hseg : (segment c')[0]? with
  | none =>
    have hc0 : c' = [] := by rw [← restAt_zero c', restAt_end hseg]
    subst hc0
    have hnone : ¬ (lookup body ⟨p ++ [(i, a)], 0⟩).isSome := by rw [lookup_eq, hcA]; simp [hseg]
    unfold entry at hg
    simp only [hnone, Bool.false_eq_true, ↓reduceIte] at hg
    rw [cont, List.reverse_append, List.reverse_singleton, List.singleton_append,
      show p.length + 1 = p.reverse.length + 1 by simp] at hg
    obtain ⟨np', nr', har', hg'⟩ := gotoN_cons (Proofs.Machine.depth_contRev_cons body i a _) hg
    obtain ⟨hlk, hgn⟩ := gotoN_contRev_block hg' hblkn (by simpa using hdn) (by simpa using hls)
    simp only [List.reverse_reverse] at hlk hgn
    have hw : WrapL L t [] (s, f, .flow (.normal (V'.take np))) []
        (s, f, .flow (.normal (L.outer ++ topVals nr' (V'.take np).reverse).reverse)) := by
      simpa using wrap_fall (W := (V'.take np).reverse) (t := t) (rest := []) har'
        (by simpa [liftInstrs] using
          @EvalLXPS.nil H s f (L.outer ++ topVals nr' (V'.take np).reverse).reverse)
    have hone := wrap_one hk hsel harm har (by simpa [liftInstrs] using EvalLXPS.nil) hw
    obtain ⟨sg', hsg'⟩ := Option.isSome_iff_exists.mp hlk
    obtain ⟨L₂, hL₂, hd₂⟩ := blk_at hpt hnN hBn (by rw [hgn, List.reverse_reverse]) hp.hc
      (seg_of_lookup' hp.hc hsg') hok (.inr (.inr (by omega))) hstay
    obtain ⟨L₁, hL₁, hd₁⟩ := logDiv_cons hone rfl rfl hd₂
    have : L₁ = [] := by simpa using hL₁.symm
    subst this
    exact ⟨L₂, hL₂, by simpa using hd₁⟩
  | some sg₀ =>
    have hsg₀ := hseg
    have hg0 := gotoN_entry hcA hsg₀ (L :: ls) (V'.take np).reverse s f
    rw [List.length_append, List.length_singleton] at hg0
    rw [hg0] at hg; simp only [Option.some.injEq] at hg
    rcases Nat.lt_or_ge n N with hlt | hge
    · by_cases hall : ∀ m, n ≤ m → m < N → StaysT body G lg (p.length + 1) m
      · obtain ⟨L₁, hL₁, hd₁⟩ := blk_at hpt hnN hBn (p := p ++ [(i, a)]) (j := 0)
          (W := V'.take np) hg.symm hcA hsg₀ (by simpa using hokA) (.inl hlt)
          (fun k hk hk' => by simpa using hall k hk hk')
        rw [restAt_zero] at hd₁
        exact ⟨L₁, hL₁, descend hk hsel harm har hd₁⟩
      · push Not at hall
        classical
        have hex : ∃ m, n ≤ m ∧ m < N ∧ ¬ StaysT body G lg (p.length + 1) m := hall
        have hm₀ := Nat.find_spec hex
        set m₀ := Nat.find hex with hm₀def
        have hbefore : ∀ m, n ≤ m → m < m₀ → StaysT body G lg (p.length + 1) m := fun m h1 h2 => by
          by_contra hc
          exact Nat.find_min hex h2 ⟨h1, by have := hm₀.2.1; omega, hc⟩
        have hrun₁ := mrunS_of (body := body) (G := G) (lg := lg) (δ := p.length + 1) (a := n)
          (m₀ - n) (fun m h1 h2 => (hbefore m h1 (by omega)).2)
        rw [show n + (m₀ - n) = m₀ by omega] at hrun₁
        obtain ⟨-, hD⟩ := hstay m₀ hm₀.1 hm₀.2.1
        have hok₀ : MInv body (G n) := by
          rw [← hg]; show FramesOk body (p ++ [(i, a)]).reverse (L :: ls); simpa using hokA
        have hd₀ : p.length + 1 ≤ (G n).lbls.length := by rw [← hg]; simp [hls]
        obtain ⟨-, hdm⟩ := run_props hrun₁ hok₀ hd₀
        have hnot : ¬ MStepS body (p.length + 1) (G m₀) (lg m₀) (G (m₀ + 1)) :=
          fun h => hm₀.2.2 ⟨hdm, h⟩
        rw [← hg] at hrun₁
        obtain ⟨r₀, hrun₀, hex₀⟩ := arm_fwd hcA hokA hrun₁ hD hnot
        rw [List.reverse_reverse] at hrun₀
        obtain ⟨s', f', o⟩ := r₀
        have har₀ : arity f' bt = some (np, nr) :=
          (arity_congr (MachineLSeq.module_eq hrun₀) _).trans har
        have hstay1 : ∀ m, m₀ + 1 ≤ m → m < N → StaysT body G lg p.length m :=
          fun m hm hm' => hstay m (by omega) hm'
        have hblk1 := blk_succ hpt (m := m₀ + 1) (by omega)
          (fun k hk hk' => ⟨_, hstay1 k hk hk'⟩)
        have hdep1 := hD.depth
        have hlogs : segLog lg n (N - n) =
            segLog lg n (m₀ - n) ++ lg m₀ ++ segLog lg (m₀ + 1) (N - (m₀ + 1)) := by
          rw [show N - n = (m₀ - n) + (1 + (N - (m₀ + 1))) by omega, segLog_add, segLog_add,
            segLog_one, show n + (m₀ - n) = m₀ by omega, show m₀ + 1 = m₀ + 1 from rfl,
            List.append_assoc]
        rcases hex₀ with ⟨ws, ho, hgo⟩ | ⟨ws, L', ho, hL', hbr⟩
        · simp only at ho hgo; subst ho
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
          obtain ⟨L₂, hL₂, hd₂⟩ := blk_at hpt (m := m₀ + 1) (by omega)
            (fun h => hB' (m₀ + 1) (by omega) h) (by rw [hgn1, List.reverse_reverse]) hp.hc
            (seg_of_lookup' hp.hc hsg') hok (.inr (.inr (by omega))) hstay1
          obtain ⟨L₁, hL₁, hd₁⟩ := logDiv_cons hone rfl rfl hd₂
          refine ⟨L₁ ++ L₂, ?_, hd₁⟩
          rw [hlogs, List.map_append, ← hL₂, ← hL₁]; simp
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
            obtain ⟨L₂, hL₂, hd₂⟩ := blk_at hpt (m := m₀ + 1) (by omega)
              (fun h => hB' (m₀ + 1) (by omega) h) (W := ws.take nr' ++ L.outer.reverse) (s := s') (f := f')
              (by rw [hgn1]; simp [hLdef]) hp.hc (seg_of_lookup' hp.hc hsg') hok
              (.inr (.inr (by omega))) hstay1
            obtain ⟨L₁, hL₁, hd₁⟩ := logDiv_cons hone rfl rfl hd₂
            refine ⟨L₁ ++ L₂, ?_, hd₁⟩
            rw [hlogs, List.map_append, ← hL₂, ← hL₁]; simp
          | true =>
            subst hloop
            cases hk
            cases hsel
            simp only [armOf, Option.some.injEq] at harm; subst harm
            rw [har₀] at har'; simp only [Option.some.injEq, Prod.mk.injEq] at har'
            obtain ⟨rfl, rfl⟩ := har'
            simp only [hLdef, ↓reduceIte, List.length_cons, Nat.sub_zero, List.reverse_reverse] at hbr
            obtain ⟨Lb, hLb, hb'⟩ := evalLXPS_canonical hrun₀ (by simp)
            obtain ⟨L₂, hL₂, hd₂⟩ := hA' (m₀ + 1) (by omega) (by omega) p c i sg sg.body _ bt true
              false [] 0 _ (ws.take np ++ V'.drop np) np nr ls s' f' (ws.take np ++ V'.drop np) hp
              .loop hok (.plain (fun _ _ _ => nofun)) rfl har₀ (by simpa using hbr)
              (by simpa using hdep1) hstay1
            refine ⟨Lb ++ L₂, ?_, LogDivXP.loopBack har hb' (by simpa [liftInstr] using hd₂)⟩
            rw [hlogs, List.map_append, ← hL₂, ← hLb]
    · have hnN' : n = N := by omega
      subst hnN'
      rcases hpt with ⟨p₁, c₁, i₁, stk₁, ls₁, s₁, f₁, hGN, hc₁, hd⟩ |
        ⟨p₁, c₁, i₁, sg₁, bt₁, b₁, ls₁, np₁, nr₁, V₁, s₁, f₁, hp₁, har₁, hGN, hd⟩
      · rw [← hg] at hGN
        simp only [MState.mk.injEq, Target.block.injEq, BlockId.mk.injEq] at hGN
        obtain ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl⟩ := hGN
        rw [hcA] at hc₁; cases hc₁
        refine ⟨[], by simp [segLog], descend hk hsel harm har (.div ?_)⟩
        simpa [restAt_zero] using hd
      · rw [← hg] at hGN
        simp only [MState.mk.injEq, Target.block.injEq, BlockId.mk.injEq, List.cons.injEq,
          hLdef, LFrame.mk.injEq] at hGN
        obtain ⟨⟨hpp, -⟩, hstk, ⟨⟨har1, hout, hloop, htry, hcs, hbt⟩, rfl⟩, rfl, rfl⟩ := hGN
        obtain ⟨rfl, hia⟩ := List.append_inj' hpp rfl
        simp only [List.cons.injEq, Prod.mk.injEq, and_true] at hia
        obtain ⟨rfl, rfl⟩ := hia
        subst hloop htry hcs hbt
        simp only [↓reduceIte] at har1
        subst har1
        obtain ⟨ht₁, -, -⟩ := pos_term hp₁ rfl
        have hcc : c₁ = c := by
          have := hp₁.hc; rw [hp.hc] at this; exact (Option.some.inj this).symm
        subst hcc
        have hsgeq : sg₁ = sg := by
          have := hp₁.hsg; rw [hp.hsg] at this; exact (Option.some.inj this).symm
        subst hsgeq
        rw [ht] at ht₁; cases ht₁
        cases hsel
        have hV : V₁ = V' := by
          have h1 : V₁.take np = V'.take np := by simpa using hstk.symm
          have h2 : V₁.drop np = V'.drop np := by simpa using hout.symm
          rw [← List.take_append_drop np V₁, h1, h2, List.take_append_drop]
        subst hV
        exact ⟨[], by simp [segLog], .div hd⟩

/-- **Both clauses at every time**, by strong induction on the time left. -/
theorem ptAB {body : Expr} {G : ℕ → MState H} {lg : ℕ → List (SCall H)} {N : ℕ}
    (hG : ∀ k, k < N → MStepL body (G k) (lg k) (G (k + 1))) (hpt : PointT body G N) :
    ∀ d n, N - n = d → n ≤ N → (n < N → BClause body G lg N n) ∧ AClause body G lg N n := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro n hd hn
    have hlater : ∀ m, n < m → m ≤ N → (m < N → BClause body G lg N m) ∧ AClause body G lg N m :=
      fun m h1 h2 => ih (N - m) (by omega) m rfl h2
    have hB : n < N → BClause body G lg N n := fun hlt =>
      b_step hpt hlt (hlater (n + 1) (by omega) (by omega)).2 (hlater (n + 1) (by omega) (by omega)).1
    exact ⟨hB, a_step hG hpt hn hB (fun m h1 h2 => (hlater m h1 h2).2)
      (fun m h1 h2 => (hlater m h1 (by omega)).1 h2)⟩

/-- **A logged run from the CFG entry to a point** is divergence of the body after the run's log. -/
theorem prefix_logDiv {body : Expr} {G : ℕ → MState H} {lg : ℕ → List (SCall H)} {N : ℕ}
    {s : Store H} {f : Frame} (hG : ∀ k, k < N → MStepL body (G k) (lg k) (G (k + 1)))
    (hpt : PointT body G N) (h0 : G 0 = initial body s f) :
    ∃ L, segLog lg 0 N = L.map OCall.toS ∧ LogDivXP s f [] (liftInstrs body) L := by
  have hblk : ∀ m, m ≤ N → ∃ b, (G m).node = .block b := by
    intro m hm
    rcases Nat.lt_or_ge m N with h | h
    · exact MachineLDivI.mstepL_block (hG m h)
    · have : m = N := by omega
      subst this; exact point_block hpt
  have hstay0 : ∀ k, 0 ≤ k → k < N → StaysT body G lg ([] : List SeqStep).length k := fun k _ hk =>
    ⟨Nat.zero_le _, MachineLDivI.mstepS_zero (hG k hk) (hblk (k + 1) (by omega))⟩
  have hie := initial_eq body s f
  rw [← h0] at hie
  obtain ⟨hlk, hgn⟩ := gotoN_entry_block hie (hblk 0 (Nat.zero_le _)) (Nat.zero_le _) rfl
  obtain ⟨sg₀, hsg₀⟩ := Option.isSome_iff_exists.mp hlk
  obtain ⟨L, hL, hd⟩ := blk_at hpt (m := 0) (Nat.zero_le _)
    (fun h => (ptAB hG hpt (N - 0) 0 rfl (Nat.zero_le _)).1 h) (p := []) (j := 0) (c := body)
    (W := []) (ls := []) (by simpa using hgn) rfl (seg_of_lookup' rfl hsg₀)
    (by simp [FramesOk]) (.inr (.inl rfl)) hstay0
  exact ⟨L, by simpa using hL, by simpa [restAt_zero] using hd⟩

end Silmaril.Wasm.Cfg.Proofs.MachineLLogDivP
