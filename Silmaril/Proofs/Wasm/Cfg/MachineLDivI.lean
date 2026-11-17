module

public import Silmaril.Proofs.Wasm.Cfg.MachineLRel
public import Silmaril.Proofs.Wasm.Cfg.MachineLDivF

@[expose] public section

/-!
# Infinite local steps of the machine are native divergence (H2, proofs)

The machine runs forever by oracle-answered steps (`InfK`), from the CFG entry. Native divergence
of the body (`XDivergeP.EvalDivXP`) is shown by coinduction over **positions of that run**:

* `QB`: the run is at block `i` of the sequence at `p` at time `n`, the instructions `pre` of the
  block already accounted for, the native configuration `(s, f, N)` the one the block's step reaches
  after them, and every later step stays at depth `|p|` (`StaysK`): the run never leaves the
  sequence.
* `QA`: the run is at the entry of the arm of a structured instruction ending block `i`, entered
  natively from `(s, f, N)`, and never leaves the sequence at `p` from then on.

A structured instruction is resolved by whether the run ever leaves its arm (the first step not
staying one level deeper): never, and the arm diverges (`block`, `loop`, `arm`, `try_`); at a
first leaving step, the arm ran natively to that point (`MachineLRel.arm_fwd`) and its outcome
continues the sequence (`cont`) or re-enters the loop (`loopBack`).
-/

namespace Silmaril.Wasm.Cfg.Proofs.MachineLDivI

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Abstract (EvalLXPS SCall)
open Silmaril.Wasm.Abstract.CallXP (POut EvalOXP)
open Silmaril.Wasm.Abstract.XRecursionP (closedCallXP)
open Silmaril.Wasm.Abstract.XDivergeP (EvalDivXP FunDivXP DivStepXP CallStepXP evalDivXP_iff_step
  funDivXP_iff_step evalDivXP_of_coind)
open Silmaril.Wasm.Cfg.Proofs.Machine (restAt_cons restAt_end restAt_zero seg_of_lookup lookup_eq)
open Silmaril.Wasm.Cfg.Proofs.MachineLFwd
open Silmaril.Wasm.Cfg.Proofs.MachineLBwd (Pos pos_next pos_term isStruct_terminator lift_op
  lift_block lift_loop lift_if lift_try nil_inv nil_inv_normal seg_wf armOf_if armOf_if'
  liftInstrs_ite)
open Silmaril.Wasm.Cfg.Proofs.MachineLRel
open Silmaril.Wasm.Cfg.Proofs.MachineLClosed (AllOk logged_closed allOk_append allOk_nil)

variable {H : Type}

/-! ## Helpers -/

theorem gotoN_lbls {t : Target} {d : Nat} {ls : List LFrame} {W : List Val} {s : Store H}
    {f : Frame} {st' : MState H} (h : gotoN t d ls W s f = some st') :
    st'.lbls = ls.drop (d - depthT t) := by
  simp only [gotoN, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl⟩ := h
  exact popN_fst _ _ _ hp

theorem gotoN_contRev_block {body : Expr} {m a : Nat} {rp : List SeqStep} {ls : List LFrame}
    {W : List Val} {s : Store H} {f : Frame} {st' : MState H}
    (h : gotoN (contRev body ((m, a) :: rp)) rp.length ls W s f = some st')
    (hb : ∃ b, st'.node = .block b) (hd : rp.length ≤ st'.lbls.length)
    (hls : ls.length = rp.length) :
    (lookup body ⟨rp.reverse, m + 1⟩).isSome ∧ st' = ⟨.block ⟨rp.reverse, m + 1⟩, W, ls, s, f⟩ := by
  unfold contRev at h
  split at h
  · next hs =>
    rw [show rp.length = (⟨rp.reverse, m + 1⟩ : BlockId).seq.length by simp] at h
    exact ⟨hs, gotoN_block h⟩
  · exfalso
    have hl := gotoN_lbls h
    rcases rp with _ | ⟨⟨m', a'⟩, rp'⟩
    · simp only [contRev, gotoN, depthT, List.length_nil, Nat.sub_self, popN,
        Option.map_some, Option.some.injEq] at h
      subst h
      obtain ⟨b, hb⟩ := hb
      cases hb
    · have := Proofs.Machine.depth_contRev_cons body m' a' rp'
      rw [hl] at hd
      simp at hd hls this; omega

theorem gotoN_entry_block {body : Expr} {p : List SeqStep} {j : Nat} {ls : List LFrame}
    {W : List Val} {s : Store H} {f : Frame} {st' : MState H}
    (h : gotoN (entry body p j) p.length ls W s f = some st')
    (hb : ∃ b, st'.node = .block b) (hd : p.length ≤ st'.lbls.length)
    (hls : ls.length = p.length) :
    (lookup body ⟨p, j⟩).isSome ∧ st' = ⟨.block ⟨p, j⟩, W, ls, s, f⟩ := by
  unfold entry at h
  split at h
  · next hs =>
    rw [show p.length = (⟨p, j⟩ : BlockId).seq.length from rfl] at h
    exact ⟨hs, gotoN_block h⟩
  · exfalso
    have hl := gotoN_lbls h
    unfold cont at h hl
    rcases hp : p.reverse with _ | ⟨⟨m', a'⟩, rp'⟩
    · rw [hp] at h
      simp only [contRev, gotoN, depthT, popN, Option.map_some, Option.some.injEq,
        List.reverse_eq_nil_iff.mp hp, List.length_nil, Nat.sub_self] at h
      subst h
      obtain ⟨b, hb⟩ := hb
      cases hb
    · have := Proofs.Machine.depth_contRev_cons body m' a' rp'
      rw [hp] at hl
      rw [hl] at hd
      have hpl : p.length = rp'.length + 1 := by
        rw [← List.length_reverse, hp]; simp
      simp at hd; omega

/-- A dispatch staying at the depth of its own frames is falling through. -/
theorem dispS_own {body : Expr} {b : BlockId} {ls : List LFrame} {r : Store H × Frame × POut}
    {st' : MState H} (h : DispS body ls.length b ls r st') : r.2.2.IsNormal := by
  cases h with
  | next => trivial
  | br _ _ hk => omega
  | catch_ _ _ _ _ _ _ hk => omega

/-- **A step staying at depth `0` is any step to a block.** -/
theorem mstepS_zero {body : Expr} {st st' : MState H} {l : List (SCall H)}
    (h : MStepL body st l st') (hb : ∃ b, st'.node = .block b) : MStepS body 0 st l st' := by
  have hd : ∀ {b : BlockId} {ls : List LFrame} {r : Store H × Frame × POut},
      DispL body b ls r st' → DispS body 0 b ls r st' := by
    intro b ls r hd
    cases hd with
    | next hg => exact .next hg (Nat.zero_le _)
    | br hL hg =>
      have hk := (List.getElem?_eq_some_iff.mp hL).1
      exact .br hL hg (by omega) (Nat.zero_le _)
    | brOut => obtain ⟨_, hb⟩ := hb; cases hb
    | ret => obtain ⟨_, hb⟩ := hb; cases hb
    | trap => obtain ⟨_, hb⟩ := hb; cases hb
    | raise => obtain ⟨_, hb⟩ := hb; cases hb
    | catch_ hpass hL hT hc hL' hg =>
      have hk := (List.getElem?_eq_some_iff.mp hL').1
      exact .catch_ hpass hL hT hc hL' hg (by omega) (Nat.zero_le _)
    | catchOut => obtain ⟨_, hb⟩ := hb; cases hb
  cases h with
  | run hb' ht hr hdl => exact .run hb' ht hr (hd hdl)
  | abort hb' hr hn hdl => exact .abort hb' hr hn (hd hdl)
  | enter hb' ht harm hkind hr hsel har hg =>
    exact .enter hb' ht harm hkind hr hsel har hg (Nat.zero_le _)

/-- **A structured instruction run alone**, natively, from the arm's run and its frame's
continuation (`WrapL`) with nothing after it. -/
theorem wrap_one {t : Instr} {bt : BlockType} {loop tryT : Bool} {cs : List Catch} {N V' : List Val}
    {a : Nat} {c' : List Instr} {np nr : Nat} {s : Store H} {f : Frame} {l₀ l₁ : List (SCall H)}
    {r₀ r₁ : Store H × Frame × POut} (hk : StructKind t bt loop tryT cs) (hsel : ArmSel t N a V')
    (harm : armOf t a = some c') (har : arity f bt = some (np, nr))
    (hrun : EvalLXPS s f (V'.take np) (liftInstrs c') l₀ r₀)
    (hw : WrapL ⟨if loop then np else nr, (V'.drop np).reverse, loop, tryT, cs, bt⟩ t [] r₀ l₁ r₁) :
    EvalLXPS s f N [liftInstr t] (l₀ ++ l₁) r₁ := by
  have hdr : V'.drop np =
      (⟨if loop then np else nr, (V'.drop np).reverse, loop, tryT, cs, bt⟩ : LFrame).outer.reverse :=
    by simp
  cases hsel with
  | plain hi => simpa [liftInstrs] using wrap_sound hk harm hi har hdr hrun hw
  | cond hb => simpa [liftInstrs] using wrap_sound_if hk harm hb rfl har hdr hrun hw

theorem mstepL_block {body : Expr} {st st' : MState H} {l : List (SCall H)}
    (h : MStepL body st l st') : ∃ b, st.node = .block b := by
  cases h <;> exact ⟨_, rfl⟩

theorem mrunS_snoc {body : Expr} {δ : Nat} {st st₁ st₂ : MState H} {l l' : List (SCall H)}
    (h : MRunS body δ st l st₁) (hs : MStepS body δ st₁ l' st₂) : MRunS body δ st (l ++ l') st₂ := by
  induction h with
  | refl => simpa using MRunS.step hs (.refl _)
  | step h₁ _ ih => simpa [List.append_assoc] using MRunS.step h₁ (ih hs)

/-! ## Positions of an infinite run -/

section Run

variable (body : Expr) (g : ℕ → MState H)

/-- **A step staying at depth `δ`**, from a state at least that deep, oracle-answered. -/
def StaysK (δ : Nat) (st st' : MState H) : Prop :=
  δ ≤ st.lbls.length ∧ ∃ l, MStepS body δ st l st' ∧ AllOk closedCallXP l

/-- **What step `n`, at block `i` of the sequence at `p`, does from `(s, f, N)`**, the code `post`
left: runs it straight to a dispatch staying in the sequence, or runs its part `X` before a
structured terminator `t` and enters an arm of `t`. -/
def ResB (n : Nat) (p : List SeqStep) (i : Nat) (sg : Segment) (post : List Instr)
    (ls : List LFrame) (s : Store H) (f : Frame) (N : List Val) : Prop :=
  (∃ (l' : List (SCall H)) (r' : Store H × Frame × POut),
    EvalLXPS s f N (liftInstrs post) l' r' ∧ AllOk closedCallXP l' ∧
      (∀ t, sg.term = some t → ¬ Instr.IsStruct t) ∧
      DispS body p.length ⟨p, i⟩ ls r' (g (n + 1))) ∨
  (∃ (X : List Instr) (t : Instr) (l' : List (SCall H)) (s₁ : Store H) (f₁ : Frame)
    (V : List Val) (a : Nat) (c' : List Instr) (V' : List Val) (np nr : Nat) (bt : BlockType)
    (loop tryT : Bool) (cs : List Catch),
    post = X ++ [t] ∧ sg.term = some t ∧ StructKind t bt loop tryT cs ∧
      EvalLXPS s f N (liftInstrs X) l' (s₁, f₁, .flow (.normal V)) ∧ AllOk closedCallXP l' ∧
      ArmSel t V a V' ∧ armOf t a = some c' ∧ arity f₁ bt = some (np, nr) ∧
      gotoN (entry body (p ++ [(i, a)]) 0) (p.length + 1)
        (⟨if loop then np else nr, (V'.drop np).reverse, loop, tryT, cs, bt⟩ :: ls)
        (V'.take np).reverse s₁ f₁ = some (g (n + 1)))

/-- **The run in a block of a sequence it never leaves**, at a native configuration of the
block's step. -/
def QB (s : Store H) (f : Frame) (N : List Val) (es : List BExpr) : Prop :=
  ∃ (n : Nat) (p : List SeqStep) (c : List Instr) (i : Nat) (sg : Segment) (pre post : List Instr)
    (ls : List LFrame),
    Pos body p c i sg pre post ∧ FramesOk body p.reverse ls ∧
      es = liftInstrs post ++ liftInstrs (restAt c (i + 1)) ∧
      (∀ m, n < m → StaysK body p.length (g m) (g (m + 1))) ∧
      ResB body g n p i sg post ls s f N

/-- **The run at the entry of an arm of a structured instruction** entered natively from
`(s, f, N)`, in a sequence the run never leaves. -/
def QA (s : Store H) (f : Frame) (N : List Val) (es : List BExpr) : Prop :=
  ∃ (n : Nat) (p : List SeqStep) (c : List Instr) (i : Nat) (sg : Segment) (pre : List Instr)
    (t : Instr) (bt : BlockType) (loop tryT : Bool) (cs : List Catch) (a : Nat)
    (c' : List Instr) (V' : List Val) (np nr : Nat) (ls : List LFrame),
    Pos body p c i sg pre [t] ∧ StructKind t bt loop tryT cs ∧ FramesOk body p.reverse ls ∧
      es = liftInstr t :: liftInstrs (restAt c (i + 1)) ∧ ArmSel t N a V' ∧
      armOf t a = some c' ∧ arity f bt = some (np, nr) ∧
      gotoN (entry body (p ++ [(i, a)]) 0) (p.length + 1)
        (⟨if loop then np else nr, (V'.drop np).reverse, loop, tryT, cs, bt⟩ :: ls)
        (V'.take np).reverse s f = some (g n) ∧
      (∀ m, n ≤ m → StaysK body p.length (g m) (g (m + 1)))

/-- The coinductive set: positions of the run, or native divergence. -/
def QX (s : Store H) (f : Frame) (N : List Val) (es : List BExpr) : Prop :=
  QB body g s f N es ∨ QA body g s f N es ∨ EvalDivXP s f N es

end Run

/-- **The step from a block of a sequence the run never leaves** is a residual from the block's
start. -/
theorem resB_of_stays {body : Expr} {g : ℕ → MState H} {n : Nat} {p : List SeqStep} {j : Nat}
    {sg : Segment} {stk : List Val} {ls : List LFrame} {s : Store H} {f : Frame}
    (hgn : g n = ⟨.block ⟨p, j⟩, stk, ls, s, f⟩) (hls : ls.length = p.length)
    (hlk : lookup body ⟨p, j⟩ = some sg) (hS : StaysK body p.length (g n) (g (n + 1))) :
    ResB body g n p j sg sg.instrs ls s f stk.reverse := by
  obtain ⟨-, l, hS, hl⟩ := hS
  rw [hgn] at hS
  cases hS with
  | run hb ht hr hd =>
    rw [hlk] at hb; cases hb
    exact .inl ⟨l, _, by simpa [codeOf_eq] using hr, hl, ht, hd⟩
  | abort hb hr hn hd =>
    rw [← hls] at hd
    exact absurd (dispS_own hd) hn
  | @enter _ _ _ V V' _ _ s₁ _ f₁ i a c bt np nr loop tryT cs _ _ hb ht harm hkind hr hsel har hg _ =>
    rw [hlk] at hb; cases hb
    exact .inr ⟨sg.body, i, l, s₁, f₁, V, a, c, V', np, nr, bt, loop, tryT, cs,
      by simp [Segment.instrs, ht], ht, hkind, hr, hl, hsel, harm, har, hg⟩

theorem pos_start {body : Expr} {p : List SeqStep} {c : List Instr} {j : Nat} {sg : Segment}
    (hc : seqAt body p = some c) (hsg : (segment c)[j]? = some sg) :
    Pos body p c j sg [] sg.instrs :=
  ⟨hc, hsg, rfl, (segment_isSegmentation c).2.2.2 sg (List.mem_of_getElem? hsg),
    fun _ _ _ => Nat.zero_le _⟩

theorem seg_of_lookup' {body : Expr} {p : List SeqStep} {c : List Instr} {j : Nat} {sg : Segment}
    (hc : seqAt body p = some c) (h : lookup body ⟨p, j⟩ = some sg) : (segment c)[j]? = some sg := by
  rw [lookup_eq, hc] at h; simpa using h

theorem lift_rest {c : List Instr} {j : Nat} {sg : Segment} (hsg : (segment c)[j]? = some sg) :
    liftInstrs (restAt c j) = liftInstrs sg.instrs ++ liftInstrs (restAt c (j + 1)) := by
  rw [restAt_cons hsg, MachineLSeq.liftInstrs_append]

/-- **Continuing at the next block** of a sequence the run never leaves, after a structured
instruction ran natively to `N₂`. -/
theorem qb_next {body : Expr} {g : ℕ → MState H} {n : Nat} {p : List SeqStep} {c : List Instr}
    {i : Nat} {ls : List LFrame} {s : Store H} {f : Frame} {N₂ : List Val}
    (hc : seqAt body p = some c) (hok : FramesOk body p.reverse ls) (hls : ls.length = p.length)
    (hlk : (lookup body ⟨p, i + 1⟩).isSome)
    (hgn : g n = ⟨.block ⟨p, i + 1⟩, N₂.reverse, ls, s, f⟩)
    (hstay : ∀ m, n ≤ m → StaysK body p.length (g m) (g (m + 1))) :
    QX body g s f N₂ (liftInstrs (restAt c (i + 1))) := by
  obtain ⟨sg', hsg'⟩ := Option.isSome_iff_exists.mp hlk
  have hsg := seg_of_lookup' hc hsg'
  have hres := resB_of_stays hgn hls hsg' (hstay n le_rfl)
  rw [List.reverse_reverse] at hres
  exact .inl ⟨n, p, c, i + 1, sg', [], sg'.instrs, ls, pos_start hc hsg, hok, lift_rest hsg,
    fun m hm => hstay m (by omega), hres⟩

/-- **At the entry of an arm**: one native unfolding. -/
theorem qa_step {body : Expr} {g : ℕ → MState H} {s : Store H} {f : Frame} {N : List Val}
    {es : List BExpr} (h : QA body g s f N es) : DivStepXP (QX body g) FunDivXP s f N es := by
  obtain ⟨n, p, c, i, sg, pre, t, bt, loop, tryT, cs, a, c', V', np, nr, ls, hp, hk, hok, rfl,
    hsel, harm, har, hg, hstay⟩ := h
  obtain ⟨ht, -, rfl⟩ := pos_term hp (isStruct_terminator ⟨_, _, _, _, hk⟩)
  have hls : ls.length = p.length := by simpa using Proofs.Machine.framesOk_length _ _ hok
  have hcA : seqAt body (p ++ [(i, a)]) = some c' := by
    rw [Proofs.Machine.seqAt_append]; simp [hp.hc, hp.hsg, ht, harm]
  set L : LFrame := ⟨if loop then np else nr, (V'.drop np).reverse, loop, tryT, cs, bt⟩ with hLdef
  have hokA : FramesOk body ((i, a) :: p.reverse) (L :: ls) := by
    simpa using MachineLBwd.arm_ok hp hk harm hok (if loop then np else nr) (V'.drop np).reverse
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
    obtain ⟨hdn, l, hS, -⟩ := hstay n le_rfl
    obtain ⟨b, stk, ls', s', f', hgb⟩ := hS.block
    obtain ⟨hlk, hgn⟩ := gotoN_contRev_block hg' ⟨b, by rw [hgb]⟩ (by simpa using hdn)
      (by simpa using hls)
    simp only [List.reverse_reverse] at hlk hgn
    have hw : WrapL L t [] (s, f, .flow (.normal (V'.take np))) []
        (s, f, .flow (.normal (L.outer ++ topVals nr' (V'.take np).reverse).reverse)) := by
      simpa using wrap_fall (W := (V'.take np).reverse) (t := t) (rest := []) har'
        (by simpa [liftInstrs] using
          @EvalLXPS.nil H s f (L.outer ++ topVals nr' (V'.take np).reverse).reverse)
    have hone := wrap_one hk hsel harm har (by simpa [liftInstrs] using EvalLXPS.nil) hw
    refine .cont (logged_closed hone (allOk_nil _)) ?_
    exact qb_next hp.hc hok hls hlk (by rw [hgn, List.reverse_reverse]) hstay
  | some sg₀ =>
    have hsg₀ := hseg
    have hg0 := MachineLDivB.gotoN_entry hcA hsg₀ (L :: ls) (V'.take np).reverse s f
    rw [List.length_append, List.length_singleton] at hg0
    rw [hg0] at hg; simp only [Option.some.injEq] at hg
    by_cases hall : ∀ m, n ≤ m → StaysK body (p.length + 1) (g m) (g (m + 1))
    · have hres := resB_of_stays (n := n) (p := p ++ [(i, a)]) (j := 0) (sg := sg₀) hg.symm
        (by simpa using hls)
        (by rw [lookup_eq, hcA]; simp [hsg₀]) (by simpa using hall n le_rfl)
      have hQ : QX body g s f (V'.take np) (liftInstrs c') := by
        refine .inl ⟨n, p ++ [(i, a)], c', 0, sg₀, [], sg₀.instrs, L :: ls, pos_start hcA hsg₀,
          by simpa using hokA, by simpa [restAt_zero] using lift_rest hsg₀,
          fun m hm => by simpa using hall m (by omega), ?_⟩
        simpa using hres
      cases hk with
      | block =>
        cases hsel
        simp only [armOf, Option.some.injEq] at harm; subst harm
        exact .block har hQ
      | loop =>
        cases hsel
        simp only [armOf, Option.some.injEq] at harm; subst harm
        exact .loop har hQ
      | tryTable =>
        cases hsel
        simp only [armOf, Option.some.injEq] at harm; subst harm
        exact .try_ har hQ
      | if_ =>
        cases hsel with
        | cond hb =>
          have hc' := armOf_if harm; subst hc'
          rw [← liftInstrs_ite] at hQ
          exact .arm (logged_closed .nil (allOk_nil _)) hb har hQ
        | plain hi => exact absurd rfl (hi _ _ _)
    · push Not at hall
      classical
      have hex : ∃ m, n ≤ m ∧ ¬ StaysK body (p.length + 1) (g m) (g (m + 1)) := hall
      have hm₀ := Nat.find_spec hex
      have hbefore : ∀ m, n ≤ m → m < Nat.find hex →
          StaysK body (p.length + 1) (g m) (g (m + 1)) := fun m h1 h2 => by
        by_contra hc; exact Nat.find_min hex h2 ⟨h1, hc⟩
      have hinner : ∀ k, n + k ≤ Nat.find hex → ∃ l, MRunS body (p.length + 1) (g n) l (g (n + k)) ∧
          AllOk closedCallXP l := by
        intro k
        induction k with
        | zero => intro _; exact ⟨[], by simpa using MRunS.refl (body := body) (δ := p.length + 1) (g n),
            allOk_nil _⟩
        | succ k ih =>
          intro hk'
          obtain ⟨l, hr, hl⟩ := ih (by omega)
          obtain ⟨-, l', hs, hl'⟩ := hbefore (n + k) (by omega) (by omega)
          refine ⟨l ++ l', ?_, allOk_append.2 ⟨hl, hl'⟩⟩
          rw [show n + (k + 1) = n + k + 1 by omega]
          exact mrunS_snoc hr hs
      obtain ⟨l₁, hrun₁, hl₁⟩ := hinner (Nat.find hex - n) (by omega)
      rw [show n + (Nat.find hex - n) = Nat.find hex by omega] at hrun₁
      obtain ⟨-, l₂, hD, hl₂⟩ := hstay (Nat.find hex) hm₀.1
      have hok₀ : MInv body (g n) := by
        rw [← hg]; show FramesOk body (p ++ [(i, a)]).reverse (L :: ls); simpa using hokA
      have hd₀ : p.length + 1 ≤ (g n).lbls.length := by rw [← hg]; simp [hls]
      obtain ⟨-, hdm⟩ := run_props hrun₁ hok₀ hd₀
      have hnot : ¬ MStepS body (p.length + 1) (g (Nat.find hex)) l₂ (g (Nat.find hex + 1)) :=
        fun h => hm₀.2 ⟨hdm, l₂, h, hl₂⟩
      rw [← hg] at hrun₁
      obtain ⟨r₀, hrun₀, hex₀⟩ := arm_fwd hcA hokA hrun₁ hD hnot
      rw [List.reverse_reverse] at hrun₀
      have hlr := allOk_append.2 ⟨hl₁, hl₂⟩
      obtain ⟨s', f', o⟩ := r₀
      have har₀ : arity f' bt = some (np, nr) :=
        (arity_congr (MachineLSeq.module_eq hrun₀) _).trans har
      have hstay1 : ∀ m, Nat.find hex + 1 ≤ m → StaysK body p.length (g m) (g (m + 1)) :=
        fun m hm => hstay m (by omega)
      obtain ⟨hdn1, l₃, hS1, -⟩ := hstay1 _ le_rfl
      obtain ⟨b1, _, _, _, _, hgb1⟩ := hS1.block
      have hblk1 : ∃ b, (g (Nat.find hex + 1)).node = .block b := ⟨b1, by rw [hgb1]⟩
      rcases hex₀ with ⟨ws, ho, hgo⟩ | ⟨ws, L', ho, hL', hbr⟩
      · simp only at ho hgo; subst ho
        rw [show ((i, a) :: p.reverse).length = p.reverse.length + 1 by simp] at hgo
        obtain ⟨np', nr', har', hgo'⟩ :=
          gotoN_cons (Proofs.Machine.depth_contRev_cons body i a _) hgo
        obtain ⟨hlk, hgn1⟩ := gotoN_contRev_block hgo' hblk1 (by simpa using hdn1)
          (by simpa using hls)
        simp only [List.reverse_reverse] at hlk hgn1
        have hw : WrapL L t [] (s', f', .flow (.normal ws)) []
            (s', f', .flow (.normal (L.outer ++ topVals nr' ws.reverse).reverse)) := by
          simpa using wrap_fall (W := ws.reverse) (t := t) (rest := []) har'
            (by simpa [liftInstrs] using
              @EvalLXPS.nil H s' f' (L.outer ++ topVals nr' ws.reverse).reverse)
        have hone := wrap_one hk hsel harm har hrun₀ hw
        refine .cont (logged_closed hone (by simpa using hlr)) ?_
        exact qb_next hp.hc hok hls hlk (by rw [hgn1, List.reverse_reverse]) hstay1
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
            (by simpa using hdn1) (by simpa using hls)
          simp only [List.reverse_reverse] at hlk hgn1
          have hw : WrapL L t [] (s', f', .flow (.brk 0 ws)) []
              (s', f', .flow (.normal (ws.take nr' ++ L.outer.reverse))) :=
            .ok (by simp [hLdef, hloop]) har' rfl (by simpa [liftInstrs] using EvalLXPS.nil)
          have hone := wrap_one hk hsel harm har hrun₀ hw
          refine .cont (logged_closed hone (by simpa using hlr)) ?_
          refine qb_next hp.hc hok hls hlk ?_ hstay1
          rw [hgn1]; simp [hLdef]
        | true =>
          subst hloop
          cases hk
          cases hsel
          simp only [armOf, Option.some.injEq] at harm; subst harm
          rw [har₀] at har'; simp only [Option.some.injEq, Prod.mk.injEq] at har'
          obtain ⟨rfl, rfl⟩ := har'
          simp only [hLdef, ↓reduceIte, List.length_cons, Nat.sub_zero, List.reverse_reverse] at hbr
          refine .loopBack har (logged_closed hrun₀ (by simpa using hlr)) (.inr (.inl ?_))
          refine ⟨Nat.find hex + 1, p, c, i, sg, sg.body, _, bt, true, false, [], 0, _,
            ws.take np ++ N.drop np, np, nr, ls, hp, .loop, hok, by simp [liftInstr],
            .plain (fun _ _ _ => nofun), rfl, har₀, ?_, hstay1⟩
          simpa using hbr

/-- **At a block of a sequence the run never leaves**: one native unfolding. -/
theorem qb_step {body : Expr} {g : ℕ → MState H} :
    ∀ (post : List Instr) {n : Nat} {p : List SeqStep} {c : List Instr} {i : Nat} {sg : Segment}
      {pre : List Instr} {ls : List LFrame} {s : Store H} {f : Frame} {N : List Val},
      Pos body p c i sg pre post → FramesOk body p.reverse ls →
      (∀ m, n < m → StaysK body p.length (g m) (g (m + 1))) →
      ResB body g n p i sg post ls s f N →
      DivStepXP (QX body g) FunDivXP s f N (liftInstrs post ++ liftInstrs (restAt c (i + 1)))
  | [], _, _, _, _, _, _, _, _, _, _, hp, _, _, _ => absurd rfl hp.hpost
  | e :: post', n, p, c, i, sg, pre, ls, s, f, N, hp, hok, hstay, hres => by
    have hls : ls.length = p.length := by simpa using Proofs.Machine.framesOk_length _ _ hok
    simp only [liftInstrs, List.cons_append]
    rcases hres with ⟨l', r', hr', hl', ht, hd⟩ |
      ⟨X, t, l', s₁, f₁, V, a, c', V', np, nr, bt, loop, tryT, cs, hpost, hterm, hk, hX, hl', hsel,
        harm, har, hg⟩
    · obtain ⟨s', f', o⟩ := r'
      have hse : ¬ Instr.IsStruct e := fun h => ht e (pos_term hp (isStruct_terminator h)).1 h
      have hsp := MachineLSeq.split [liftInstr e] (liftInstrs post')
        (by simpa [liftInstrs] using hr')
      rcases hsp with ⟨s₂, f₂, N₂, l₁, l₂, h₁, h₂, rfl⟩ | ⟨-, hn⟩
      · obtain ⟨hl₁, hl₂⟩ := allOk_append.1 hl'
        refine .cont (logged_closed h₁ hl₁) ?_
        cases post' with
        | cons e' post'' =>
          exact .inl ⟨n, p, c, i, sg, pre ++ [e], e' :: post'', ls, pos_next hp hse, hok, rfl,
            hstay, .inl ⟨l₂, _, h₂, hl₂, ht, hd⟩⟩
        | nil =>
          obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_inv (by simpa [liftInstrs] using h₂)
          cases hd with
          | next hg hδ =>
            obtain ⟨hdn1, l₃, hS1, -⟩ := hstay (n + 1) (by omega)
            obtain ⟨b1, _, _, _, _, hgb1⟩ := hS1.block
            obtain ⟨hlk, hgn1⟩ := gotoN_entry_block hg ⟨b1, by rw [hgb1]⟩ (by simpa using hdn1) hls
            have := qb_next hp.hc hok hls hlk (by rw [hgn1]) (fun m hm => hstay m (by omega))
            simpa [liftInstrs] using this
      · rw [← hls] at hd; exact absurd (dispS_own hd) hn
    · cases X with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at hpost
        obtain ⟨rfl, rfl⟩ := hpost
        obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_inv_normal (by simpa [liftInstrs] using hX)
        have := qa_step (body := body) (g := g) ⟨n + 1, p, c, i, sg, pre, e, bt, loop, tryT, cs, a,
          c', V', np, nr, ls, hp, hk, hok, rfl, hsel, harm, har, hg, fun m hm => hstay m (by omega)⟩
        simpa [liftInstrs] using this
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
        rcases hsp with ⟨s₂, f₂, N₂, l₁, l₂, h₁, h₂, rfl⟩ | ⟨-, hn⟩
        · obtain ⟨hl₁, hl₂⟩ := allOk_append.1 hl'
          refine .cont (logged_closed h₁ hl₁) ?_
          obtain ⟨e', post'', heq⟩ : ∃ e' post'', X' ++ [t] = e' :: post'' := by
            cases X' with
            | nil => exact ⟨t, [], rfl⟩
            | cons x xs => exact ⟨x, xs ++ [t], rfl⟩
          have hp' := hp
          rw [heq] at hp'
          refine .inl ⟨n, p, c, i, sg, pre ++ [e], e' :: post'', ls, pos_next hp' hse, hok,
            by rw [heq], hstay, .inr ⟨X', t, l₂, s₁, f₁, V, a, c', V', np, nr, bt, loop, tryT, cs,
              heq.symm, hterm, hk, h₂, hl₂, hsel, harm, har, hg⟩⟩
        · exact absurd trivial hn

/-- **Infinite local steps from the CFG entry are native divergence of the body.** -/
theorem infK_div {body : Expr} {s : Store H} {f : Frame} (h : InfK body (initial body s f)) :
    EvalDivXP s f [] (liftInstrs body) := by
  obtain ⟨g, hg0, hg⟩ := h
  have hstay0 : ∀ m, StaysK body 0 (g m) (g (m + 1)) := by
    intro m
    obtain ⟨l, hs, hl⟩ := hg m
    obtain ⟨l', hs', -⟩ := hg (m + 1)
    exact ⟨Nat.zero_le _, l, mstepS_zero hs (mstepL_block hs'), hl⟩
  have hX : ∀ s f N es, QX body g s f N es → DivStepXP (QX body g) FunDivXP s f N es := by
    rintro s f N es (⟨n, p, c, i, sg, pre, post, ls, hp, hok, rfl, hstay, hres⟩ | hA | hD)
    · exact qb_step post hp hok hstay hres
    · exact qa_step hA
    · exact (evalDivXP_iff_step.1 hD).mono (fun _ _ _ _ h => .inr (.inr h)) le_rfl
  have hY : ∀ s a vs, FunDivXP s a vs → CallStepXP (QX body g) FunDivXP s a vs := by
    intro s a vs h
    exact (funDivXP_iff_step.1 h).mono (fun _ _ _ _ h => .inr (.inr h)) le_rfl
  have hle := (evalDivXP_of_coind hX hY).1
  obtain ⟨l, hs, -⟩ := hg 0
  obtain ⟨b, hb⟩ := mstepL_block hs
  have hie := initial_eq body s f
  rw [← hg0] at hie
  obtain ⟨hlk, hgn⟩ := gotoN_entry_block hie ⟨b, hb⟩ (Nat.zero_le _) rfl
  obtain ⟨sg₀, hsg₀⟩ := Option.isSome_iff_exists.mp hlk
  have hres := resB_of_stays (p := []) hgn rfl hsg₀ (hstay0 0)
  have hsg := seg_of_lookup' (c := body) rfl hsg₀
  refine hle _ _ _ _ (.inl ⟨0, [], body, 0, sg₀, [], sg₀.instrs, [], pos_start rfl hsg, trivial,
    by rw [← lift_rest hsg, restAt_zero], fun m _ => hstay0 m, ?_⟩)
  simpa using hres

end Silmaril.Wasm.Cfg.Proofs.MachineLDivI
