module

public import Silmaril.Proofs.Wasm.Cfg.MachineLBwd
public import Silmaril.Proofs.Wasm.Cfg.MachineLPend
public import Silmaril.Proofs.Wasm.Cfg.MachineLClosed
public import Silmaril.Wasm.Cfg.MachineLDiv.Defs
public import Silmaril.Wasm.Abstract.XDivergeP.Thms

@[expose] public section

/-!
# Native host-free divergence is machine divergence (H2, proofs)

`struct_run`: a structured instruction run natively to a normal end, from the entry of its arm, is
a machine run to the position after it (the converse's arm clause, with the continuation an
obligation). `InvB`, `InvA`: the machine is at a block whose rest diverges natively after an
oracle-answered prefix, or at the entry of a loop's arm whose loop diverges natively. `prog`: from
either, the machine makes at least one oracle-answered step to either, or reaches a diverging
callee. `div_machine`: native divergence of a body is `MDivL` from the CFG entry.
-/

namespace Silmaril.Wasm.Cfg.Proofs.MachineLDivB

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Abstract (EvalLXPS SCall ReachLXPS)
open Silmaril.Wasm.Abstract.CallXP (POut EvalOXP)
open Silmaril.Wasm.Abstract.XRecursionP (closedCallXP)
open Silmaril.Wasm.Abstract.XDivergeP (EvalDivXP FunDivXP DivStepXP evalDivXP_iff_step)
open Silmaril.Wasm.Cfg.Proofs.Machine (restAt_cons restAt_end restAt_zero seg_of_lookup lookup_eq)
open Silmaril.Wasm.Cfg.Proofs.MachineLFwd
open Silmaril.Wasm.Cfg.Proofs.MachineLBwd
open Silmaril.Wasm.Cfg.Proofs.MachineLClosed (AllOk closed_logged allOk_append allOk_nil)

variable {H : Type}

/-! ## A structured instruction ending normally -/

/-- **The arm clause of a structured instruction run alone to a normal end**: given what the
machine must do at the position after it (`hK`), it finishes from the entry of the arm. -/
theorem struct_run {body : Expr} {Fin : Store H × Frame × POut → Prop} {Z : MState H → Prop}
    {s : Store H} {f : Frame} {N : List Val} {es : List BExpr} {l : List (SCall H)}
    {r : Store H × Frame × POut} (h : EvalLXPS s f N es l r) :
    ∀ {t : Instr} {s₂ : Store H} {f₂ : Frame} {N₂ : List Val} {p : List SeqStep} {c : List Instr}
      {i : Nat} {sg : Segment} {pre : List Instr} {ls : List LFrame} {l' : List (SCall H)},
      Instr.IsStruct t → es = [liftInstr t] → r = (s₂, f₂, .flow (.normal N₂)) →
      Pos body p c i sg pre [t] → FramesOk body p.reverse ls →
      (∃ st, gotoN (entry body p (i + 1)) p.length ls N₂.reverse s₂ f₂ = some st ∧
        MEndsZ body Fin Z st l') →
      ∀ (a : Nat) (c' : List Instr) (V' : List Val) (np nr : Nat) (bt : BlockType)
        (loop tryT : Bool) (cs : List Catch), StructKind t bt loop tryT cs →
        ArmSel t N a V' → armOf t a = some c' → arity f bt = some (np, nr) →
        ∃ st₁, gotoN (entry body (p ++ [(i, a)]) 0) (p.length + 1)
          (⟨if loop then np else nr, (V'.drop np).reverse, loop, tryT, cs, bt⟩ :: ls)
          (V'.take np).reverse s f = some st₁ ∧ MEndsZ body Fin Z st₁ (l ++ l') := by
  induction h with
  | blockOk har hbody hvs hk _ _ =>
    intro t s₂ f₂ N₂ p c i sg pre ls l' hst hes hr hp hok hK
    obtain ⟨hhd, rfl⟩ := List.cons.inj hes
    obtain ⟨b₀, rfl, rfl⟩ := lift_block hhd.symm
    subst hr
    obtain ⟨rfl, rfl, h3, rfl⟩ := nil_inv hk
    simp only [POut.flow.injEq, Flow.normal.injEq] at h3; subst h3
    intro a c' V' np nr bt' loop tryT cs hk' hsel harm' har'
    cases hk'
    cases hsel
    simp only [armOf, Option.some.injEq] at harm'; subst harm'
    have har₀ := har
    rw [har'] at har₀; simp only [Option.some.injEq, Prod.mk.injEq] at har₀
    obtain ⟨rfl, rfl⟩ := har₀
    have hokA := arm_ok (a := 0) hp .block rfl hok
    have har₁ := (arity_congr (MachineLSeq.module_eq hbody) _).trans har'
    obtain ⟨st, hg, hE⟩ := hK
    exact mEnds_congr' (by simp) (arm_entry hp .block rfl hok hbody (mot hbody)
      (exit_ok_like (hokA _ _) rfl har₁ hvs ⟨st, by simpa [List.reverse_append] using hg, hE⟩))
  | loopOk har hbody hk _ _ =>
    intro t s₂ f₂ N₂ p c i sg pre ls l' hst hes hr hp hok hK
    obtain ⟨hhd, rfl⟩ := List.cons.inj hes
    obtain ⟨b₀, rfl, rfl⟩ := lift_loop hhd.symm
    subst hr
    obtain ⟨rfl, rfl, h3, rfl⟩ := nil_inv hk
    simp only [POut.flow.injEq, Flow.normal.injEq] at h3; subst h3
    intro a c' V' np nr bt' loop tryT cs hk' hsel harm' har'
    cases hk'
    cases hsel
    simp only [armOf, Option.some.injEq] at harm'; subst harm'
    have har₀ := har
    rw [har'] at har₀; simp only [Option.some.injEq, Prod.mk.injEq] at har₀
    obtain ⟨rfl, rfl⟩ := har₀
    have har₁ := (arity_congr (MachineLSeq.module_eq hbody) _).trans har'
    obtain ⟨st, hg, hE⟩ := hK
    exact mEnds_congr' (by simp) (arm_entry hp .loop rfl hok hbody (mot hbody)
      (exit_fall har₁ ⟨st, by simpa [List.reverse_append] using hg, hE⟩))
  | loopBack har hbody hk _ ihk =>
    intro t s₂ f₂ N₂ p c i sg pre ls l' hst hes hr hp hok hK
    obtain ⟨hhd, rfl⟩ := List.cons.inj hes
    obtain ⟨b₀, rfl, rfl⟩ := lift_loop hhd.symm
    intro a c' V' np nr bt' loop tryT cs hk' hsel harm' har'
    cases hk'
    cases hsel
    simp only [armOf, Option.some.injEq] at harm'; subst harm'
    have har₀ := har
    rw [har'] at har₀; simp only [Option.some.injEq, Prod.mk.injEq] at har₀
    obtain ⟨rfl, rfl⟩ := har₀
    have hokA := arm_ok (a := 0) hp .loop rfl hok
    have har₁ := (arity_congr (MachineLSeq.module_eq hbody) _).trans har'
    obtain ⟨st, hg, hE⟩ := ihk hst rfl hr hp hok hK 0 _ _ np nr _ true false [] .loop
      (.plain (fun _ _ _ => nofun)) rfl har₁
    exact mEnds_congr' (by simp) (arm_entry hp .loop rfl hok hbody (mot hbody)
      (exit_loopBack (hokA _ _) rfl har₁ ⟨st, by simpa using hg, hE⟩))
  | ifOk hc hb har harm hvs hk _ _ _ =>
    intro t s₂ f₂ N₂ p c i sg pre ls l' hst hes hr hp hok hK
    obtain ⟨hhd, rfl⟩ := List.cons.inj hes
    obtain ⟨t₀, e₀, rfl, rfl, rfl, rfl⟩ := lift_if hhd.symm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_inv_normal hc
    subst hr
    obtain ⟨rfl, rfl, h3, rfl⟩ := nil_inv hk
    simp only [POut.flow.injEq, Flow.normal.injEq] at h3; subst h3
    rw [liftInstrs_ite] at harm
    intro a c' V' np nr bt' loop tryT cs hk' hsel harm' har'
    cases hk'
    cases hsel with
    | cond hb' =>
      rw [hb] at hb'; cases hb'
      have hc' := armOf_if harm'; subst hc'
      have har₀ := har
      rw [har'] at har₀; simp only [Option.some.injEq, Prod.mk.injEq] at har₀
      obtain ⟨rfl, rfl⟩ := har₀
      have hokA := arm_ok hp .if_ harm' hok
      have har₁ := (arity_congr (MachineLSeq.module_eq harm) _).trans har'
      obtain ⟨st, hg, hE⟩ := hK
      exact mEnds_congr' (by simp) (arm_entry hp .if_ harm' hok harm (mot harm)
        (exit_ok_like (hokA _ _) rfl har₁ hvs ⟨st, by simpa [List.reverse_append] using hg, hE⟩))
    | plain hi => exact absurd rfl (hi _ _ _)
  | tryOk har hbody hvs hk _ _ =>
    intro t s₂ f₂ N₂ p c i sg pre ls l' hst hes hr hp hok hK
    obtain ⟨hhd, rfl⟩ := List.cons.inj hes
    obtain ⟨b₀, rfl, rfl⟩ := lift_try hhd.symm
    subst hr
    obtain ⟨rfl, rfl, h3, rfl⟩ := nil_inv hk
    simp only [POut.flow.injEq, Flow.normal.injEq] at h3; subst h3
    intro a c' V' np nr bt' loop tryT cs hk' hsel harm' har'
    cases hk'
    cases hsel
    simp only [armOf, Option.some.injEq] at harm'; subst harm'
    have har₀ := har
    rw [har'] at har₀; simp only [Option.some.injEq, Prod.mk.injEq] at har₀
    obtain ⟨rfl, rfl⟩ := har₀
    have hokA := arm_ok (a := 0) hp .tryTable rfl hok
    have har₁ := (arity_congr (MachineLSeq.module_eq hbody) _).trans har'
    obtain ⟨st, hg, hE⟩ := hK
    exact mEnds_congr' (by simp) (arm_entry hp .tryTable rfl hok hbody (mot hbody)
      (exit_ok_like (hokA _ _) rfl har₁ hvs ⟨st, by simpa [List.reverse_append] using hg, hE⟩))
  | blockEsc _ _ ho _ | loopEsc _ _ ho _ | ifEsc _ _ _ _ ho _ _ | tryEsc _ _ ho _ _ =>
    intro t s₂ f₂ N₂ p c i sg pre ls l' hst hes hr
    simp only [Prod.mk.injEq] at hr
    obtain ⟨-, -, rfl⟩ := hr
    exact absurd ho (by simp [POut.Escapes, Flow.Escapes])
  | ifAbort _ ho _ =>
    intro t s₂ f₂ N₂ p c i sg pre ls l' hst hes hr
    simp only [Prod.mk.injEq] at hr
    obtain ⟨-, -, rfl⟩ := hr
    exact absurd trivial ho
  | nil => intro t _ _ _ _ _ _ _ _ _ _ _ hes; simp at hes
  | blockBrk | loopBrk | ifBrk | tryBrk | tryCatch | tryRethrow =>
    intro t _ _ _ _ _ _ _ _ _ _ _ _ hr; simp at hr
  | _ =>
    intro t _ _ _ _ _ _ _ _ _ _ hst hes
    obtain ⟨hhd, -⟩ := List.cons.inj hes
    exact absurd hst (lift_op hhd.symm).2.2

/-- **Which arm a structured instruction run alone to a normal end entered**, natively. -/
theorem struct_sel {s : Store H} {f : Frame} {N : List Val} {es : List BExpr} {l : List (SCall H)}
    {r : Store H × Frame × POut} (h : EvalLXPS s f N es l r) :
    ∀ {t : Instr} {bt : BlockType} {loop tryT : Bool} {cs : List Catch} {s₂ : Store H}
      {f₂ : Frame} {N₂ : List Val}, es = [liftInstr t] → r = (s₂, f₂, .flow (.normal N₂)) →
      StructKind t bt loop tryT cs →
      ∃ (a : Nat) (c' : List Instr) (V' : List Val) (np nr : Nat),
        ArmSel t N a V' ∧ armOf t a = some c' ∧ arity f bt = some (np, nr) := by
  intro t bt loop tryT cs s₂ f₂ N₂ hes hr hk
  cases h with
  | blockOk har =>
    obtain ⟨hhd, -⟩ := List.cons.inj hes
    obtain ⟨b₀, rfl, rfl⟩ := lift_block hhd.symm
    cases hk
    exact ⟨0, _, _, _, _, .plain (fun _ _ _ => nofun), rfl, har⟩
  | loopOk har | loopBack har =>
    obtain ⟨hhd, -⟩ := List.cons.inj hes
    obtain ⟨b₀, rfl, rfl⟩ := lift_loop hhd.symm
    cases hk
    exact ⟨0, _, _, _, _, .plain (fun _ _ _ => nofun), rfl, har⟩
  | tryOk har =>
    obtain ⟨hhd, -⟩ := List.cons.inj hes
    obtain ⟨b₀, rfl, rfl⟩ := lift_try hhd.symm
    cases hk
    exact ⟨0, _, _, _, _, .plain (fun _ _ _ => nofun), rfl, har⟩
  | ifOk hc hb har =>
    obtain ⟨hhd, -⟩ := List.cons.inj hes
    obtain ⟨t₀, e₀, rfl, rfl, rfl, rfl⟩ := lift_if hhd.symm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_inv_normal hc
    cases hk
    exact ⟨_, _, _, _, _, .cond hb, armOf_if' _ _ _ _, har⟩
  | blockEsc _ _ ho | loopEsc _ _ ho | ifEsc _ _ _ _ ho | tryEsc _ _ ho _ =>
    simp only [Prod.mk.injEq] at hr
    obtain ⟨-, -, rfl⟩ := hr
    exact absurd ho (by simp [POut.Escapes, Flow.Escapes])
  | ifAbort _ ho =>
    simp only [Prod.mk.injEq] at hr
    obtain ⟨-, -, rfl⟩ := hr
    exact absurd trivial ho
  | nil => simp at hes
  | blockBrk | loopBrk | ifBrk | tryBrk | tryCatch | tryRethrow => simp at hr
  | _ =>
    obtain ⟨hhd, -⟩ := List.cons.inj hes
    obtain ⟨-, -, hst⟩ := lift_op hhd.symm
    exact absurd ⟨_, _, _, _, hk⟩ hst

/-! ## Helpers -/

theorem div_nil {s : Store H} {f : Frame} {N : List Val} : ¬ EvalDivXP s f N ([] : List BExpr) := by
  intro h
  have := evalDivXP_iff_step.1 h
  cases this

theorem closed_nil {s s' : Store H} {f f' : Frame} {N N' : List Val}
    (h : EvalOXP closedCallXP s f N [] (s', f', .flow (.normal N'))) :
    s' = s ∧ f' = f ∧ N' = N := by
  obtain ⟨l, h, -⟩ := closed_logged h
  obtain ⟨h1, h2, h3, -⟩ := nil_inv_normal h
  exact ⟨h1, h2, h3⟩

theorem run_stepK {body : Expr} {st st' : MState H} {l : List (SCall H)} (h : MRunL body st l st')
    (hl : AllOk closedCallXP l) : Relation.ReflTransGen (StepK body) st st' := by
  induction h with
  | refl => exact .refl
  | step hs _ ih =>
    obtain ⟨h1, h2⟩ := allOk_append.1 hl
    exact .head ⟨_, hs, h1⟩ (ih h2)

/-- A strict run to a stop state, oracle-answered, is at least one oracle-answered step. -/
theorem mEnds_trans {body : Expr} {st st' : MState H} {l : List (SCall H)}
    (h : MEnds body (fun _ => False) (· = st') st l) (hl : AllOk closedCallXP l) :
    Relation.TransGen (StepK body) st st' := by
  obtain ⟨st₁, l₁, l₂, hr, rfl, ⟨st'', hs, rfl⟩ | ⟨_, hF, _⟩⟩ := h
  · obtain ⟨h1, h2⟩ := allOk_append.1 hl
    exact Relation.TransGen.tail' (run_stepK hr h1) ⟨_, hs, h2⟩
  · exact hF.elim

theorem gotoN_entry {body : Expr} {p : List SeqStep} {c : List Instr} {j : Nat} {sg : Segment}
    (hc : seqAt body p = some c) (hsg : (segment c)[j]? = some sg) (ls : List LFrame)
    (W : List Val) (s : Store H) (f : Frame) :
    gotoN (entry body p j) p.length ls W s f = some ⟨.block ⟨p, j⟩, W, ls, s, f⟩ := by
  have hl : lookup body ⟨p, j⟩ = some sg := by rw [lookup_eq]; simp [hc, hsg]
  simp [entry, hl, gotoN, depthT, popN]

theorem seg_of_div {c : List Instr} {j : Nat} {s : Store H} {f : Frame} {N : List Val}
    (h : EvalDivXP s f N (liftInstrs (restAt c j))) : ∃ sg, (segment c)[j]? = some sg := by
  cases hs : (segment c)[j]? with
  | none => rw [restAt_end hs] at h; exact (div_nil (by simpa [liftInstrs] using h)).elim
  | some sg => exact ⟨sg, rfl⟩

/-- A pending call reached after a normal prefix run. -/
theorem reach_prefix {s₀ s : Store H} {f₀ f : Frame} {N₀ N : List Val} {A B : List BExpr}
    {l₀ l : List (SCall H)} {z : (Abstract.wasmOShape H).self.Op}
    (hpre : EvalLXPS s₀ f₀ N₀ A l₀ (s, f, .flow (.normal N))) (hR : ReachLXPS s f N B l z) :
    ReachLXPS s₀ f₀ N₀ (A ++ B) (l₀ ++ l) z := by
  obtain ⟨f', hr⟩ := MachineLPend.reach_trap hR z.2.2
  have := (MachineLSeq.append hpre B).2 _ _ _ rfl _ _ hr
  exact MachineLPend.trap_reach this (l₀ ++ l) z z.2.2 (by simp)

/-! ## The invariants -/

/-- **At a block whose rest diverges**: the machine is at block `i` of the sequence at `p`, whose
instructions `pre` ran natively with oracle answers to `(s, f, N)`, from where the rest of the
sequence diverges natively. -/
def InvB (body : Expr) (st : MState H) : Prop :=
  ∃ (p : List SeqStep) (c : List Instr) (i : Nat) (sg : Segment) (pre post : List Instr)
    (ls : List LFrame) (s : Store H) (f : Frame) (N : List Val) (s₀ : Store H) (f₀ : Frame)
    (N₀ : List Val) (l₀ : List (SCall H)),
    st = ⟨.block ⟨p, i⟩, N₀.reverse, ls, s₀, f₀⟩ ∧ Pos body p c i sg pre post ∧
      FramesOk body p.reverse ls ∧ EvalLXPS s₀ f₀ N₀ (liftInstrs pre) l₀ (s, f, .flow (.normal N)) ∧
      AllOk closedCallXP l₀ ∧ EvalDivXP s f N (liftInstrs post ++ liftInstrs (restAt c (i + 1)))

/-- **At the entry of a loop's arm whose loop diverges**: the loop ending block `i` of the
sequence at `p` diverges natively from `(s, f, N)`, and the machine is at the entry of its
(nonempty) arm, as entering or re-entering the loop on `N` leaves it. -/
def InvA (body : Expr) (st : MState H) : Prop :=
  ∃ (p : List SeqStep) (c : List Instr) (i : Nat) (sg : Segment) (pre : List Instr) (t : Instr)
    (bt : BlockType) (tryT : Bool) (cs : List Catch) (c' : List Instr) (sg₀ : Segment)
    (ls : List LFrame) (s : Store H) (f : Frame) (N : List Val) (np nr : Nat),
    Pos body p c i sg pre [t] ∧ StructKind t bt true tryT cs ∧ armOf t 0 = some c' ∧
      (segment c')[0]? = some sg₀ ∧ FramesOk body p.reverse ls ∧ arity f bt = some (np, nr) ∧
      st = ⟨.block ⟨p ++ [(i, 0)], 0⟩, (N.take np).reverse,
        ⟨np, (N.drop np).reverse, true, tryT, cs, bt⟩ :: ls, s, f⟩ ∧
      EvalDivXP s f N (liftInstr t :: liftInstrs (restAt c (i + 1)))

/-- A block whose whole sequence rest diverges, nothing run yet. -/
theorem invB_at {body : Expr} {p : List SeqStep} {c : List Instr} {j : Nat} {sg : Segment}
    {ls : List LFrame} {s : Store H} {f : Frame} {N : List Val} (hc : seqAt body p = some c)
    (hsg : (segment c)[j]? = some sg) (hok : FramesOk body p.reverse ls)
    (hX : EvalDivXP s f N (liftInstrs (restAt c j))) :
    InvB body ⟨.block ⟨p, j⟩, N.reverse, ls, s, f⟩ := by
  refine ⟨p, c, j, sg, [], sg.instrs, ls, s, f, N, s, f, N, [], rfl,
    ⟨hc, hsg, rfl, (segment_isSegmentation c).2.2.2 sg (List.mem_of_getElem? hsg),
      fun _ _ _ => Nat.zero_le _⟩, hok, .nil, allOk_nil _, ?_⟩
  rwa [restAt_cons hsg, MachineLSeq.liftInstrs_append] at hX

/-- **Entering an arm that diverges**: one oracle-answered step. -/
theorem enter_inv {body : Expr} {p : List SeqStep} {c : List Instr} {i : Nat} {sg : Segment}
    {pre : List Instr} {t : Instr} {ls : List LFrame} {s s₀ : Store H} {f f₀ : Frame}
    {N N₀ : List Val} {l₀ : List (SCall H)} {a : Nat} {c' : List Instr} {V' : List Val}
    {np nr : Nat} {bt : BlockType} {loop tryT : Bool} {cs : List Catch}
    (hp : Pos body p c i sg pre [t]) (hok : FramesOk body p.reverse ls)
    (hpre : EvalLXPS s₀ f₀ N₀ (liftInstrs pre) l₀ (s, f, .flow (.normal N)))
    (hk : StructKind t bt loop tryT cs) (hsel : ArmSel t N a V')
    (harm : armOf t a = some c') (har : arity f bt = some (np, nr))
    (hX : EvalDivXP s f (V'.take np) (liftInstrs c')) :
    ∃ st', MStepL body ⟨.block ⟨p, i⟩, N₀.reverse, ls, s₀, f₀⟩ l₀ st' ∧ InvB body st' := by
  obtain ⟨ht, -, rfl⟩ := pos_term hp (isStruct_terminator ⟨_, _, _, _, hk⟩)
  have hb : lookup body ⟨p, i⟩ = some sg := by rw [lookup_eq]; simp [hp.hc, hp.hsg]
  have hcA : seqAt body (p ++ [(i, a)]) = some c' := by
    rw [Proofs.Machine.seqAt_append]; simp [hp.hc, hp.hsg, ht, harm]
  rw [← restAt_zero c'] at hX
  obtain ⟨sg₀, hsg₀⟩ := seg_of_div hX
  have hg := gotoN_entry hcA hsg₀
    (⟨if loop then np else nr, (V'.drop np).reverse, loop, tryT, cs, bt⟩ :: ls) (V'.take np).reverse
    s f
  refine ⟨_, MStepL.enter hb ht harm hk (by rw [List.reverse_reverse]; exact hpre) hsel har
    (by simpa using hg), ?_⟩
  exact invB_at hcA hsg₀ (by simpa using arm_ok hp hk harm hok _ _) hX

/-- **A pending internal call of a block**, reached after an oracle-answered prefix. -/
theorem reachL_at {body : Expr} {p : List SeqStep} {c : List Instr} {i : Nat} {sg : Segment}
    {pre post' : List Instr} {e : Instr} {ls : List LFrame} {s s₀ : Store H} {f f₀ : Frame}
    {N N₀ : List Val} {l₀ : List (SCall H)} {z : (Abstract.wasmOShape H).self.Op}
    (hp : Pos body p c i sg pre (e :: post')) (he : ¬ Instr.IsStruct e)
    (hpre : EvalLXPS s₀ f₀ N₀ (liftInstrs pre) l₀ (s, f, .flow (.normal N)))
    (hR : ∀ rest, ReachLXPS s f N (liftInstr e :: rest) [] z) :
    ReachL body ⟨.block ⟨p, i⟩, N₀.reverse, ls, s₀, f₀⟩ l₀ z := by
  have hb : lookup body ⟨p, i⟩ = some sg := by rw [lookup_eq]; simp [hp.hc, hp.hsg]
  by_cases hts : ∃ t, sg.term = some t ∧ Instr.IsStruct t
  · obtain ⟨t, ht, hst⟩ := hts
    obtain ⟨X, hX⟩ := pos_body_prefix hp he ht hst
    refine .body hb ?_
    rw [List.reverse_reverse, hX, MachineLSeq.liftInstrs_append]
    simpa [liftInstrs] using reach_prefix hpre (hR (liftInstrs X))
  · push Not at hts
    refine .run hb (fun t ht h => hts t ht h) ?_
    rw [List.reverse_reverse, codeOf_eq, hp.hinstrs, MachineLSeq.liftInstrs_append]
    simpa [liftInstrs] using reach_prefix hpre (hR (liftInstrs post'))

/-! ## Progress -/

/-- **Progress after an open prefix** `l₀`: a nonempty run from `st` whose log is `l₀` then
oracle-answered entries, to an invariant state; or a reached call, after `l₀` then oracle-answered
entries, whose callee diverges at the frame. -/
def ProgO (body : Expr) (st : MState H) (l₀ : List (SCall H)) : Prop :=
  (∃ (l₁ : List (SCall H)) (st₁ : MState H) (l₂ : List (SCall H)) (st' : MState H)
    (L : List (SCall H)), MStepL body st l₁ st₁ ∧ MRunL body st₁ l₂ st' ∧ l₁ ++ l₂ = l₀ ++ L ∧
      AllOk closedCallXP L ∧ (InvB body st' ∨ InvA body st')) ∨
  (∃ (L : List (SCall H)) (z : (Abstract.wasmOShape H).self.Op), ReachL body st (l₀ ++ L) z ∧
    AllOk closedCallXP L ∧ FunDivXP z.2.2 z.1 z.2.1)

theorem progO_append {body : Expr} {st : MState H} {l₀ l : List (SCall H)}
    (h : ProgO body st (l₀ ++ l)) (hl : AllOk closedCallXP l) : ProgO body st l₀ := by
  rcases h with ⟨l₁, st₁, l₂, st', L, hs, hr, heq, hL, hI⟩ | ⟨L, z, hR, hL, hY⟩
  · exact .inl ⟨l₁, st₁, l₂, st', l ++ L, hs, hr, by simp [heq], allOk_append.2 ⟨hl, hL⟩, hI⟩
  · exact .inr ⟨l ++ L, z, by simpa using hR, allOk_append.2 ⟨hl, hL⟩, hY⟩

/-- A strict run to a stop state is a first step, then a run. -/
theorem mEnds_run {body : Expr} {st st' : MState H} {l : List (SCall H)}
    (h : MEnds body (fun _ => False) (· = st') st l) :
    ∃ l₁ st₁ l₂, MStepL body st l₁ st₁ ∧ MRunL body st₁ l₂ st' ∧ l = l₁ ++ l₂ := by
  obtain ⟨st₀, l₁, l₂, hr, rfl, ⟨st'', hs, rfl⟩ | ⟨_, hF, _⟩⟩ := h
  · cases hr with
    | refl => exact ⟨l₂, st'', [], hs, .refl _, by simp⟩
    | step h₁ h₂ =>
      exact ⟨_, _, _, h₁, MachineLPend.mrun_snoc h₂ hs, by simp⟩
  · exact hF.elim

/-- With an oracle-answered prefix, progress is oracle-answered steps. -/
theorem progO_closed {body : Expr} {st : MState H} {l₀ : List (SCall H)} (h : ProgO body st l₀)
    (hl₀ : AllOk closedCallXP l₀) :
    (∃ st', Relation.TransGen (StepK body) st st' ∧ (InvB body st' ∨ InvA body st')) ∨
      CalleeDivK body st := by
  rcases h with ⟨l₁, st₁, l₂, st', L, hs, hr, heq, hL, hI⟩ | ⟨L, z, hR, hL, hY⟩
  · have hall : AllOk closedCallXP (l₁ ++ l₂) := by rw [heq]; exact allOk_append.2 ⟨hl₀, hL⟩
    obtain ⟨h₁, h₂⟩ := allOk_append.1 hall
    exact .inl ⟨st', Relation.TransGen.head' ⟨_, hs, h₁⟩ (run_stepK hr h₂), hI⟩
  · exact .inr ⟨st, _, z, .refl, hR, allOk_append.2 ⟨hl₀, hL⟩, hY⟩

/-- **From a block whose rest diverges**, the machine makes at least one oracle-answered step to
an invariant state, or reaches a diverging callee. -/
theorem progB {body : Expr} : ∀ (post : List Instr) {p : List SeqStep} {c : List Instr} {i : Nat}
    {sg : Segment} {pre : List Instr} {ls : List LFrame} {s : Store H} {f : Frame}
    {N : List Val} {s₀ : Store H} {f₀ : Frame} {N₀ : List Val} {l₀ : List (SCall H)},
    Pos body p c i sg pre post → FramesOk body p.reverse ls →
    EvalLXPS s₀ f₀ N₀ (liftInstrs pre) l₀ (s, f, .flow (.normal N)) →
    EvalDivXP s f N (liftInstrs post ++ liftInstrs (restAt c (i + 1))) →
    ProgO body ⟨.block ⟨p, i⟩, N₀.reverse, ls, s₀, f₀⟩ l₀
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, hp, _, _, _ => absurd rfl hp.hpost
  | e :: post', p, c, i, sg, pre, ls, s, f, N, s₀, f₀, N₀, l₀, hp, hok, hpre, hdiv => by
    have hd := evalDivXP_iff_step.1 hdiv
    generalize hes : liftInstrs (e :: post') ++ liftInstrs (restAt c (i + 1)) = es at hd
    simp only [liftInstrs, List.cons_append] at hes
    have hb : lookup body ⟨p, i⟩ = some sg := by rw [lookup_eq]; simp [hp.hc, hp.hsg]
    cases hd with
    | args h =>
      obtain ⟨hhd, -⟩ := List.cons.inj hes
      obtain ⟨-, rfl, -⟩ := lift_op hhd
      exact (div_nil h).elim
    | @cont _ s₂ _ f₂ _ N₂ _ _ hd' hX =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj hes
      obtain ⟨l_e, hle, hlok⟩ := closed_logged hd'
      by_cases hse : Instr.IsStruct e
      · obtain ⟨ht, rfl, rfl⟩ := pos_term hp (isStruct_terminator hse)
        simp only [liftInstrs, List.nil_append] at hX
        obtain ⟨sg', hsg'⟩ := seg_of_div hX
        have hg := gotoN_entry hp.hc hsg' ls N₂.reverse s₂ f₂
        obtain ⟨bt, loop, tryT, cs, hk⟩ := hse
        obtain ⟨a, c', V', np, nr, hsel, harm, har⟩ := struct_sel hle rfl rfl hk
        have hA := struct_run (Fin := fun _ => False)
          (Z := (· = ⟨.block ⟨p, i + 1⟩, N₂.reverse, ls, s₂, f₂⟩)) (l' := []) hle
          ⟨_, _, _, _, hk⟩ rfl rfl hp hok ⟨_, hg, .inr ⟨rfl, rfl⟩⟩ a c' V' np nr bt loop tryT cs hk
          hsel harm har
        have hE := blk_enter hp hk hsel harm har hA s₀ f₀ N₀ l₀ hpre
        obtain ⟨l₁, st₁, l₂, hs, hr, heq⟩ := mEnds_run hE
        exact .inl ⟨l₁, st₁, l₂, _, l_e, hs, hr, by rw [← heq]; simp, hlok,
          .inl (invB_at hp.hc hsg' hok hX)⟩
      · cases post' with
        | nil =>
          have ht := pos_last_nonstruct hp hse
          simp only [liftInstrs, List.nil_append] at hX
          obtain ⟨sg', hsg'⟩ := seg_of_div hX
          have hr : EvalLXPS s₀ f₀ (N₀.reverse).reverse (liftInstrs (MachineL.codeOf sg)) (l₀ ++ l_e)
              (s₂, f₂, .flow (.normal N₂)) := by
            rw [List.reverse_reverse, codeOf_eq, hp.hinstrs, MachineLSeq.liftInstrs_append]
            exact (MachineLSeq.append hpre _).2 _ _ _ rfl _ _ (by simpa [liftInstrs] using hle)
          exact .inl ⟨_, _, [], _, l_e, MStepL.run hb ht hr
            (.next (by simpa using gotoN_entry hp.hc hsg' ls N₂.reverse s₂ f₂)), .refl _, by simp,
            hlok, .inl (invB_at hp.hc hsg' hok hX)⟩
        | cons e' post'' =>
          have hpre' : EvalLXPS s₀ f₀ N₀ (liftInstrs (pre ++ [e])) (l₀ ++ l_e)
              (s₂, f₂, .flow (.normal N₂)) := by
            rw [MachineLSeq.liftInstrs_append]
            exact (MachineLSeq.append hpre _).2 _ _ _ rfl _ _ (by simpa [liftInstrs] using hle)
          exact progO_append (progB (e' :: post'') (pos_next hp hse) hok hpre' hX) hlok
    | callee hargs hfi hty hY =>
      obtain ⟨hhd, -⟩ := List.cons.inj hes
      obtain ⟨rfl, rfl, hse⟩ := lift_op hhd
      obtain ⟨rfl, rfl, rfl⟩ := closed_nil hargs
      exact .inr ⟨[], _, by simpa using reachL_at hp hse hpre (fun _ => .call .nil hfi hty),
        allOk_nil _, hY⟩
    | callIndCallee hargs hres hfi hty hy hY =>
      obtain ⟨hhd, -⟩ := List.cons.inj hes
      obtain ⟨rfl, rfl, hse⟩ := lift_op hhd
      obtain ⟨rfl, rfl, hN⟩ := closed_nil hargs
      subst hN
      exact .inr ⟨[], _, by simpa using reachL_at hp hse hpre (fun _ => .ind .nil hres hfi hty hy),
        allOk_nil _, hY⟩
    | callRefCallee hargs hfi hty hy hY =>
      obtain ⟨hhd, -⟩ := List.cons.inj hes
      obtain ⟨rfl, rfl, hse⟩ := lift_op hhd
      obtain ⟨rfl, rfl, hN⟩ := closed_nil hargs
      subst hN
      exact .inr ⟨[], _, by simpa using reachL_at hp hse hpre (fun _ => .ref .nil hfi hty hy),
        allOk_nil _, hY⟩
    | block har hX =>
      obtain ⟨hhd, -⟩ := List.cons.inj hes
      obtain ⟨b₀, rfl, rfl⟩ := lift_block hhd
      obtain ⟨-, rfl, -⟩ := pos_term hp rfl
      obtain ⟨st', hs, hI⟩ := enter_inv hp hok hpre .block (.plain (fun _ _ _ => nofun)) rfl
        har hX
      exact .inl ⟨l₀, st', [], st', [], hs, .refl _, by simp, allOk_nil _, .inl hI⟩
    | loop har hX =>
      obtain ⟨hhd, -⟩ := List.cons.inj hes
      obtain ⟨b₀, rfl, rfl⟩ := lift_loop hhd
      obtain ⟨-, rfl, -⟩ := pos_term hp rfl
      obtain ⟨st', hs, hI⟩ := enter_inv hp hok hpre .loop (.plain (fun _ _ _ => nofun)) rfl
        har hX
      exact .inl ⟨l₀, st', [], st', [], hs, .refl _, by simp, allOk_nil _, .inl hI⟩
    | @loopBack _ s₁ _ f₁ _ vs bt _ _ np nr har hbody hX =>
      obtain ⟨hhd, htl⟩ := List.cons.inj hes
      obtain ⟨b₀, rfl, rfl⟩ := lift_loop hhd
      obtain ⟨ht, rfl, rfl⟩ := pos_term hp rfl
      subst htl
      obtain ⟨l_b, hlb, hlbok⟩ := closed_logged hbody
      have hcA : seqAt body (p ++ [(i, 0)]) = some b₀ := by
        rw [Proofs.Machine.seqAt_append]; simp [hp.hc, hp.hsg, ht, armOf]
      obtain ⟨sg₀, hsg₀⟩ : ∃ sg₀, (segment b₀)[0]? = some sg₀ := by
        cases hs : (segment b₀)[0]? with
        | none =>
          rw [← restAt_zero b₀, restAt_end hs] at hlb
          obtain ⟨-, -, h3, -⟩ := nil_inv hlb
          cases h3
        | some sg₀ => exact ⟨sg₀, rfl⟩
      have hokA := arm_ok (a := 0) hp .loop rfl hok
      have har₁ := (arity_congr (MachineLSeq.module_eq hlb) _).trans har
      set N' := vs.take np ++ N.drop np with hN'
      have hg₂ := gotoN_entry hcA hsg₀ (⟨np, (N'.drop np).reverse, true, false, [], bt⟩ :: ls)
        (N'.take np).reverse s₁ f₁
      have hA := arm_entry (Fin := fun _ => False)
        (Z := (· = ⟨.block ⟨p ++ [(i, 0)], 0⟩, (N'.take np).reverse,
          ⟨np, (N'.drop np).reverse, true, false, [], bt⟩ :: ls, s₁, f₁⟩)) (l₂ := []) (nr := nr)
        hp .loop rfl hok hlb (mot hlb)
        (exit_loopBack (hokA _ _) rfl har₁ ⟨_, by simpa [hN'] using hg₂, .inr ⟨rfl, rfl⟩⟩)
      have hE := blk_enter hp .loop (.plain (fun _ _ _ => nofun)) rfl har hA s₀ f₀ N₀ l₀ hpre
      obtain ⟨l₁, st₁, l₂, hs, hr, heq⟩ := mEnds_run hE
      refine .inl ⟨l₁, st₁, l₂, _, l_b, hs, hr, by rw [← heq]; simp, hlbok, .inr ?_⟩
      exact ⟨p, c, i, sg, sg.body, _, bt, false, [], b₀, sg₀, ls, s₁, f₁, N', np, nr, hp, .loop, rfl,
        hsg₀, hok, har₁, rfl, by simpa [liftInstrs, liftInstr] using hX⟩
    | cond hX =>
      obtain ⟨hhd, -⟩ := List.cons.inj hes
      obtain ⟨t₀, e₀, rfl, rfl, -, -⟩ := lift_if hhd
      exact (div_nil hX).elim
    | arm hc hb har hX =>
      obtain ⟨hhd, -⟩ := List.cons.inj hes
      obtain ⟨t₀, e₀, rfl, rfl, rfl, rfl⟩ := lift_if hhd
      obtain ⟨rfl, rfl, rfl⟩ := closed_nil hc
      obtain ⟨-, rfl, -⟩ := pos_term hp rfl
      rw [liftInstrs_ite] at hX
      obtain ⟨st', hs, hI⟩ := enter_inv hp hok hpre .if_ (.cond hb) (armOf_if' _ _ _ _) har hX
      exact .inl ⟨l₀, st', [], st', [], hs, .refl _, by simp, allOk_nil _, .inl hI⟩
    | try_ har hX =>
      obtain ⟨hhd, -⟩ := List.cons.inj hes
      obtain ⟨b₀, rfl, rfl⟩ := lift_try hhd
      obtain ⟨-, rfl, -⟩ := pos_term hp rfl
      obtain ⟨st', hs, hI⟩ := enter_inv hp hok hpre .tryTable (.plain (fun _ _ _ => nofun))
        rfl har hX
      exact .inl ⟨l₀, st', [], st', [], hs, .refl _, by simp, allOk_nil _, .inl hI⟩

/-- **From the entry of a diverging loop's arm**: the arm's own block diverges there, or the
machine makes at least one oracle-answered step to an invariant state, or reaches a diverging
callee. -/
theorem progA {body : Expr} {st : MState H} (h : InvA body st) :
    InvB body st ∨ (∃ st', Relation.TransGen (StepK body) st st' ∧
      (InvB body st' ∨ InvA body st')) ∨ CalleeDivK body st := by
  obtain ⟨p, c, i, sg, pre, t, bt, tryT, cs, c', sg₀, ls, s, f, N, np, nr, hp, hk, harm, hsg₀, hok,
    har, rfl, hdiv⟩ := h
  cases hk
  rename_i b₀
  simp only [armOf, Option.some.injEq] at harm; subst harm
  obtain ⟨ht, -, rfl⟩ := pos_term hp rfl
  have hcA : seqAt body (p ++ [(i, 0)]) = some b₀ := by
    rw [Proofs.Machine.seqAt_append]; simp [hp.hc, hp.hsg, ht, armOf]
  have hokA := arm_ok (a := 0) hp .loop rfl hok
  have hd := evalDivXP_iff_step.1 hdiv
  generalize hes : liftInstr (.loop bt b₀) :: liftInstrs (restAt c (i + 1)) = es at hd
  simp only [liftInstr] at hes
  cases hd with
  | @cont _ s₂ _ f₂ _ N₂ _ _ hd' hX =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hes
    obtain ⟨l_e, hle, hlok⟩ := closed_logged hd'
    obtain ⟨sg', hsg'⟩ := seg_of_div hX
    have hg := gotoN_entry hp.hc hsg' ls N₂.reverse s₂ f₂
    have hA := struct_run (Fin := fun _ => False)
      (Z := (· = ⟨.block ⟨p, i + 1⟩, N₂.reverse, ls, s₂, f₂⟩)) (l' := []) hle
      ⟨_, _, _, _, .loop⟩ (by simp [liftInstr]) rfl hp hok ⟨_, hg, .inr ⟨rfl, rfl⟩⟩ 0 b₀ N np nr bt
      true false [] .loop (.plain (fun _ _ _ => nofun)) rfl har
    obtain ⟨st₁, hg₁, hE⟩ := hA
    have h2 := gotoN_entry hcA hsg₀
      (⟨if (true = true) then np else nr, (N.drop np).reverse, true, false, [], bt⟩ :: ls) (N.take np).reverse s f
    rw [List.length_append, List.length_singleton] at h2
    rw [h2] at hg₁
    simp only [Option.some.injEq] at hg₁; subst hg₁
    rcases hE with hE | ⟨hZ, -⟩
    · exact .inr (.inl ⟨_, mEnds_trans hE (by simpa using hlok), .inl (invB_at hp.hc hsg' hok hX)⟩)
    · simp only [MState.mk.injEq, Target.block.injEq, BlockId.mk.injEq] at hZ
      have := congrArg List.length hZ.1.1
      simp at this
  | loop har' hX =>
    obtain ⟨hhd, -⟩ := List.cons.inj hes
    simp only [BExpr.loop.injEq] at hhd; obtain ⟨rfl, rfl⟩ := hhd
    rw [har] at har'; simp only [Option.some.injEq, Prod.mk.injEq] at har'
    obtain ⟨rfl, rfl⟩ := har'
    rw [← restAt_zero b₀] at hX
    exact .inl (by simpa using invB_at hcA hsg₀ (by simpa using hokA np (N.drop np).reverse) hX)
  | @loopBack _ s₁ _ f₁ _ vs _ _ _ np' nr' har' hbody hX =>
    obtain ⟨hhd, htl⟩ := List.cons.inj hes
    simp only [BExpr.loop.injEq] at hhd; obtain ⟨rfl, rfl⟩ := hhd
    rw [har] at har'; simp only [Option.some.injEq, Prod.mk.injEq] at har'
    obtain ⟨rfl, rfl⟩ := har'
    subst htl
    obtain ⟨l_b, hlb, hlbok⟩ := closed_logged hbody
    have har₁ := (arity_congr (MachineLSeq.module_eq hlb) _).trans har
    set N' := vs.take np ++ N.drop np with hN'
    have hg₂ := gotoN_entry hcA hsg₀ (⟨np, (N'.drop np).reverse, true, false, [], bt⟩ :: ls)
      (N'.take np).reverse s₁ f₁
    have hx := exit_loopBack (Fin := fun _ => False)
      (Z := (· = ⟨.block ⟨p ++ [(i, 0)], 0⟩, (N'.take np).reverse,
        ⟨np, (N'.drop np).reverse, true, false, [], bt⟩ :: ls, s₁, f₁⟩)) (l' := [])
      (hokA np (N.drop np).reverse) rfl har₁ ⟨_, by simpa [hN'] using hg₂, .inr ⟨rfl, rfl⟩⟩
    have hpos : Pos body (p ++ [(i, 0)]) b₀ 0 sg₀ [] sg₀.instrs :=
      ⟨hcA, hsg₀, rfl, (segment_isSegmentation b₀).2.2.2 sg₀ (List.mem_of_getElem? hsg₀),
        fun _ _ _ => Nat.zero_le _⟩
    have hE := (mot hlb (p ++ [(i, 0)]) b₀ 0 sg₀ [] sg₀.instrs _ [] hpos
      (by rw [← MachineLSeq.liftInstrs_append, ← restAt_cons hsg₀, restAt_zero])
      (by simpa using hokA np (N.drop np).reverse) hx).1 s f (N.take np) [] .nil
    refine .inr (.inl ⟨_, mEnds_trans hE (by simpa using hlbok), .inr ?_⟩)
    exact ⟨p, c, i, sg, sg.body, _, bt, false, [], b₀, sg₀, ls, s₁, f₁, N', np, nr, hp, .loop, rfl,
      hsg₀, hok, har₁, rfl, by simpa [liftInstr] using hX⟩
  | _ => simp at hes

/-- **Progress**: from either invariant, at least one oracle-answered step to either, or a
diverging callee. -/
theorem prog {body : Expr} {st : MState H} (h : InvB body st ∨ InvA body st) :
    (∃ st', Relation.TransGen (StepK body) st st' ∧ (InvB body st' ∨ InvA body st')) ∨
      CalleeDivK body st := by
  have hB : InvB body st → (∃ st', Relation.TransGen (StepK body) st st' ∧
      (InvB body st' ∨ InvA body st')) ∨ CalleeDivK body st := by
    rintro ⟨p, c, i, sg, pre, post, ls, s, f, N, s₀, f₀, N₀, l₀, rfl, hp, hok, hpre, hl₀, hdiv⟩
    exact progO_closed (progB post hp hok hpre hdiv) hl₀
  rcases h with h | h
  · exact hB h
  · rcases progA h with h' | h' | h'
    · exact hB h'
    · exact .inl h'
    · exact .inr h'

/-! ## Infinite runs -/

/-- **An infinite run from a step-closed predicate.** -/
theorem infK_of {body : Expr} (Q : MState H → Prop) {st : MState H} (h0 : Q st)
    (hs : ∀ x, Q x → ∃ y, StepK body x y ∧ Q y) : InfK body st := by
  let next : {x // Q x} → {x // Q x} := fun x => ⟨Classical.choose (hs x.1 x.2),
    (Classical.choose_spec (hs x.1 x.2)).2⟩
  let g : ℕ → {x // Q x} := fun n => Nat.rec ⟨st, h0⟩ (fun _ x => next x) n
  exact ⟨fun n => (g n).1, rfl, fun n => (Classical.choose_spec (hs (g n).1 (g n).2)).1⟩

theorem calleeDivK_head {body : Expr} {st st' : MState H}
    (h : Relation.ReflTransGen (StepK body) st st') (hC : CalleeDivK body st') :
    CalleeDivK body st := by
  obtain ⟨st₁, l, z, hr, hR, hl, hY⟩ := hC
  exact ⟨st₁, l, z, h.trans hr, hR, hl, hY⟩

/-- **From an invariant state, the machine diverges.** -/
theorem mdiv_of_inv {body : Expr} {st : MState H} (h : InvB body st ∨ InvA body st) :
    MDivL body st := by
  by_cases hC : CalleeDivK body st
  · exact .inr hC
  refine .inl (infK_of (fun x => Relation.ReflTransGen (StepK body) st x ∧
    ∃ y, Relation.ReflTransGen (StepK body) x y ∧ (InvB body y ∨ InvA body y))
    ⟨.refl, st, .refl, h⟩ ?_)
  rintro x ⟨hsx, y, hxy, hy⟩
  rcases Relation.ReflTransGen.cases_head hxy with rfl | ⟨x₁, hx₁, hx₁y⟩
  · rcases prog hy with ⟨z, hz, hIz⟩ | hCx
    · obtain ⟨x₁, hx₁, hx₁z⟩ := Relation.TransGen.head'_iff.mp hz
      exact ⟨x₁, hx₁, hsx.tail hx₁, z, hx₁z, hIz⟩
    · exact (hC (calleeDivK_head hsx hCx)).elim
  · exact ⟨x₁, hx₁, hsx.tail hx₁, y, hx₁y, hy⟩

/-- **Native host-free divergence of a body is machine divergence** from the CFG entry. -/
theorem div_machine {body : Expr} {s : Store H} {f : Frame}
    (h : EvalDivXP s f [] (liftInstrs body)) : MDivL body (initial body s f) := by
  rw [← restAt_zero body] at h
  obtain ⟨sg, hsg⟩ := seg_of_div h
  have hg := gotoN_entry (body := body) (p := []) rfl hsg [] [] s f
  rw [initial_eq] at hg
  simp only [Option.some.injEq] at hg
  rw [hg]
  exact mdiv_of_inv (.inl (invB_at rfl hsg (by simp [FramesOk]) h))

end Silmaril.Wasm.Cfg.Proofs.MachineLDivB
