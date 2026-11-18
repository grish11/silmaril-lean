module

public import Silmaril.Proofs.Wasm.Cfg.MachineLDivI
public import Silmaril.Wasm.Abstract.HostClosingInfXP.Defs
public import Silmaril.Wasm.Abstract.HostClosingS.Thms

@[expose] public section

/-!
# Divergence after a log, natively and on the machine (H2, proofs)

`logDiv_machine`: divergence after a log of the canonical logged semantics (`LogDivXP`, an
`EvalLXPh` prefix, then host-free divergence) is the machine's divergence after the same log
(`MLogDivL`, the calls as session calls `OCall.toS`). By induction on `LogDivXP` with a position
motive as the converse's (`MachineLBwd.Mot`): a block clause, from the block with the instructions
before the position run natively, and an arm clause, at a loop's arm entry.
-/

namespace Silmaril.Wasm.Cfg.Proofs.MachineLLogDiv

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Abstract (EvalLXPS EvalLXPh SCall OCall LogDivXP)
open Silmaril.Wasm.Abstract.CallXP (POut EvalOXP)
open Silmaril.Wasm.Abstract.XRecursionP (closedCallXP)
open Silmaril.Wasm.Abstract.XDivergeP (EvalDivXP FunDivXP)
open Silmaril.Wasm.Abstract (evalLXPh_session)
open Silmaril.Wasm.Cfg.Proofs.Machine (restAt_cons restAt_end restAt_zero seg_of_lookup lookup_eq)
open Silmaril.Wasm.Cfg.Proofs.MachineLFwd
open Silmaril.Wasm.Cfg.Proofs.MachineLBwd
open Silmaril.Wasm.Cfg.Proofs.MachineLDivB
open Silmaril.Wasm.Cfg.Proofs.MachineLClosed (AllOk allOk_append allOk_nil allOk_cons)

variable {H : Type}

/-! ## The machine side -/

theorem mdiv_step {body : Expr} {st st' : MState H} (hs : StepK body st st')
    (h : MDivL body st') : MDivL body st := by
  rcases h with ⟨g, hg0, hg⟩ | ⟨st₁, l, z, hr, hR, hl, hY⟩
  · refine .inl ⟨fun n => Nat.rec st (fun k _ => g k) n, rfl, fun n => ?_⟩
    cases n with
    | zero => simpa [hg0] using hs
    | succ n => exact hg n
  · exact .inr ⟨st₁, l, z, .head hs hr, hR, hl, hY⟩

theorem mdiv_run {body : Expr} {st st' : MState H} {l : List (SCall H)} (h : MRunL body st l st')
    (hl : AllOk closedCallXP l) (hd : MDivL body st') : MDivL body st := by
  induction h with
  | refl => exact hd
  | step hs _ ih =>
    obtain ⟨h₁, h₂⟩ := allOk_append.1 hl
    exact mdiv_step ⟨_, hs, h₁⟩ (ih h₂ hd)

/-- **Divergence is divergence after the empty log.** -/
theorem mlog_of_mdiv {body : Expr} {st : MState H} (h : MDivL body st) : MLogDivL body st [] := by
  rcases h with ⟨g, hg0, hg⟩ | ⟨st₁, l, z, hr, hR, hl, hY⟩
  · obtain ⟨l, hs, hl⟩ := hg 0
    rw [hg0] at hs
    refine ⟨st, [], [], l, .refl _, rfl, hl, .inl ⟨g 1, by simpa using hs, ?_⟩⟩
    exact .inl ⟨fun n => g (n + 1), rfl, fun n => hg (n + 1)⟩
  · rcases Relation.ReflTransGen.cases_head hr with rfl | ⟨x, ⟨l', hs, hl'⟩, hx⟩
    · exact ⟨st, [], [], l, .refl _, rfl, hl, .inr ⟨z, by simpa using hR, hY⟩⟩
    · exact ⟨st, [], [], l', .refl _, rfl, hl', .inl ⟨x, by simpa using hs,
        .inr ⟨st₁, l, z, hx, hR, hl, hY⟩⟩⟩

theorem mlog_step {body : Expr} {st st' : MState H} {l L : List (SCall H)}
    (hs : MStepL body st l st') (h : MLogDivL body st' L) : MLogDivL body st (l ++ L) := by
  obtain ⟨st₁, l₁, l₂, l₃, hr, rfl, hl₃, hend⟩ := h
  exact ⟨st₁, l ++ l₁, l₂, l₃, .step hs hr, by simp, hl₃, hend⟩

theorem mlog_run {body : Expr} {st st' : MState H} {l L : List (SCall H)}
    (hr : MRunL body st l st') (h : MLogDivL body st' L) : MLogDivL body st (l ++ L) := by
  induction hr with
  | refl => simpa using h
  | step hs _ ih => simpa [List.append_assoc] using mlog_step hs (ih h)

/-- **A run whose log is `A` then oracle answers, into divergence**, is divergence after `A`. -/
theorem mlog_of_run {body : Expr} {st st' : MState H} {L : List (SCall H)}
    (hr : MRunL body st L st') :
    ∀ {A B : List (SCall H)}, L = A ++ B → AllOk closedCallXP B → MDivL body st' →
      MLogDivL body st A := by
  induction hr with
  | refl =>
    intro A B hAB _ hd
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hAB.symm
    exact mlog_of_mdiv hd
  | @step st st₁ st₂ l₁ l₂ hs hr' ih =>
    intro A B hAB hB hd
    rcases List.append_eq_append_iff.mp hAB with ⟨A', rfl, hA'⟩ | ⟨C, rfl, hC⟩
    · exact mlog_step hs (ih hA' hB hd)
    · subst hC
      obtain ⟨hC, hl₂⟩ := allOk_append.1 hB
      exact ⟨st, [], A, C, .refl _, rfl, hC, .inl ⟨st₁, hs, mdiv_run hr' hl₂ hd⟩⟩

/-- **Progress after an open prefix is divergence after it.** -/
theorem mlog_of_progO {body : Expr} {st : MState H} {l₀ : List (SCall H)} (h : ProgO body st l₀) :
    MLogDivL body st l₀ := by
  rcases h with ⟨l₁, st₁, l₂, st', L, hs, hr, heq, hL, hI⟩ | ⟨L, z, hR, hL, hY⟩
  · exact mlog_of_run (.step hs hr) heq hL (mdiv_of_inv hI)
  · exact ⟨st, [], l₀, L, .refl _, rfl, hL, .inr ⟨z, hR, hY⟩⟩

/-! ## The native side -/

theorem ne_trap_of_blockVals {fl : Flow} {vs : List Val} (hvs : fl.blockVals = some vs) :
    POut.flow fl ≠ .flow .trap := by
  rintro ⟨⟩
  simp [Flow.blockVals] at hvs

theorem logDiv_nil {s : Store H} {f : Frame} {N : List Val} {L : List (OCall H)}
    (h : LogDivXP s f N [] L) : False := by
  cases h with
  | div hd => exact div_nil hd

theorem logDiv_ne {s : Store H} {f : Frame} {N : List Val} {c : List Instr} {j : Nat}
    {L : List (OCall H)} (h : LogDivXP s f N (liftInstrs (restAt c j)) L) :
    ∃ sg, (segment c)[j]? = some sg := by
  cases hs : (segment c)[j]? with
  | none => rw [restAt_end hs] at h; exact (logDiv_nil (by simpa [liftInstrs] using h)).elim
  | some sg => exact ⟨sg, rfl⟩

theorem lxph_nil {s s' : Store H} {f f' : Frame} {N N' : List Val} {l : List (OCall H)}
    (h : EvalLXPh s f N [] l (s', f', .flow (.normal N'))) : s = s' ∧ f = f' ∧ N = N' ∧ l = [] := by
  have := nil_inv_normal (evalLXPh_session h (by simp))
  obtain ⟨h1, h2, h3, h4⟩ := this
  exact ⟨h1.symm, h2.symm, h3.symm, by simpa using h4⟩

/-! ## Positions -/

/-- **Entering a nonempty arm** from the block, its segment body run natively. -/
theorem enter_at {body : Expr} {p : List SeqStep} {c : List Instr} {i : Nat} {sg : Segment}
    {pre : List Instr} {t : Instr} {ls : List LFrame} {s s₀ : Store H} {f f₀ : Frame}
    {N N₀ : List Val} {l₀ : List (SCall H)} {a : Nat} {c' : List Instr} {V' : List Val}
    {np nr : Nat} {bt : BlockType} {loop tryT : Bool} {cs : List Catch} {sg₀ : Segment}
    (hp : Pos body p c i sg pre [t]) (hok : FramesOk body p.reverse ls)
    (hpre : EvalLXPS s₀ f₀ N₀ (liftInstrs pre) l₀ (s, f, .flow (.normal N)))
    (hk : StructKind t bt loop tryT cs) (hsel : ArmSel t N a V') (harm : armOf t a = some c')
    (har : arity f bt = some (np, nr)) (hsg₀ : (segment c')[0]? = some sg₀) :
    seqAt body (p ++ [(i, a)]) = some c' ∧
      FramesOk body (p ++ [(i, a)]).reverse
        (⟨if loop then np else nr, (V'.drop np).reverse, loop, tryT, cs, bt⟩ :: ls) ∧
      MStepL body ⟨.block ⟨p, i⟩, N₀.reverse, ls, s₀, f₀⟩ l₀
        ⟨.block ⟨p ++ [(i, a)], 0⟩, (V'.take np).reverse,
          ⟨if loop then np else nr, (V'.drop np).reverse, loop, tryT, cs, bt⟩ :: ls, s, f⟩ := by
  obtain ⟨ht, -, rfl⟩ := pos_term hp (isStruct_terminator ⟨_, _, _, _, hk⟩)
  have hb : lookup body ⟨p, i⟩ = some sg := by rw [lookup_eq]; simp [hp.hc, hp.hsg]
  have hcA : seqAt body (p ++ [(i, a)]) = some c' := by
    rw [Proofs.Machine.seqAt_append]; simp [hp.hc, hp.hsg, ht, harm]
  have hg := gotoN_entry hcA hsg₀
    (⟨if loop then np else nr, (V'.drop np).reverse, loop, tryT, cs, bt⟩ :: ls) (V'.take np).reverse
    s f
  exact ⟨hcA, by simpa using arm_ok hp hk harm hok _ _,
    MStepL.enter hb ht harm hk (by rw [List.reverse_reverse]; exact hpre) hsel har (by simpa using hg)⟩

/-- **A structured instruction run natively to a normal end**, from its block to the next. -/
theorem struct_target {body : Expr} {p : List SeqStep} {c : List Instr} {i : Nat} {sg sg' : Segment}
    {pre : List Instr} {t : Instr} {ls : List LFrame} {s s₀ s₂ : Store H} {f f₀ f₂ : Frame}
    {N N₀ N₂ : List Val} {l₀ l_t : List (SCall H)} (hp : Pos body p c i sg pre [t])
    (hst : Instr.IsStruct t) (hok : FramesOk body p.reverse ls)
    (hpre : EvalLXPS s₀ f₀ N₀ (liftInstrs pre) l₀ (s, f, .flow (.normal N)))
    (hrun : EvalLXPS s f N [liftInstr t] l_t (s₂, f₂, .flow (.normal N₂)))
    (hsg' : (segment c)[i + 1]? = some sg') :
    MRunL body ⟨.block ⟨p, i⟩, N₀.reverse, ls, s₀, f₀⟩ (l₀ ++ l_t)
      ⟨.block ⟨p, i + 1⟩, N₂.reverse, ls, s₂, f₂⟩ := by
  have hg := gotoN_entry hp.hc hsg' ls N₂.reverse s₂ f₂
  obtain ⟨bt, loop, tryT, cs, hk⟩ := hst
  obtain ⟨a, c', V', np, nr, hsel, harm, har⟩ := struct_sel hrun rfl rfl hk
  have hA := struct_run (Fin := fun _ => False)
    (Z := (· = ⟨.block ⟨p, i + 1⟩, N₂.reverse, ls, s₂, f₂⟩)) (l' := []) hrun
    ⟨_, _, _, _, hk⟩ rfl rfl hp hok ⟨_, hg, .inr ⟨rfl, rfl⟩⟩ a c' V' np nr bt loop tryT cs hk
    hsel harm har
  have hE := blk_enter hp hk hsel harm har hA s₀ f₀ N₀ l₀ hpre
  obtain ⟨l₁, st₁, l₂, hs, hr, heq⟩ := mEnds_run hE
  rw [show l₀ ++ l_t = l₁ ++ l₂ by rw [← heq]; simp]
  exact .step hs hr

/-- **A loop run natively to a normal end**, from the entry of its arm to the next block. -/
theorem struct_target_arm {body : Expr} {p : List SeqStep} {c : List Instr} {i : Nat}
    {sg sg' sg₀ : Segment} {pre : List Instr} {bt : BlockType} {b₀ : List Instr}
    {ls : List LFrame} {s s₂ : Store H} {f f₂ : Frame} {N N₂ : List Val} {l_t : List (SCall H)}
    {np nr : Nat} (hp : Pos body p c i sg pre [.loop bt b₀]) (hok : FramesOk body p.reverse ls)
    (har : arity f bt = some (np, nr)) (hsg₀ : (segment b₀)[0]? = some sg₀)
    (hrun : EvalLXPS s f N [liftInstr (.loop bt b₀)] l_t (s₂, f₂, .flow (.normal N₂)))
    (hsg' : (segment c)[i + 1]? = some sg') :
    MRunL body ⟨.block ⟨p ++ [(i, 0)], 0⟩, (N.take np).reverse,
        ⟨np, (N.drop np).reverse, true, false, [], bt⟩ :: ls, s, f⟩ l_t
      ⟨.block ⟨p, i + 1⟩, N₂.reverse, ls, s₂, f₂⟩ := by
  obtain ⟨ht, -, -⟩ := pos_term hp rfl
  have hcA : seqAt body (p ++ [(i, 0)]) = some b₀ := by
    rw [Proofs.Machine.seqAt_append]; simp [hp.hc, hp.hsg, ht, armOf]
  have hg := gotoN_entry hp.hc hsg' ls N₂.reverse s₂ f₂
  obtain ⟨st₁, hg₁, hE⟩ := struct_run (Fin := fun _ => False)
    (Z := (· = ⟨.block ⟨p, i + 1⟩, N₂.reverse, ls, s₂, f₂⟩)) (l' := []) hrun
    ⟨_, _, _, _, .loop⟩ rfl rfl hp hok ⟨_, hg, .inr ⟨rfl, rfl⟩⟩ 0 b₀ N np nr bt true false []
    .loop (.plain (fun _ _ _ => nofun)) rfl har
  have h2 := gotoN_entry hcA hsg₀
    (⟨if (true = true) then np else nr, (N.drop np).reverse, true, false, [], bt⟩ :: ls)
    (N.take np).reverse s f
  rw [List.length_append, List.length_singleton] at h2
  rw [h2] at hg₁
  simp only [Option.some.injEq] at hg₁; subst hg₁
  rcases hE with hE | ⟨hZ, -⟩
  · obtain ⟨l₁, st₂, l₂, hs, hr, heq⟩ := mEnds_run hE
    rw [show l_t = l₁ ++ l₂ by rw [← heq]; simp]
    simpa using MRunL.step hs hr
  · simp only [MState.mk.injEq, Target.block.injEq, BlockId.mk.injEq] at hZ
    have := congrArg List.length hZ.1.1
    simp at this

/-- **A loop iteration branching back**, from the loop's block to the arm's re-entry. -/
theorem loopBack_target {body : Expr} {p : List SeqStep} {c : List Instr} {i : Nat}
    {sg sg₀ : Segment} {bt : BlockType} {b₀ : List Instr} {ls : List LFrame}
    {s s₀ s₁ : Store H} {f f₀ f₁ : Frame} {N N₀ vs : List Val} {l₀ l_b : List (SCall H)}
    {np nr : Nat} (hp : Pos body p c i sg sg.body [.loop bt b₀]) (hok : FramesOk body p.reverse ls)
    (hpre : EvalLXPS s₀ f₀ N₀ (liftInstrs sg.body) l₀ (s, f, .flow (.normal N)))
    (har : arity f bt = some (np, nr)) (hsg₀ : (segment b₀)[0]? = some sg₀)
    (hlb : EvalLXPS s f (N.take np) (liftInstrs b₀) l_b (s₁, f₁, .flow (.brk 0 vs))) :
    MRunL body ⟨.block ⟨p, i⟩, N₀.reverse, ls, s₀, f₀⟩ (l₀ ++ l_b)
      ⟨.block ⟨p ++ [(i, 0)], 0⟩, ((vs.take np ++ N.drop np).take np).reverse,
        ⟨np, ((vs.take np ++ N.drop np).drop np).reverse, true, false, [], bt⟩ :: ls, s₁, f₁⟩ := by
  obtain ⟨ht, -, -⟩ := pos_term hp rfl
  have hcA : seqAt body (p ++ [(i, 0)]) = some b₀ := by
    rw [Proofs.Machine.seqAt_append]; simp [hp.hc, hp.hsg, ht, armOf]
  have hokA := arm_ok (a := 0) hp .loop rfl hok
  have har₁ := (arity_congr (MachineLSeq.module_eq hlb) _).trans har
  have hg₂ := gotoN_entry hcA hsg₀
    (⟨np, ((vs.take np ++ N.drop np).drop np).reverse, true, false, [], bt⟩ :: ls)
    ((vs.take np ++ N.drop np).take np).reverse s₁ f₁
  have hA := arm_entry (Fin := fun _ => False)
    (Z := (· = ⟨.block ⟨p ++ [(i, 0)], 0⟩, ((vs.take np ++ N.drop np).take np).reverse,
      ⟨np, ((vs.take np ++ N.drop np).drop np).reverse, true, false, [], bt⟩ :: ls, s₁, f₁⟩))
    (l₂ := []) (nr := nr) hp .loop rfl hok hlb (mot hlb)
    (exit_loopBack (hokA _ _) rfl har₁ ⟨_, by simpa using hg₂, .inr ⟨rfl, rfl⟩⟩)
  have hE := blk_enter hp .loop (.plain (fun _ _ _ => nofun)) rfl har hA s₀ f₀ N₀ l₀ hpre
  obtain ⟨l₁, st₁, l₂, hs, hr, heq⟩ := mEnds_run hE
  rw [show l₀ ++ l_b = l₁ ++ l₂ by rw [← heq]; simp]
  exact .step hs hr

/-- **A loop iteration branching back**, from the arm's entry to its re-entry. -/
theorem loopBack_target_arm {body : Expr} {p : List SeqStep} {c : List Instr} {i : Nat}
    {sg sg₀ : Segment} {pre : List Instr} {bt : BlockType} {b₀ : List Instr} {ls : List LFrame}
    {s s₁ : Store H} {f f₁ : Frame} {N vs : List Val} {l_b : List (SCall H)} {np nr : Nat}
    (hp : Pos body p c i sg pre [.loop bt b₀]) (hok : FramesOk body p.reverse ls)
    (har : arity f bt = some (np, nr)) (hsg₀ : (segment b₀)[0]? = some sg₀)
    (hlb : EvalLXPS s f (N.take np) (liftInstrs b₀) l_b (s₁, f₁, .flow (.brk 0 vs))) :
    ∃ l₁ st₁ l₂, MStepL body ⟨.block ⟨p ++ [(i, 0)], 0⟩, (N.take np).reverse,
        ⟨np, (N.drop np).reverse, true, false, [], bt⟩ :: ls, s, f⟩ l₁ st₁ ∧
      MRunL body st₁ l₂ ⟨.block ⟨p ++ [(i, 0)], 0⟩, ((vs.take np ++ N.drop np).take np).reverse,
        ⟨np, ((vs.take np ++ N.drop np).drop np).reverse, true, false, [], bt⟩ :: ls, s₁, f₁⟩ ∧
      l_b = l₁ ++ l₂ := by
  obtain ⟨ht, -, -⟩ := pos_term hp rfl
  have hcA : seqAt body (p ++ [(i, 0)]) = some b₀ := by
    rw [Proofs.Machine.seqAt_append]; simp [hp.hc, hp.hsg, ht, armOf]
  have hokA := arm_ok (a := 0) hp .loop rfl hok
  have har₁ := (arity_congr (MachineLSeq.module_eq hlb) _).trans har
  have hg₂ := gotoN_entry hcA hsg₀
    (⟨np, ((vs.take np ++ N.drop np).drop np).reverse, true, false, [], bt⟩ :: ls)
    ((vs.take np ++ N.drop np).take np).reverse s₁ f₁
  have hx := exit_loopBack (Fin := fun _ => False)
    (Z := (· = ⟨.block ⟨p ++ [(i, 0)], 0⟩, ((vs.take np ++ N.drop np).take np).reverse,
      ⟨np, ((vs.take np ++ N.drop np).drop np).reverse, true, false, [], bt⟩ :: ls, s₁, f₁⟩))
    (l' := []) (hokA np (N.drop np).reverse) rfl har₁ ⟨_, by simpa using hg₂, .inr ⟨rfl, rfl⟩⟩
  have hpos : Pos body (p ++ [(i, 0)]) b₀ 0 sg₀ [] sg₀.instrs :=
    ⟨hcA, hsg₀, rfl, (segment_isSegmentation b₀).2.2.2 sg₀ (List.mem_of_getElem? hsg₀),
      fun _ _ _ => Nat.zero_le _⟩
  have hE := (mot hlb (p ++ [(i, 0)]) b₀ 0 sg₀ [] sg₀.instrs _ [] hpos
    (by rw [← MachineLSeq.liftInstrs_append, ← restAt_cons hsg₀, restAt_zero])
    (by simpa using hokA np (N.drop np).reverse) hx).1 s f (N.take np) [] .nil
  obtain ⟨l₁, st₁, l₂, hs, hr, heq⟩ := mEnds_run hE
  exact ⟨l₁, st₁, l₂, hs, hr, by rw [← heq]; simp⟩

/-! ## The motive -/

/-- **The block clause**: from block `i` of the sequence at `p`, its instructions `pre` run
natively to `(s, f, N)` with the log `l₀`, the machine diverges after `l₀` then the log `L`. -/
def BlkL (body : Expr) (s : Store H) (f : Frame) (N : List Val) (es : List BExpr)
    (L : List (OCall H)) : Prop :=
  ∀ (p : List SeqStep) (c : List Instr) (i : Nat) (sg : Segment) (pre post : List Instr)
    (ls : List LFrame) (s₀ : Store H) (f₀ : Frame) (N₀ : List Val) (l₀ : List (SCall H)),
    Pos body p c i sg pre post → es = liftInstrs post ++ liftInstrs (restAt c (i + 1)) →
    FramesOk body p.reverse ls →
    EvalLXPS s₀ f₀ N₀ (liftInstrs pre) l₀ (s, f, .flow (.normal N)) →
    MLogDivL body ⟨.block ⟨p, i⟩, N₀.reverse, ls, s₀, f₀⟩ (l₀ ++ L.map OCall.toS)

/-- **The arm clause**: at the entry of the arm of a loop ending block `i`, entered from
`(s, f, N)`, the machine diverges after the log `L`. -/
def ArmL (body : Expr) (s : Store H) (f : Frame) (N : List Val) (es : List BExpr)
    (L : List (OCall H)) : Prop :=
  ∀ (p : List SeqStep) (c : List Instr) (i : Nat) (sg : Segment) (pre : List Instr)
    (bt : BlockType) (b₀ : List Instr) (sg₀ : Segment) (ls : List LFrame) (np nr : Nat),
    Pos body p c i sg pre [.loop bt b₀] → (segment b₀)[0]? = some sg₀ →
    FramesOk body p.reverse ls → arity f bt = some (np, nr) →
    es = liftInstr (.loop bt b₀) :: liftInstrs (restAt c (i + 1)) →
    MLogDivL body ⟨.block ⟨p ++ [(i, 0)], 0⟩, (N.take np).reverse,
      ⟨np, (N.drop np).reverse, true, false, [], bt⟩ :: ls, s, f⟩ (L.map OCall.toS)

/-- **A finished flat instruction, then divergence after the rest's log.** -/
theorem flat_cont {body : Expr} {p : List SeqStep} {c : List Instr} {i : Nat} {sg : Segment}
    {pre post' : List Instr} {e : Instr} {ls : List LFrame} {s s₀ s₂ : Store H} {f f₀ f₂ : Frame}
    {N N₀ N₂ : List Val} {l₀ l_e : List (SCall H)} {es' : List BExpr} {L₂ : List (OCall H)}
    (hp : Pos body p c i sg pre (e :: post')) (hse : ¬ Instr.IsStruct e)
    (hok : FramesOk body p.reverse ls)
    (hpre : EvalLXPS s₀ f₀ N₀ (liftInstrs pre) l₀ (s, f, .flow (.normal N)))
    (hhead : EvalLXPS s f N [liftInstr e] l_e (s₂, f₂, .flow (.normal N₂)))
    (htl : es' = liftInstrs post' ++ liftInstrs (restAt c (i + 1)))
    (hk : LogDivXP s₂ f₂ N₂ es' L₂) (ih : BlkL body s₂ f₂ N₂ es' L₂) :
    MLogDivL body ⟨.block ⟨p, i⟩, N₀.reverse, ls, s₀, f₀⟩ (l₀ ++ l_e ++ L₂.map OCall.toS) := by
  have hpre' : EvalLXPS s₀ f₀ N₀ (liftInstrs (pre ++ [e])) (l₀ ++ l_e)
      (s₂, f₂, .flow (.normal N₂)) := by
    rw [MachineLSeq.liftInstrs_append]
    exact (MachineLSeq.append hpre _).2 _ _ _ rfl _ _ (by simpa [liftInstrs] using hhead)
  cases post' with
  | cons e' post'' =>
    exact ih p c i sg (pre ++ [e]) (e' :: post'') ls s₀ f₀ N₀ (l₀ ++ l_e) (pos_next hp hse) htl
      hok hpre'
  | nil =>
    have ht := pos_last_nonstruct hp hse
    have hb : lookup body ⟨p, i⟩ = some sg := by rw [lookup_eq]; simp [hp.hc, hp.hsg]
    simp only [liftInstrs, List.nil_append] at htl
    subst htl
    obtain ⟨sg', hsg'⟩ := logDiv_ne hk
    have hr : EvalLXPS s₀ f₀ (N₀.reverse).reverse (liftInstrs (MachineL.codeOf sg)) (l₀ ++ l_e)
        (s₂, f₂, .flow (.normal N₂)) := by
      rw [List.reverse_reverse, codeOf_eq, hp.hinstrs]; exact hpre'
    have hstep := MStepL.run hb ht hr
      (.next (by simpa using gotoN_entry hp.hc hsg' ls N₂.reverse s₂ f₂))
    have := ih p c (i + 1) sg' [] sg'.instrs ls s₂ f₂ N₂ [] (MachineLDivI.pos_start hp.hc hsg')
      (MachineLDivI.lift_rest hsg') hok .nil
    simpa using mlog_step hstep this

open Silmaril.Wasm.Cfg.Proofs.MachineLDivI (pos_start lift_rest)

theorem seg0_of_run {c : List Instr} {s s' : Store H} {f f' : Frame} {N N' : List Val}
    {l : List (SCall H)} {k : Nat}
    (h : EvalLXPS s f N (liftInstrs c) l (s', f', .flow (.brk k N'))) :
    ∃ sg₀, (segment c)[0]? = some sg₀ := by
  cases hs : (segment c)[0]? with
  | none =>
    rw [← restAt_zero c, restAt_end hs] at h
    obtain ⟨-, -, h3, -⟩ := nil_inv h
    cases h3
  | some sg₀ => exact ⟨sg₀, rfl⟩

/-- **The main induction**: divergence after a log satisfies both clauses. -/
theorem logDiv_mot {body : Expr} {s : Store H} {f : Frame} {N : List Val} {es : List BExpr}
    {L : List (OCall H)} (h : LogDivXP s f N es L) : BlkL body s f N es L ∧ ArmL body s f N es L := by
  induction h with
  | @div s f N es hd =>
    refine ⟨fun p c i sg pre post ls s₀ f₀ N₀ l₀ hp hes hok hpre => ?_,
      fun p c i sg pre bt b₀ sg₀ ls np nr hp hsg₀ hok har hes => ?_⟩
    · subst hes
      simpa using mlog_of_progO (progB post hp hok hpre hd)
    · subst hes
      simpa using mlog_of_mdiv (mdiv_of_inv (.inr ⟨p, c, i, sg, pre, .loop bt b₀, bt, false, [], b₀,
        sg₀, ls, s, f, N, np, nr, hp, .loop, rfl, hsg₀, hok, har, rfl, hd⟩))
  | args h _ =>
    refine ⟨fun p c i sg pre post ls s₀ f₀ N₀ l₀ hp hes hok hpre => ?_,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hes => by simp [liftInstr] at hes⟩
    obtain ⟨e, post', rfl, hhd, -⟩ := pos_head hp hes
    obtain ⟨-, rfl, -⟩ := lift_op hhd.symm
    exact (logDiv_nil h).elim
  | @callK s s₁ s₂ f f₁ stk stk₁ ws x args es a fi ps rs l₁ l₂ hargs hfi hty hk ih =>
    refine ⟨fun p c i sg pre post ls s₀ f₀ N₀ l₀ hp hes hok hpre => ?_,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hes => by simp [liftInstr] at hes⟩
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    obtain ⟨rfl, rfl, hse⟩ := lift_op hhd.symm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := lxph_nil hargs
    have hhead : EvalLXPS s f stk [liftInstr (.call x)]
        [SCall.mk a (stk.take ps.length).reverse s (.inl (.inl ws)) s₂]
        (s₂, f, .flow (.normal (ws.reverse ++ stk.drop ps.length))) := by
      simpa [liftInstr] using EvalLXPS.callRet (es := []) (l₂ := []) .nil hfi hty .nil
    simpa using flat_cont hp hse hok hpre hhead htl hk ih.1
  | @indK s s₁ s₂ f f₁ stk stk₁ ws x y args es ad iv fa fi ps rs l₁ l₂ hargs hres hfi hty hy hk ih =>
    refine ⟨fun p c i sg pre post ls s₀ f₀ N₀ l₀ hp hes hok hpre => ?_,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hes => by simp [liftInstr] at hes⟩
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    obtain ⟨rfl, rfl, hse⟩ := lift_op hhd.symm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := lxph_nil hargs
    have hhead := EvalLXPS.indRet (es := []) (l₂ := []) (ws := ws) (s₂ := s₂) (stk₁ := stk₁) .nil
      hres hfi hty hy .nil
    have hfc := flat_cont hp hse hok hpre (by simpa [liftInstr] using hhead) htl hk ih.1
    convert hfc using 1
    simp
  | @refK s s₁ s₂ f f₁ stk stk₁ ws y args es fa fi ps rs l₁ l₂ hargs hfi hty hy hk ih =>
    refine ⟨fun p c i sg pre post ls s₀ f₀ N₀ l₀ hp hes hok hpre => ?_,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hes => by simp [liftInstr] at hes⟩
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    obtain ⟨rfl, rfl, hse⟩ := lift_op hhd.symm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := lxph_nil hargs
    have hhead := EvalLXPS.refRet (es := []) (l₂ := []) (ws := ws) (s₂ := s₂) (stk₁ := stk₁) .nil
      hfi hty hy .nil
    have hfc := flat_cont hp hse hok hpre (by simpa [liftInstr] using hhead) htl hk ih.1
    convert hfc using 1
    simp
  | @opK s s₁ s₂ f f₁ f₂ stk stk₁ stk₂ i' args es l₁ l₂ hi hargs hflat hk ih =>
    refine ⟨fun p c i sg pre post ls s₀ f₀ N₀ l₀ hp hes hok hpre => ?_,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hes => by simp [liftInstr] at hes⟩
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    obtain ⟨he, rfl, hse⟩ := lift_op hhd.symm
    subst he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := lxph_nil hargs
    have hhead := EvalLXPS.opOk (es := []) (l₂ := []) hi .nil hflat .nil
    rw [hhd] at hhead
    simpa using flat_cont hp hse hok hpre hhead htl hk ih.1
  | @block s f stk bt bd es np nr l har hk ih =>
    refine ⟨fun p c i sg pre post ls s₀ f₀ N₀ l₀ hp hes hok hpre => ?_,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hes => by simp [liftInstr] at hes⟩
    obtain ⟨e, post', rfl, hhd, -⟩ := pos_head hp hes
    obtain ⟨b₀, rfl, rfl⟩ := lift_block hhd.symm
    obtain ⟨-, rfl, rfl⟩ := pos_term hp rfl
    rw [← restAt_zero b₀] at hk
    obtain ⟨sg₀, hsg₀⟩ := logDiv_ne hk
    obtain ⟨hcA, hokA, hstep⟩ := enter_at hp hok hpre .block (.plain (fun _ _ _ => nofun)) rfl har
      hsg₀
    have := ih.1 (p ++ [(i, 0)]) b₀ 0 sg₀ [] sg₀.instrs _ s f (stk.take np) []
      (pos_start hcA hsg₀) (by simpa [restAt_zero] using lift_rest hsg₀) hokA .nil
    simpa using mlog_step hstep this
  | @blockK s s₁ f f₁ stk vs bt bd es np nr fl l₁ l₂ har hbody hvs hk ih =>
    refine ⟨fun p c i sg pre post ls s₀ f₀ N₀ l₀ hp hes hok hpre => ?_,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hes => by simp [liftInstr] at hes⟩
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    obtain ⟨b₀, rfl, rfl⟩ := lift_block hhd.symm
    obtain ⟨-, rfl, rfl⟩ := pos_term hp rfl
    simp only [liftInstrs, List.nil_append] at htl
    subst htl
    have hrun : EvalLXPS s f stk [liftInstr (.block bt b₀)] (l₁.map OCall.toS)
        (s₁, f₁, .flow (.normal (vs.take nr ++ stk.drop np))) := by
      simpa [liftInstr] using EvalLXPS.blockOk (es := []) (l₂ := []) har
        (evalLXPh_session hbody (ne_trap_of_blockVals hvs)) hvs .nil
    obtain ⟨sg', hsg'⟩ := logDiv_ne hk
    have hrunM := struct_target hp ⟨_, _, _, _, .block⟩ hok hpre hrun hsg'
    have := ih.1 p c (i + 1) sg' [] sg'.instrs ls s₁ f₁ _ [] (pos_start hp.hc hsg') (lift_rest hsg')
      hok .nil
    simpa using mlog_run hrunM this
  | @loop s f stk bt bd es np nr l har hk ih =>
    refine ⟨fun p c i sg pre post ls s₀ f₀ N₀ l₀ hp hes hok hpre => ?_,
      fun p c i sg pre bt' b₀ sg₀ ls np' nr' hp hsg₀ hok har' hes => ?_⟩
    · obtain ⟨e, post', rfl, hhd, -⟩ := pos_head hp hes
      obtain ⟨b₀, rfl, rfl⟩ := lift_loop hhd.symm
      obtain ⟨-, rfl, rfl⟩ := pos_term hp rfl
      rw [← restAt_zero b₀] at hk
      obtain ⟨sg₀, hsg₀⟩ := logDiv_ne hk
      obtain ⟨hcA, hokA, hstep⟩ := enter_at hp hok hpre .loop (.plain (fun _ _ _ => nofun)) rfl har
        hsg₀
      have := ih.1 (p ++ [(i, 0)]) b₀ 0 sg₀ [] sg₀.instrs _ s f (stk.take np) []
        (pos_start hcA hsg₀) (by simpa [restAt_zero] using lift_rest hsg₀) hokA .nil
      simpa using mlog_step hstep this
    · simp only [liftInstr, List.cons.injEq, BExpr.loop.injEq] at hes
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hes
      rw [har] at har'; simp only [Option.some.injEq, Prod.mk.injEq] at har'
      obtain ⟨rfl, rfl⟩ := har'
      obtain ⟨ht, -, -⟩ := pos_term hp rfl
      have hcA : seqAt body (p ++ [(i, 0)]) = some b₀ := by
        rw [Proofs.Machine.seqAt_append]; simp [hp.hc, hp.hsg, ht, armOf]
      have hokA := arm_ok (a := 0) hp .loop rfl hok np (stk.drop np).reverse
      have := ih.1 (p ++ [(i, 0)]) b₀ 0 sg₀ [] sg₀.instrs _ s f (stk.take np) []
        (pos_start hcA hsg₀) (by simpa [restAt_zero] using lift_rest hsg₀) (by simpa using hokA) .nil
      simpa using this
  | @loopK s s₁ f f₁ stk vs bt bd es np nr l₁ l₂ har hbody hk ih =>
    have hrun : ∀ b₀, bd = liftInstrs b₀ → EvalLXPS s f stk [liftInstr (.loop bt b₀)] (l₁.map OCall.toS)
        (s₁, f₁, .flow (.normal (vs.take nr ++ stk.drop np))) := by
      rintro b₀ rfl
      simpa [liftInstr] using EvalLXPS.loopOk (es := []) (l₂ := []) har
        (evalLXPh_session hbody (by simp)) .nil
    refine ⟨fun p c i sg pre post ls s₀ f₀ N₀ l₀ hp hes hok hpre => ?_,
      fun p c i sg pre bt' b₀ sg₀ ls np' nr' hp hsg₀ hok har' hes => ?_⟩
    · obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
      obtain ⟨b₀, rfl, rfl⟩ := lift_loop hhd.symm
      obtain ⟨-, rfl, rfl⟩ := pos_term hp rfl
      simp only [liftInstrs, List.nil_append] at htl
      subst htl
      obtain ⟨sg', hsg'⟩ := logDiv_ne hk
      have hrunM := struct_target hp ⟨_, _, _, _, .loop⟩ hok hpre (hrun b₀ rfl) hsg'
      have := ih.1 p c (i + 1) sg' [] sg'.instrs ls s₁ f₁ _ [] (pos_start hp.hc hsg')
        (lift_rest hsg') hok .nil
      simpa using mlog_run hrunM this
    · simp only [liftInstr, List.cons.injEq, BExpr.loop.injEq] at hes
      obtain ⟨⟨rfl, rfl⟩, htl⟩ := hes
      subst htl
      rw [har] at har'; simp only [Option.some.injEq, Prod.mk.injEq] at har'
      obtain ⟨rfl, rfl⟩ := har'
      obtain ⟨sg', hsg'⟩ := logDiv_ne hk
      have hrunM := struct_target_arm hp hok har hsg₀ (hrun b₀ rfl) hsg'
      have := ih.1 p c (i + 1) sg' [] sg'.instrs ls s₁ f₁ _ [] (pos_start hp.hc hsg')
        (lift_rest hsg') hok .nil
      simpa using mlog_run hrunM this
  | @loopBack s s₁ f f₁ stk vs bt bd es np nr l₁ l₂ har hbody hk ih =>
    have hlb := evalLXPh_session hbody (by simp)
    have har₁ := (arity_congr (MachineLSeq.module_eq hlb) _).trans har
    refine ⟨fun p c i sg pre post ls s₀ f₀ N₀ l₀ hp hes hok hpre => ?_,
      fun p c i sg pre bt' b₀ sg₀ ls np' nr' hp hsg₀ hok har' hes => ?_⟩
    · obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
      obtain ⟨b₀, rfl, rfl⟩ := lift_loop hhd.symm
      obtain ⟨-, rfl, rfl⟩ := pos_term hp rfl
      obtain ⟨sg₀, hsg₀⟩ := seg0_of_run hlb
      have hrunM := loopBack_target hp hok hpre har hsg₀ hlb
      simp only [liftInstrs, List.nil_append] at htl
      have := ih.2 p c i sg sg.body bt b₀ sg₀ ls np nr hp hsg₀ hok har₁
        (by simp [liftInstr, htl])
      simpa using mlog_run hrunM this
    · simp only [liftInstr, List.cons.injEq, BExpr.loop.injEq] at hes
      obtain ⟨⟨rfl, rfl⟩, htl⟩ := hes
      rw [har] at har'; simp only [Option.some.injEq, Prod.mk.injEq] at har'
      obtain ⟨rfl, rfl⟩ := har'
      obtain ⟨lb₁, stb, lb₂, hsb, hrb, hlbe⟩ := loopBack_target_arm hp hok har hsg₀ hlb
      have hrunM := MRunL.step hsb hrb
      rw [← hlbe] at hrunM
      have := ih.2 p c i sg pre bt b₀ sg₀ ls np nr hp hsg₀ hok har₁ (by simp [liftInstr, htl])
      simpa using mlog_run hrunM this
  | cond hk _ =>
    refine ⟨fun p c i sg pre post ls s₀ f₀ N₀ l₀ hp hes hok hpre => ?_,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hes => by simp [liftInstr] at hes⟩
    obtain ⟨e, post', rfl, hhd, -⟩ := pos_head hp hes
    obtain ⟨t₀, e₀, rfl, rfl, -, -⟩ := lift_if hhd.symm
    exact (logDiv_nil hk).elim
  | @arm s s₁ f f₁ stk stk₁ cv b bt cc tt el es np nr l₁ l₂ hc hb har hk ih =>
    refine ⟨fun p c i sg pre post ls s₀ f₀ N₀ l₀ hp hes hok hpre => ?_,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hes => by simp [liftInstr] at hes⟩
    obtain ⟨e, post', rfl, hhd, -⟩ := pos_head hp hes
    obtain ⟨t₀, e₀, rfl, rfl, rfl, rfl⟩ := lift_if hhd.symm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := lxph_nil hc
    obtain ⟨-, rfl, rfl⟩ := pos_term hp rfl
    rw [liftInstrs_ite, ← restAt_zero (if b then t₀ else e₀)] at hk
    obtain ⟨sg₀, hsg₀⟩ := logDiv_ne hk
    obtain ⟨hcA, hokA, hstep⟩ := enter_at hp hok hpre .if_ (.cond hb) (armOf_if' _ _ _ _) har hsg₀
    have := ih.1 _ _ 0 sg₀ [] sg₀.instrs _ s f (stk₁.take np) [] (pos_start hcA hsg₀)
      (by rw [liftInstrs_ite]; simpa [restAt_zero] using lift_rest hsg₀) hokA .nil
    simpa using mlog_step hstep this
  | @ifK s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt cc tt el es np nr fl l₁ l₂ l₃ hc hb har harm hvs hk
      ih =>
    refine ⟨fun p c i sg pre post ls s₀ f₀ N₀ l₀ hp hes hok hpre => ?_,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hes => by simp [liftInstr] at hes⟩
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    obtain ⟨t₀, e₀, rfl, rfl, rfl, rfl⟩ := lift_if hhd.symm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := lxph_nil hc
    obtain ⟨-, rfl, rfl⟩ := pos_term hp rfl
    simp only [liftInstrs, List.nil_append] at htl
    subst htl
    have hrun : EvalLXPS s f (cv :: stk₁) [liftInstr (.if_ bt t₀ e₀)] (l₂.map OCall.toS)
        (s₂, f₂, .flow (.normal (vs.take nr ++ stk₁.drop np))) := by
      simpa [liftInstr] using EvalLXPS.ifOk (es := []) (l₃ := []) .nil hb har
        (evalLXPh_session harm (ne_trap_of_blockVals hvs)) hvs .nil
    obtain ⟨sg', hsg'⟩ := logDiv_ne hk
    have hrunM := struct_target hp ⟨_, _, _, _, .if_⟩ hok hpre hrun hsg'
    have := ih.1 p c (i + 1) sg' [] sg'.instrs ls s₂ f₂ _ [] (pos_start hp.hc hsg') (lift_rest hsg')
      hok .nil
    simpa using mlog_run hrunM this
  | @handler s f stk bt cs bd es np nr l har hk ih =>
    refine ⟨fun p c i sg pre post ls s₀ f₀ N₀ l₀ hp hes hok hpre => ?_,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hes => by simp [liftInstr] at hes⟩
    obtain ⟨e, post', rfl, hhd, -⟩ := pos_head hp hes
    obtain ⟨b₀, rfl, rfl⟩ := lift_try hhd.symm
    obtain ⟨-, rfl, rfl⟩ := pos_term hp rfl
    rw [← restAt_zero b₀] at hk
    obtain ⟨sg₀, hsg₀⟩ := logDiv_ne hk
    obtain ⟨hcA, hokA, hstep⟩ := enter_at hp hok hpre .tryTable (.plain (fun _ _ _ => nofun)) rfl
      har hsg₀
    have := ih.1 (p ++ [(i, 0)]) b₀ 0 sg₀ [] sg₀.instrs _ s f (stk.take np) []
      (pos_start hcA hsg₀) (by simpa [restAt_zero] using lift_rest hsg₀) hokA .nil
    simpa using mlog_step hstep this
  | @tryK s s₁ f f₁ stk vs bt cs bd es np nr fl l₁ l₂ har hbody hvs hk ih =>
    refine ⟨fun p c i sg pre post ls s₀ f₀ N₀ l₀ hp hes hok hpre => ?_,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hes => by simp [liftInstr] at hes⟩
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    obtain ⟨b₀, rfl, rfl⟩ := lift_try hhd.symm
    obtain ⟨-, rfl, rfl⟩ := pos_term hp rfl
    simp only [liftInstrs, List.nil_append] at htl
    subst htl
    have hrun : EvalLXPS s f stk [liftInstr (.tryTable bt cs b₀)] (l₁.map OCall.toS)
        (s₁, f₁, .flow (.normal (vs.take nr ++ stk.drop np))) := by
      simpa [liftInstr] using EvalLXPS.tryOk (es := []) (l₂ := []) (cs := cs) har
        (evalLXPh_session hbody (ne_trap_of_blockVals hvs)) hvs .nil
    obtain ⟨sg', hsg'⟩ := logDiv_ne hk
    have hrunM := struct_target hp ⟨_, _, _, _, .tryTable⟩ hok hpre hrun hsg'
    have := ih.1 p c (i + 1) sg' [] sg'.instrs ls s₁ f₁ _ [] (pos_start hp.hc hsg') (lift_rest hsg')
      hok .nil
    simpa using mlog_run hrunM this

/-- **Divergence after a log is the machine's divergence after the same log**, the calls as
session calls. -/
theorem logDiv_machine {body : Expr} {s : Store H} {f : Frame} {L : List (OCall H)}
    (h : LogDivXP s f [] (liftInstrs body) L) :
    MLogDivL body (initial body s f) (L.map OCall.toS) := by
  have hm := (logDiv_mot (body := body) h).1
  rw [← restAt_zero body] at h
  obtain ⟨sg₀, hsg₀⟩ := logDiv_ne h
  have hg := gotoN_entry (body := body) (p := []) rfl hsg₀ [] [] s f
  rw [initial_eq] at hg
  simp only [Option.some.injEq] at hg
  rw [hg]
  simpa using hm [] body 0 sg₀ [] sg₀.instrs [] s f [] [] (pos_start rfl hsg₀)
    (by rw [← lift_rest hsg₀, restAt_zero]) trivial .nil

end Silmaril.Wasm.Cfg.Proofs.MachineLLogDiv
