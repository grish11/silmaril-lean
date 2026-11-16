module

public import Silmaril.Proofs.Wasm.Cfg.Machine
import Silmaril.Wasm.Cfg.Block.Thms
import Silmaril.Wasm.SingleThreaded.Determinism.Head
import Silmaril.Wasm.SingleThreaded.Determinism.Family
import Silmaril.Wasm.Execution.Core.Inversion.Thms

@[expose] public section

/-!
# Completeness of the block-CFG machine for the region semantics

Every region run of a function body is a machine run from its initial state. The proof is by
induction on the `Region.Run` derivation, against a shape relation `Rep` between region codes
and the machine states they stand for, at a level (`Lv`) of the label nesting.
-/

namespace Silmaril.Wasm.Cfg.Proofs.MachineComplete

set_option linter.unusedSimpArgs false

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H}

/-! ## `unreachable` never runs to values -/

theorem famStep_unreachable {s : Store H} {f : Frame} {vs : List Val} {c : Config H}
    (h : FamStep P ⟨s, f, vals vs ++ [.plain .unreachable]⟩ c) : c = ⟨s, f, [.trap]⟩ := by
  have hk : ∀ {k : SingleThreaded.Det.Fam},
      SingleThreaded.Det.FamShape k (vals vs ++ [.plain .unreachable]) → k = .parametric :=
    fun hs => ((SingleThreaded.Det.famOf_of_shape hs).2).symm.trans (by rfl)
  cases h with
  | parametric h =>
    generalize he : vals vs ++ [Admin.plain .unreachable] = l at h
    cases h with
    | unreachable => rfl
    | _ => have := congrArg List.getLast? he; simp at this
  | numeric h => cases hk (SingleThreaded.Det.NumericStep.shape h)
  | vector h => cases hk (SingleThreaded.Det.VectorStep.shape h)
  | «variable» h => cases hk (SingleThreaded.Det.VariableStep.shape h)
  | table h => cases hk (SingleThreaded.Det.TableStep.shape h)
  | memory h => cases hk (SingleThreaded.Det.MemoryStep.shape h)
  | reference h => cases hk (SingleThreaded.Det.RefStep.shape h)
  | aggregate h => cases hk (SingleThreaded.Det.AggregateStep.shape h)

theorem step_unreachable {s : Store H} {f : Frame} {vs : List Val} {c : Config H}
    (h : Step P host ⟨s, f, vals vs ++ [.plain .unreachable]⟩ c) :
    ∃ w, c = ⟨s, f, vals w ++ [.trap]⟩ := by
  obtain ⟨ws, vs', c₀, -, hf, rfl⟩ :=
    Step.noncontrol_vals_inv (by simp [SingleThreaded.Det.famOf]) h
  cases famStep_unreachable hf
  exact ⟨ws, rfl⟩

theorem steps_trap_vals {s : Store H} {f : Frame} {w : List Val} {c : Config H}
    (h : Steps P host ⟨s, f, vals w ++ [.trap]⟩ c) : ∃ w', c = ⟨s, f, vals w' ++ [.trap]⟩ := by
  induction h with
  | refl => exact ⟨w, rfl⟩
  | tail _ hst ih =>
    obtain ⟨w', rfl⟩ := ih
    obtain ⟨w'', rfl, -⟩ := Step.trap_vals_inv hst
    exact ⟨w'', rfl⟩

theorem not_mem_vals {a : Admin} (ha : a.val? = none) {ws : List Val} : a ∉ vals ws := by
  intro hm
  simp only [vals, List.mem_map] at hm
  obtain ⟨v, -, rfl⟩ := hm
  simp at ha

/-- **`unreachable` under values never runs to values.** -/
theorem steps_unreachable_not_vals {s s' : Store H} {f f' : Frame} {vs ws : List Val}
    (h : Steps P host ⟨s, f, vals vs ++ [.plain .unreachable]⟩ ⟨s', f', vals ws⟩) : False := by
  rcases h.cases_head with he | ⟨c, hc, hr⟩
  · have : Admin.plain .unreachable ∈ vals ws := by
      have := congrArg Config.code he; simp only at this; rw [← this]; simp
    exact not_mem_vals rfl this
  · obtain ⟨w, rfl⟩ := step_unreachable hc
    obtain ⟨w', he⟩ := steps_trap_vals hr
    have : Admin.trap ∈ vals ws := by
      have := congrArg Config.code he; simp only at this; rw [this]; simp
    exact not_mem_vals rfl this


/-! ## Levels, targets and what a run reaches -/

/-- A level of the label nesting at which a region code runs: where its branches go (path `p`,
frames `ls`, values `pre` put under branch values), where it continues when it finishes
(`cont`), and where its exceptions are handled (path `tq`, frames `tls`). -/
structure Lv (H : Type) where
  p : List SeqStep
  ls : List LFrame
  pre : List Val
  cont : List Val → Store H → Frame → MState H
  tq : List SeqStep
  tls : List LFrame

/-- The level of the sequence at path `p` with frames `ls`. -/
def seqLv (body : Expr) (p : List SeqStep) (ls : List LFrame) : Lv H :=
  ⟨p, ls, [], fun us s f => goto (contRev body p.reverse) p.length ls us s f, p, ls⟩

/-- The level of the `label` inside the `HANDLER` of the `try_table` frame `L` at position
`(m, a)` of sequence `p`. -/
def hlLv (body : Expr) (p : List SeqStep) (m a : Nat) (L : LFrame) (ls : List LFrame) : Lv H :=
  ⟨p, ls, L.outer, fun us s f => goto (contRev body ((m, a) :: p.reverse)) p.length ls
    (L.outer ++ us) s f, p ++ [(m, a)], L :: ls⟩

/-- Where a branch to the `k`-th label (frame `L`) out of sequence `p` with frames `ls` and
carried values `V` goes, as the machine's branch steps compute it. -/
def brTarget (body : Expr) (p : List SeqStep) (k : Nat) (L : LFrame) (ls : List LFrame)
    (V : List Val) (s : Store H) (f : Frame) : MState H :=
  if L.loop then
    goto ((labelsRev body p.reverse).getD k .invalid) (p.length - k) (L :: ls.drop (k + 1))
      (topVals L.arity V) s f
  else
    goto ((labelsRev body p.reverse).getD k .invalid) (p.length - (k + 1)) (ls.drop (k + 1))
      (L.outer ++ topVals L.arity V) s f

/-- A `loop` frame's block type resolves in the frame's module to its arity of parameters. -/
def LoopOk (f : Frame) (L : LFrame) : Prop :=
  L.loop = true → ∃ t₁ t₂, f.module.blockType? L.bt = some (t₁, t₂) ∧ t₁.length = L.arity

/-- The handlers of the first `j` frames let the exception pass. -/
def Pass (s : Store H) (f : Frame) (a : Nat) (ls : List LFrame) (j : Nat) : Prop :=
  ∀ (k : Nat) (L : LFrame), k < j → ls[k]? = some L → L.tryT = true →
    Catches s f a L.catches none

/-- Every handler lets the exception pass. -/
def AllPass (s : Store H) (f : Frame) (a : Nat) (ls : List LFrame) : Prop :=
  ∀ (k : Nat) (L : LFrame), ls[k]? = some L → L.tryT = true → Catches s f a L.catches none

/-- Machine runs. -/
abbrev MRun (P : Profile) (host : HostSemantics H) (C : Abstract.CallRel H) (body : Expr) :=
  Relation.ReflTransGen (MStepC P host C body)

/-- **What a region outcome at a level asks of the machine from `st`.** -/
def Reach (P : Profile) (host : HostSemantics H) (C : Abstract.CallRel H) (body : Expr) (lv : Lv H) (st : MState H)
    (s' : Store H) (f' : Frame) : Out → Prop
  | .normal us => MRun P host C body st (lv.cont us s' f')
  | .br k us => (∀ L, lv.ls[k]? = some L →
      L.arity ≤ (brVals k lv.ls (lv.pre ++ us)).length → LoopOk f' L →
      Relation.TransGen (MStepC P host C body) st
        (brTarget body lv.p k L lv.ls (brVals k lv.ls (lv.pre ++ us)) s' f')) ∧
      (k = lv.ls.length → ∃ W stk, us = W ++ stk ∧ MRun P host C body st ⟨.exit, stk, [], s', f'⟩)
  | .ret us => ∃ W stk, us = W ++ stk ∧ MRun P host C body st ⟨.exit, stk, [], s', f'⟩
  | .trap => MRun P host C body st ⟨.trap, [], [], s', f'⟩
  | .throw a =>
    (∀ (j : Nat) (L : LFrame) (us : List Val) (l : LabelIdx) (L' : LFrame),
      Pass s' f' a lv.tls j → lv.tls[j]? = some L → L.tryT = true →
      Catches s' f' a L.catches (some (us, l)) → lv.tls[j + 1 + l.toNat]? = some L' →
      L'.arity ≤ (brVals l.toNat (lv.tls.drop (j + 1)) (L.outer ++ us)).length →
      LoopOk f' L' →
      Relation.TransGen (MStepC P host C body) st (brTarget body lv.tq (j + 1 + l.toNat) L' lv.tls
        (brVals l.toNat (lv.tls.drop (j + 1)) (L.outer ++ us)) s' f')) ∧
    (AllPass s' f' a lv.tls → MRun P host C body st ⟨.raise, [.ref (.exn a)], [], s', f'⟩) ∧
    (∀ (j : Nat) (L : LFrame) (us : List Val) (l : LabelIdx),
      Pass s' f' a lv.tls j → lv.tls[j]? = some L → L.tryT = true →
      Catches s' f' a L.catches (some (us, l)) → j + 1 + l.toNat = lv.tls.length →
      MRun P host C body st ⟨.exit, L.outer ++ us, [], s', f'⟩)
  | .tail W a _ => ∀ (fi : FuncInst H) (ps rs : List CValType) (W₀ args : List Val)
      (fl : Binaryen.Flow) (s₃ : Store H) (st' : MState H), s'.funcs[a]? = some fi →
      DefType.funcType? fi.type = some (ps, rs) →
      brVals lv.ls.length lv.ls (lv.pre ++ W) = W₀ ++ args → args.length = ps.length →
      C s' a args (s₃, fl) → tailEnd rs.length s₃ f' fl = some st' → MRun P host C body st st'
  | .tailNull _ _ => MRun P host C body st ⟨.trap, [], [], s', f'⟩

/-- **The machine state a region code stands for**, at a level, for a run of the code from
`s, f` on stack `vs`. -/
inductive Rep (P : Profile) (host : HostSemantics H) (C : Abstract.CallRel H) (body : Expr) :
    Lv H → Store H → Frame → List Val → List Admin → MState H → Prop where
  /-- Inside block `i` of sequence `p`: the body prefix `pre` ran from the block's state. -/
  | blk {p : List SeqStep} {ls : List LFrame} {c : List Instr} {i : Nat} {sg : Segment}
      {pre sfx : List Instr} {stk₀ : List Val} {s₀ s : Store H} {f₀ f : Frame} {vs V : List Val}
      (hc : seqAt body p = some c) (hsg : (segment c)[i]? = some sg)
      (hbody : sg.body = pre ++ sfx) (hne : sfx ≠ [] ∨ sg.term.isSome)
      (hpre : RunC P host C s₀ f₀ stk₀ (expression pre) s f (.normal (vs ++ V))) :
      Rep P host C body (seqLv body p ls) s f vs
        (vals V ++ expression (sfx ++ sg.term.toList ++ restAt c (i + 1)))
        ⟨.block ⟨p, i⟩, stk₀, ls, s₀, f₀⟩
  /-- At an `if` terminator, after Core chose the arm (`block bt arm`). -/
  | blkIf {p : List SeqStep} {ls : List LFrame} {c : List Instr} {i : Nat} {sg : Segment}
      {bt : BlockType} {t e : List Instr} {k : BitVec 32} {stk₀ ws : List Val}
      {s₀ s : Store H} {f₀ f : Frame} {vs V : List Val}
      (hc : seqAt body p = some c) (hsg : (segment c)[i]? = some sg)
      (ht : sg.term = some (.if_ bt t e))
      (hpre : RunC P host C s₀ f₀ stk₀ (expression sg.body) s f (.normal (ws ++ [.i32 k])))
      (hstk : vs ++ V = ws) :
      Rep P host C body (seqLv body p ls) s f vs
        (vals V ++ .plain (.block bt (if k = 0 then e else t)) :: expression (restAt c (i + 1)))
        ⟨.block ⟨p, i⟩, stk₀, ls, s₀, f₀⟩
  /-- The sequence is finished. -/
  | fin {p : List SeqStep} {ls : List LFrame} {s : Store H} {f : Frame} {vs V : List Val} :
      Rep P host C body (seqLv body p ls) s f vs (vals V)
        (goto (contRev body p.reverse) p.length ls (vs ++ V) s f)
  /-- Inside the label of a structured terminator at `(m, a)` (not a `try_table`). -/
  | lab {p : List SeqStep} {ls : List LFrame} {c : List Instr} {m a : Nat} {sg : Segment}
      {t : Instr} {c' : List Instr} {L : LFrame} {inner : List Admin} {s : Store H} {f : Frame}
      {vs V : List Val} {st : MState H}
      (hc : seqAt body p = some c) (hsg : (segment c)[m]? = some sg) (ht : sg.term = some t)
      (harm : armOf t a = some c') (hkind : StructKind t L.bt L.loop L.tryT L.catches)
      (hT : L.tryT = false) (hlo : LoopOk f L) (hW : vs ++ V = L.outer)
      (hin : Rep P host C body (seqLv body (p ++ [(m, a)]) (L :: ls)) s f [] inner st) :
      Rep P host C body (seqLv body p ls) s f vs
        (vals V ++ .label L.arity (if L.loop then [t] else []) inner ::
          expression (restAt c (m + 1))) st
  /-- Inside the handler of a `try_table` at `(m, a)`. -/
  | hnd {p : List SeqStep} {ls : List LFrame} {c : List Instr} {m a : Nat} {sg : Segment}
      {t : Instr} {c' : List Instr} {L : LFrame} {inner : List Admin} {s : Store H} {f : Frame}
      {vs V : List Val} {st : MState H}
      (hc : seqAt body p = some c) (hsg : (segment c)[m]? = some sg) (ht : sg.term = some t)
      (harm : armOf t a = some c') (hkind : StructKind t L.bt L.loop L.tryT L.catches)
      (hT : L.tryT = true) (hW : vs ++ V = L.outer)
      (hin : Rep P host C body (hlLv body p m a L ls) s f [] [.label L.arity [] inner] st) :
      Rep P host C body (seqLv body p ls) s f vs
        (vals V ++ .handler L.arity L.catches [.label L.arity [] inner] ::
          expression (restAt c (m + 1))) st
  /-- The label inside a `try_table`'s handler. -/
  | hlab {p : List SeqStep} {ls : List LFrame} {m a : Nat} {L : LFrame} {inner : List Admin}
      {s : Store H} {f : Frame} {st : MState H}
      (hnl : isLoopAt body p m = false) (hloop : L.loop = false)
      (hin : Rep P host C body (seqLv body (p ++ [(m, a)]) (L :: ls)) s f [] inner st) :
      Rep P host C body (hlLv body p m a L ls) s f [] [.label L.arity [] inner] st
  /-- About to re-enter a `loop` after a branch to its label: the machine is already at the
  loop body's entry. -/
  | loopRe {p : List SeqStep} {ls : List LFrame} {c : List Instr} {m : Nat} {sg : Segment}
      {bt : BlockType} {b : List Instr} {L : LFrame} {s : Store H} {f : Frame}
      {vs V W : List Val}
      (hc : seqAt body p = some c) (hsg : (segment c)[m]? = some sg)
      (ht : sg.term = some (.loop bt b))
      (hkind : StructKind (.loop bt b) L.bt L.loop L.tryT L.catches) (hlo : LoopOk f L)
      (hW : vs ++ V = L.outer ++ W) (hWl : W.length = L.arity) :
      Rep P host C body (seqLv body p ls) s f vs
        (vals V ++ .plain (.loop bt b) :: expression (restAt c (m + 1)))
        (goto (entry body (p ++ [(m, 0)]) 0) (p.length + 1) (L :: ls) W s f)


/-! ## Helpers -/

open Silmaril.Wasm.Cfg.Proofs.Machine in
theorem seg_wf {c : List Instr} {i : Nat} {sg : Segment} (hsg : (segment c)[i]? = some sg) :
    sg.instrs ≠ [] ∧ (∀ x ∈ sg.body, isTerminator x = false) := by
  have hseg := segment_isSegmentation c
  have hm : sg ∈ segment c := List.mem_of_getElem? hsg
  exact ⟨hseg.2.2.2 sg hm, (hseg.2.1 sg hm).1⟩

open Silmaril.Wasm.Cfg.Proofs.Machine in
/-- **The machine state at a sequence position stands for the rest of the sequence.** -/
theorem rep_entry {body : Expr} {q : List SeqStep} {c : List Instr} (i : Nat) (ls : List LFrame)
    {s : Store H} {f : Frame} (vs V : List Val) (hc : seqAt body q = some c) :
    Rep P host C body (seqLv body q ls) s f vs (vals V ++ expression (restAt c i))
      (goto (entry body q i) q.length ls (vs ++ V) s f) := by
  unfold entry
  split
  · rename_i hl
    rw [lookup_eq] at hl
    simp only [hc, Option.bind_some, Option.isSome_iff_exists] at hl
    obtain ⟨sg, hsg⟩ := hl
    have hne : sg.body ≠ [] ∨ sg.term.isSome := by
      by_contra hn
      simp only [not_or, ne_eq, not_not, Option.not_isSome_iff_eq_none] at hn
      exact (seg_wf hsg).1 (by simp [Segment.instrs, hn.1, hn.2])
    have := Rep.blk (P := P) (host := host) (C := C) (ls := ls) (pre := []) (sfx := sg.body) (V := V)
      (vs := vs) (s₀ := s) (f₀ := f) (stk₀ := vs ++ V) hc hsg (by simp) hne .nil
    rw [restAt_cons hsg]
    simpa [goto, depthT, popL, Segment.instrs] using this
  · rename_i hl
    rw [restAt_none hc (by simpa using hl)]
    simpa [cont, expression] using
      (Rep.fin (P := P) (host := host) (C := C) (body := body) (p := q) (ls := ls) (s := s) (f := f)
        (vs := vs) (V := V))

theorem reach_mono {body : Expr} {lv : Lv H} {st st₁ : MState H} {s' : Store H} {f' : Frame}
    {o : Out} (hm : MRun P host C body st st₁)
    (h : Reach P host C body lv st₁ s' f' o) : Reach P host C body lv st s' f' o := by
  cases o with
  | normal us => exact hm.trans h
  | br k us =>
    exact ⟨fun L hL har hlo => Relation.TransGen.trans_right hm (h.1 L hL har hlo),
      fun hk => by obtain ⟨W, stk, he, hr⟩ := h.2 hk; exact ⟨W, stk, he, hm.trans hr⟩⟩
  | ret us => obtain ⟨W, stk, he, hr⟩ := h; exact ⟨W, stk, he, hm.trans hr⟩
  | trap => exact hm.trans h
  | throw a =>
    exact ⟨fun j L us l L' h1 h2 h3 h4 h5 h6 h7 =>
      Relation.TransGen.trans_right hm (h.1 j L us l L' h1 h2 h3 h4 h5 h6 h7),
      fun h1 => hm.trans (h.2.1 h1), fun j L us l h1 h2 h3 h4 h5 => hm.trans (h.2.2 j L us l h1 h2 h3 h4 h5)⟩
  | tail => exact fun fi ps rs W₀ args fl s₃ st' h1 h2 h3 h4 h5 h6 =>
      hm.trans (h fi ps rs W₀ args fl s₃ st' h1 h2 h3 h4 h5 h6)
  | tailNull => exact hm.trans h

theorem reach_step {body : Expr} {lv : Lv H} {st st₁ : MState H} {s' : Store H} {f' : Frame}
    {o : Out} (hs : MStepC P host C body st st₁) (h : Reach P host C body lv st₁ s' f' o) :
    Reach P host C body lv st s' f' o :=
  reach_mono (.single hs) h

theorem brTarget_succ (body : Expr) (p : List SeqStep) (m a k : Nat) (L' L : LFrame)
    (ls : List LFrame) (V : List Val) (s : Store H) (f : Frame) :
    brTarget body (p ++ [(m, a)]) (k + 1) L' (L :: ls) V s f = brTarget body p k L' ls V s f := by
  simp [brTarget, labelsRev, List.getD_cons_succ]

open Silmaril.Wasm.Cfg.Proofs.Machine in
/-- Finishing an arm continues the parent sequence after the structured terminator. -/
theorem cont_arm (body : Expr) (p : List SeqStep) (m a : Nat) (L : LFrame) (ls : List LFrame)
    (us : List Val) (s : Store H) (f : Frame) :
    goto (contRev body ((m, a) :: p.reverse)) p.length ls (L.outer ++ us) s f =
      goto (entry body p (m + 1)) p.length ls (L.outer ++ us) s f := by
  simp [contRev, entry, cont]

open Silmaril.Wasm.Cfg.Proofs.Machine in
theorem seqLv_cont_arm (body : Expr) (p : List SeqStep) (m a : Nat) (L : LFrame)
    (ls : List LFrame) (us : List Val) (s : Store H) (f : Frame) :
    (seqLv body (p ++ [(m, a)]) (L :: ls)).cont us s f =
      goto (entry body p (m + 1)) p.length ls (L.outer ++ us) s f := by
  simp only [seqLv, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, List.length_append, List.length_cons, List.length_nil]
  rw [goto_succ (by simpa using depth_contRev_cons body m a p.reverse)]
  exact cont_arm body p m a L ls us s f

theorem hlLv_cont (body : Expr) (p : List SeqStep) (m a : Nat) (L : LFrame) (ls : List LFrame)
    (us : List Val) (s : Store H) (f : Frame) :
    (hlLv body p m a L ls).cont us s f =
      goto (entry body p (m + 1)) p.length ls (L.outer ++ us) s f :=
  cont_arm body p m a L ls us s f

theorem val_none_of_noncontrol {i : Instr} (h : SingleThreaded.Det.famOf (.plain i) ≠ .control) :
    (Admin.plain i).val? = none := by
  unfold Admin.val?
  split <;> simp_all [SingleThreaded.Det.famOf]

theorem brStep_val_none {s : Store H} {f : Frame} {us us' : List Val} {i : Instr}
    {X : List Admin} (h : BrStep s f us i us' X) : (Admin.plain i).val? = none := by
  cases h <;> rfl

/-- **The only rule for a value at the head pushes it.** -/
theorem run_head_val {s s' : Store H} {f f' : Frame} {vs : List Val} {a : Admin} {v : Val}
    {code : List Admin} {o : Out} (h : RunC P host C s f vs (a :: code) s' f' o)
    (hv : a.val? = some v) : RunC P host C s f (vs ++ [v]) code s' f' o := by
  cases h with
  | val hv' h' => rw [hv] at hv'; cases hv'; exact h'
  | simple hi => rw [val_none_of_noncontrol hi] at hv; cases hv
  | simpleTrap hi => rw [val_none_of_noncontrol hi] at hv; cases hv
  | brData hb => rw [brStep_val_none hb] at hv; cases hv
  | returnCallRef hc => rw [Proofs.Region.isRetCallRef_val hc] at hv; cases hv
  | returnCallRefNull hc => rw [Proofs.Region.isRetCallRef_val hc] at hv; cases hv
  | _ => simp [Admin.val?] at hv

/-- A run of values only pushes them. -/
theorem run_vals_only {s s' : Store H} {f f' : Frame} :
    ∀ {vs W : List Val} {o : Out}, RunC P host C s f vs (vals W) s' f' o →
      o = .normal (vs ++ W) ∧ s' = s ∧ f' = f
  | _, [], o, h => by cases h; simp
  | vs, w :: W, o, h => by
    have h' := run_head_val (v := w) (by simpa [vals] using h) (by simp)
    have := run_vals_only (vs := vs ++ [w]) (W := W) h'
    simpa using this


theorem vals_cons_eq {V : List Val} {X : List Admin} {a : Admin} {code : List Admin}
    (h : vals V ++ X = a :: code) :
    (∃ v V', V = v :: V' ∧ a = v.toAdmin ∧ code = vals V' ++ X) ∨ (V = [] ∧ X = a :: code) := by
  cases V with
  | nil => right; simpa using h
  | cons v V' => left; simp [vals] at h; exact ⟨v, V', rfl, h.1.symm, h.2.symm⟩

theorem expr_cons_eq {L : List Instr} {a : Admin} {code : List Admin}
    (h : expression L = a :: code) : ∃ x L', L = x :: L' ∧ a = .plain x ∧ code = expression L' := by
  cases L with
  | nil => simp [expression] at h
  | cons x L' => simp [expression] at h; exact ⟨x, L', rfl, h.1.symm, h.2.symm⟩

/-- The head of a block's remaining code: a body instruction, or the terminator. -/
theorem blk_head {sfx : List Instr} {T : Option Instr} {R : List Instr} {a : Admin}
    {code : List Admin} (hne : sfx ≠ [] ∨ T.isSome)
    (h : expression (sfx ++ T.toList ++ R) = a :: code) :
    (∃ x sfx', sfx = x :: sfx' ∧ a = .plain x ∧ code = expression (sfx' ++ T.toList ++ R)) ∨
      (sfx = [] ∧ ∃ t, T = some t ∧ a = .plain t ∧ code = expression R) := by
  cases sfx with
  | cons x sfx' =>
    left; simp [expression] at h; exact ⟨x, sfx', rfl, h.1.symm, by simp [expression, h.2]⟩
  | nil =>
    cases T with
    | none => simp at hne
    | some t =>
      right; simp [expression] at h; exact ⟨rfl, t, rfl, h.1.symm, by simp [expression, h.2]⟩

theorem term_val_none {c : List Instr} {i : Nat} {sg : Segment} {t : Instr}
    (hsg : (segment c)[i]? = some sg) (ht : sg.term = some t) : (Admin.plain t).val? = none := by
  have hseg := segment_isSegmentation c
  have hwf := (hseg.2.1 sg (List.mem_of_getElem? hsg)).2 t (by simp [ht])
  unfold Admin.val?
  split <;> simp_all [isTerminator]

open Silmaril.Wasm.Cfg.Proofs.Machine in
theorem lookup_of {body : Expr} {p : List SeqStep} {c : List Instr} {i : Nat} {sg : Segment}
    (hc : seqAt body p = some c) (hsg : (segment c)[i]? = some sg) :
    lookup body ⟨p, i⟩ = some sg := by
  rw [lookup_eq]; simp [hc, hsg]

/-- **Advancing inside a block** by one body instruction `x`: extend the body prefix, or, at the
end of a terminator-free block, take the machine's fall-through step. -/
theorem blk_adv {body : Expr} {p : List SeqStep} {ls : List LFrame} {c : List Instr} {i : Nat}
    {sg : Segment} {pre sfx' : List Instr} {x : Instr} {stk₀ : List Val} {s₀ s s₁ s' : Store H}
    {f₀ f f₁ f' : Frame} {vs vs₁ : List Val} {o : Out}
    (hc : seqAt body p = some c) (hsg : (segment c)[i]? = some sg)
    (hbody : sg.body = pre ++ x :: sfx')
    (hpre : RunC P host C s₀ f₀ stk₀ (expression pre) s f (.normal vs))
    (hx : RunC P host C s f vs [.plain x] s₁ f₁ (.normal vs₁))
    (ih : ∀ (lv : Lv H) (st : MState H),
      Rep P host C body lv s₁ f₁ vs₁ (expression (sfx' ++ sg.term.toList ++ restAt c (i + 1))) st →
        Reach P host C body lv st s' f' o) :
    Reach P host C body (seqLv body p ls) ⟨.block ⟨p, i⟩, stk₀, ls, s₀, f₀⟩ s' f' o := by
  have hpre' : RunC P host C s₀ f₀ stk₀ (expression (pre ++ [x])) s₁ f₁ (.normal vs₁) := by
    simpa [expression] using Proofs.Region.run_append hpre (by simp only [ThenC]; exact hx)
  by_cases hne : sfx' ≠ [] ∨ sg.term.isSome
  · have hr := Rep.blk (P := P) (host := host) (C := C) (ls := ls) (V := []) (vs := vs₁)
      (pre := pre ++ [x]) hc hsg (by simp [hbody]) hne (by simpa using hpre')
    exact ih _ _ (by simpa using hr)
  · have hsfx : sfx' = [] := by by_contra h'; exact hne (Or.inl h')
    have hterm : sg.term = none := by
      cases ht : sg.term with
      | none => rfl
      | some t => exact absurd (Or.inr (by simp [ht])) hne
    subst hsfx
    have hr : RunC P host C s₀ f₀ stk₀ (expression sg.body) s₁ f₁ (.normal vs₁) := by
      rw [hbody]; simpa using hpre'
    refine reach_step (MStepC.fall (b := ⟨p, i⟩) (lookup_of hc hsg) hterm hr) ?_
    exact ih _ _ (by simpa [hterm] using rep_entry (P := P) (host := host) (C := C) (i + 1) ls vs₁ [] hc)

/-- **What a code with a non-value head stands for.** -/
inductive HeadRep (P : Profile) (host : HostSemantics H) (C : Abstract.CallRel H) (body : Expr) (s : Store H) (f : Frame) :
    Lv H → List Val → Admin → List Admin → MState H → Prop where
  | body {p : List SeqStep} {ls : List LFrame} {c : List Instr} {i : Nat} {sg : Segment}
      {pre sfx : List Instr} {x : Instr} {stk₀ : List Val} {s₀ : Store H} {f₀ : Frame}
      {vs : List Val}
      (hc : seqAt body p = some c) (hsg : (segment c)[i]? = some sg)
      (hbody : sg.body = pre ++ x :: sfx) (hx : isTerminator x = false)
      (hpre : RunC P host C s₀ f₀ stk₀ (expression pre) s f (.normal vs)) :
      HeadRep P host C body s f (seqLv body p ls) vs (.plain x)
        (expression (sfx ++ sg.term.toList ++ restAt c (i + 1)))
        ⟨.block ⟨p, i⟩, stk₀, ls, s₀, f₀⟩
  | term {p : List SeqStep} {ls : List LFrame} {c : List Instr} {i : Nat} {sg : Segment}
      {t : Instr} {stk₀ : List Val} {s₀ : Store H} {f₀ : Frame} {vs : List Val}
      (hc : seqAt body p = some c) (hsg : (segment c)[i]? = some sg) (ht : sg.term = some t)
      (hpre : RunC P host C s₀ f₀ stk₀ (expression sg.body) s f (.normal vs)) :
      HeadRep P host C body s f (seqLv body p ls) vs (.plain t) (expression (restAt c (i + 1)))
        ⟨.block ⟨p, i⟩, stk₀, ls, s₀, f₀⟩
  | blkIf {p : List SeqStep} {ls : List LFrame} {c : List Instr} {i : Nat} {sg : Segment}
      {bt : BlockType} {t e : List Instr} {k : BitVec 32} {stk₀ ws : List Val}
      {s₀ : Store H} {f₀ : Frame}
      (hc : seqAt body p = some c) (hsg : (segment c)[i]? = some sg)
      (ht : sg.term = some (.if_ bt t e))
      (hpre : RunC P host C s₀ f₀ stk₀ (expression sg.body) s f (.normal (ws ++ [.i32 k]))) :
      HeadRep P host C body s f (seqLv body p ls) ws (.plain (.block bt (if k = 0 then e else t)))
        (expression (restAt c (i + 1))) ⟨.block ⟨p, i⟩, stk₀, ls, s₀, f₀⟩
  | lab {p : List SeqStep} {ls : List LFrame} {c : List Instr} {m a : Nat} {sg : Segment}
      {t : Instr} {c' : List Instr} {L : LFrame} {inner : List Admin} {st : MState H}
      (hc : seqAt body p = some c) (hsg : (segment c)[m]? = some sg) (ht : sg.term = some t)
      (harm : armOf t a = some c') (hkind : StructKind t L.bt L.loop L.tryT L.catches)
      (hT : L.tryT = false) (hlo : LoopOk f L) {vs : List Val} (hW : vs = L.outer)
      (hin : Rep P host C body (seqLv body (p ++ [(m, a)]) (L :: ls)) s f [] inner st) :
      HeadRep P host C body s f (seqLv body p ls) vs
        (.label L.arity (if L.loop then [t] else []) inner) (expression (restAt c (m + 1))) st
  | hnd {p : List SeqStep} {ls : List LFrame} {c : List Instr} {m a : Nat} {sg : Segment}
      {t : Instr} {c' : List Instr} {L : LFrame} {inner : List Admin} {st : MState H}
      (hc : seqAt body p = some c) (hsg : (segment c)[m]? = some sg) (ht : sg.term = some t)
      (harm : armOf t a = some c') (hkind : StructKind t L.bt L.loop L.tryT L.catches)
      (hT : L.tryT = true) {vs : List Val} (hW : vs = L.outer)
      (hin : Rep P host C body (hlLv body p m a L ls) s f [] [.label L.arity [] inner] st) :
      HeadRep P host C body s f (seqLv body p ls) vs
        (.handler L.arity L.catches [.label L.arity [] inner]) (expression (restAt c (m + 1))) st
  | hlab {p : List SeqStep} {ls : List LFrame} {m a : Nat} {L : LFrame} {inner : List Admin}
      {st : MState H}
      {vs : List Val} (hv : vs = []) {code : List Admin} (hcode : code = [])
      (hnl : isLoopAt body p m = false) (hloop : L.loop = false)
      (hin : Rep P host C body (seqLv body (p ++ [(m, a)]) (L :: ls)) s f [] inner st) :
      HeadRep P host C body s f (hlLv body p m a L ls) vs (.label L.arity [] inner) code st
  | loopRe {p : List SeqStep} {ls : List LFrame} {c : List Instr} {m : Nat} {sg : Segment}
      {bt : BlockType} {b : List Instr} {L : LFrame} {W : List Val}
      (hc : seqAt body p = some c) (hsg : (segment c)[m]? = some sg)
      (ht : sg.term = some (.loop bt b))
      (hkind : StructKind (.loop bt b) L.bt L.loop L.tryT L.catches) (hlo : LoopOk f L)
      (hWl : W.length = L.arity) {vs : List Val} (hW : vs = L.outer ++ W) :
      HeadRep P host C body s f (seqLv body p ls) vs (.plain (.loop bt b))
        (expression (restAt c (m + 1)))
        (goto (entry body (p ++ [(m, 0)]) 0) (p.length + 1) (L :: ls) W s f)

theorem rep_head {body : Expr} {lv : Lv H} {s : Store H} {f : Frame} {vs : List Val}
    {a : Admin} {code : List Admin} {st : MState H}
    (hr : Rep P host C body lv s f vs (a :: code) st) (ha : a.val? = none) :
    HeadRep P host C body s f lv vs a code st := by
  generalize hcd : a :: code = code₀ at hr
  cases hr with
  | blk hc hsg hbody hne hpre =>
    rcases vals_cons_eq hcd.symm with ⟨w, V', rfl, rfl, -⟩ | ⟨rfl, hX⟩
    · simp at ha
    · rcases blk_head hne hX with ⟨x, sfx', rfl, rfl, rfl⟩ | ⟨rfl, t, ht, rfl, rfl⟩
      · exact .body hc hsg hbody ((seg_wf hsg).2 x (by simp [hbody])) (by simpa using hpre)
      · exact .term hc hsg ht (by simpa [hbody] using hpre)
  | blkIf hc hsg ht hpre hstk =>
    rcases vals_cons_eq hcd.symm with ⟨w, V', rfl, rfl, -⟩ | ⟨rfl, hX⟩
    · simp at ha
    · simp at hX; obtain ⟨rfl, rfl⟩ := hX; simp at hstk; subst hstk
      exact .blkIf hc hsg ht hpre
  | @fin _ _ _ _ _ V =>
    cases V with
    | nil => simp at hcd
    | cons w V' => simp [vals] at hcd; rw [hcd.1] at ha; simp at ha
  | lab hc hsg ht harm hkind hT hlo hW hin =>
    rcases vals_cons_eq hcd.symm with ⟨w, V', rfl, rfl, -⟩ | ⟨rfl, hX⟩
    · simp at ha
    · simp at hX; obtain ⟨rfl, rfl⟩ := hX; simp at hW
      exact .lab hc hsg ht harm hkind hT hlo hW hin
  | hnd hc hsg ht harm hkind hT hW hin =>
    rcases vals_cons_eq hcd.symm with ⟨w, V', rfl, rfl, -⟩ | ⟨rfl, hX⟩
    · simp at ha
    · simp at hX; obtain ⟨rfl, rfl⟩ := hX; simp at hW
      exact .hnd hc hsg ht harm hkind hT hW hin
  | hlab hnl hloop hin => simp at hcd; obtain ⟨rfl, rfl⟩ := hcd; exact .hlab rfl rfl hnl hloop hin
  | loopRe hc hsg ht hkind hlo hW hWl =>
    rcases vals_cons_eq hcd.symm with ⟨w, V', rfl, rfl, -⟩ | ⟨rfl, hX⟩
    · simp at ha
    · simp at hX; obtain ⟨rfl, rfl⟩ := hX; simp at hW
      exact .loopRe hc hsg ht hkind hlo hWl hW

theorem term_isTerminator {c : List Instr} {i : Nat} {sg : Segment} {t : Instr}
    (hsg : (segment c)[i]? = some sg) (ht : sg.term = some t) : isTerminator t = true :=
  ((segment_isSegmentation c).2.1 sg (List.mem_of_getElem? hsg)).2 t (by simp [ht])

theorem term_noncontrol {c : List Instr} {i : Nat} {sg : Segment} {t : Instr}
    (hsg : (segment c)[i]? = some sg) (ht : sg.term = some t)
    (hi : SingleThreaded.Det.famOf (.plain t) ≠ .control) : t = .unreachable := by
  have hseg := segment_isSegmentation c
  have hwf := (hseg.2.1 sg (List.mem_of_getElem? hsg)).2 t (by simp [ht])
  revert hi hwf
  unfold isTerminator
  split <;> simp [SingleThreaded.Det.famOf]

open Silmaril.Wasm.Cfg.Proofs.Machine in
theorem brTarget_eq (body : Expr) (p : List SeqStep) (l : LabelIdx) (L : LFrame)
    (ls : List LFrame) (V : List Val) (s : Store H) (f : Frame) :
    brTarget body p l.toNat L ls V s f =
      if L.loop then
        goto (resolveT (labels body p) l) (p.length - l.toNat) (L :: ls.drop (l.toNat + 1))
          (topVals L.arity V) s f
      else
        goto (resolveT (labels body p) l) (p.length - (l.toNat + 1)) (ls.drop (l.toNat + 1))
          (L.outer ++ topVals L.arity V) s f := by
  simp only [brTarget, resolveT_labels]

theorem brTarget_eq' (body : Expr) (p : List SeqStep) (k : Nat) (L : LFrame)
    (ls : List LFrame) (V : List Val) (s : Store H) (f : Frame) :
    brTarget body p k L ls V s f =
      if L.loop then
        goto ((labels body p).getD k .invalid) (p.length - k) (L :: ls.drop (k + 1))
          (topVals L.arity V) s f
      else
        goto ((labels body p).getD k .invalid) (p.length - (k + 1)) (ls.drop (k + 1))
          (L.outer ++ topVals L.arity V) s f := by
  simp only [brTarget, labels]

/-- The only rule for `br` at the head. -/
theorem run_br_inv {s s' : Store H} {f f' : Frame} {vs : List Val} {l : LabelIdx}
    {code : List Admin} {o : Out} (h : RunC P host C s f vs (.plain (.br l) :: code) s' f' o) :
    o = .br l.toNat vs ∧ s' = s ∧ f' = f := by
  cases h with
  | br => exact ⟨rfl, rfl, rfl⟩
  | simple hi => simp [SingleThreaded.Det.famOf] at hi
  | simpleTrap hi => simp [SingleThreaded.Det.famOf] at hi
  | brData hb => cases hb
  | val hv => simp [Admin.val?] at hv
  | returnCallRef hc => simp [Admin.IsReturnCallRef] at hc
  | returnCallRefNull hc => simp [Admin.IsReturnCallRef] at hc

/-- A `return_call_indirect` runs on its own: to a trap (of its `table.get` or `ref.cast`) or a
pending tail call, never falling through, whatever follows it. -/
theorem run_rci {s s' : Store H} {f f' : Frame} {vs : List Val} {x : TableIdx} {y : TypeIdx}
    {code : List Admin} {o : Out}
    (h : RunC P host C s f vs (.plain (.returnCallIndirect x y) :: code) s' f' o) :
    RunC P host C s f vs [.plain (.returnCallIndirect x y)] s' f' o ∧
      (o = .trap ∨ (∃ W a c, o = .tail W a c) ∨ ∃ W c, o = .tailNull W c) := by
  cases h with
  | returnCallIndirect h =>
    cases h with
    | simple hi h₁ h =>
      cases h with
      | simple hi' h₁' h' =>
        cases h' with
        | returnCallRef hc =>
          exact ⟨.returnCallIndirect (.simple hi h₁ (.simple hi' h₁' (.returnCallRef hc))),
            Or.inr (Or.inl ⟨_, _, _, rfl⟩)⟩
        | returnCallRefNull hc =>
          exact ⟨.returnCallIndirect (.simple hi h₁ (.simple hi' h₁' (.returnCallRefNull hc))),
            Or.inr (Or.inr ⟨_, _, rfl⟩)⟩
        | val hv => simp [Admin.val?] at hv
        | simple hi'' => simp [SingleThreaded.Det.famOf] at hi''
        | simpleTrap hi'' => simp [SingleThreaded.Det.famOf] at hi''
        | brData hb => cases hb
      | simpleTrap hi' h₁' =>
        exact ⟨.returnCallIndirect (.simple hi h₁ (.simpleTrap hi' h₁')), Or.inl rfl⟩
      | val hv => simp [Admin.val?] at hv
      | brData hb => cases hb
      | returnCallRef hc => simp [Admin.IsReturnCallRef] at hc
      | returnCallRefNull hc => simp [Admin.IsReturnCallRef] at hc
    | simpleTrap hi h₁ => exact ⟨.returnCallIndirect (.simpleTrap hi h₁), Or.inl rfl⟩
    | val hv => simp [Admin.val?] at hv
    | brData hb => cases hb
    | returnCallRef hc => simp [Admin.IsReturnCallRef] at hc
    | returnCallRefNull hc => simp [Admin.IsReturnCallRef] at hc
  | val hv => simp [Admin.val?] at hv
  | simple hi => simp [SingleThreaded.Det.famOf] at hi
  | simpleTrap hi => simp [SingleThreaded.Det.famOf] at hi
  | brData hb => cases hb
  | returnCallRef hc => simp [Admin.IsReturnCallRef] at hc
  | returnCallRefNull hc => simp [Admin.IsReturnCallRef] at hc

theorem brStep_X {s : Store H} {f : Frame} {us us' : List Val} {i : Instr} {X : List Admin}
    (h : BrStep s f us i us' X) : X = [] ∨ ∃ l, X = [.plain (.br l)] := by
  cases h <;> simp

open Silmaril.Wasm.Cfg.Proofs.Machine in
theorem seqAt_arm {body : Expr} {p : List SeqStep} {c : List Instr} {i : Nat} {sg : Segment}
    {t : Instr} {a : Nat} {c' : List Instr} (hc : seqAt body p = some c)
    (hsg : (segment c)[i]? = some sg) (ht : sg.term = some t) (harm : armOf t a = some c') :
    seqAt body (p ++ [(i, a)]) = some c' := by
  rw [seqAt_append]; simp [hc, hsg, ht, harm]

/-- The machine state after entering arm `a` stands for the arm's code. -/
theorem rep_arm {body : Expr} {p : List SeqStep} {c : List Instr} {i : Nat} {sg : Segment}
    {t : Instr} {a : Nat} {c' : List Instr} (ls : List LFrame) (L : LFrame) {s : Store H}
    {f : Frame} (us : List Val) (hc : seqAt body p = some c)
    (hsg : (segment c)[i]? = some sg) (ht : sg.term = some t) (harm : armOf t a = some c') :
    Rep P host C body (seqLv body (p ++ [(i, a)]) (L :: ls)) s f [] (vals us ++ expression c')
      (goto (entry body (p ++ [(i, a)]) 0) (p.length + 1) (L :: ls) us s f) := by
  have := rep_entry (P := P) (host := host) (C := C) (s := s) (f := f) 0 (L :: ls) [] us
    (seqAt_arm hc hsg ht harm)
  simpa [Proofs.Machine.restAt_zero] using this

theorem isLoopAt_kind {body : Expr} {p : List SeqStep} {c : List Instr} {m : Nat}
    {sg : Segment} {t : Instr} {bt : BlockType} {lp tt : Bool} {cs : List Catch}
    (hc : seqAt body p = some c) (hsg : (segment c)[m]? = some sg) (ht : sg.term = some t)
    (hk : StructKind t bt lp tt cs) : isLoopAt body p m = lp := by
  have hl := lookup_of hc hsg
  obtain ⟨sb, st⟩ := sg
  simp only at ht; subst ht
  cases hk <;> simp [isLoopAt, hl]

theorem loopOk_of_module {f f' : Frame} {L : LFrame} (hm : f'.module = f.module)
    (h : LoopOk f L) : LoopOk f' L := by
  simpa [LoopOk, hm] using h

theorem kind_loop_false {t : Instr} {bt : BlockType} {lp : Bool} {cs : List Catch}
    (h : StructKind t bt lp true cs) : lp = false := by
  cases h; rfl

theorem kind_arm_loop {bt : BlockType} {b : List Instr}
    {a : Nat} {c' : List Instr} (harm : armOf (.loop bt b) a = some c') : a = 0 := by
  rcases a with _ | _ | a <;> simp_all [armOf]

theorem brTarget_zero_out (body : Expr) (p : List SeqStep) (m a : Nat) (L : LFrame)
    (ls : List LFrame) (V : List Val) (s : Store H) (f : Frame)
    (hnl : isLoopAt body p m = false) (hloop : L.loop = false) :
    brTarget body (p ++ [(m, a)]) 0 L (L :: ls) V s f =
      goto (entry body p (m + 1)) p.length ls (L.outer ++ topVals L.arity V) s f := by
  simp only [brTarget, hloop, Bool.false_eq_true, ↓reduceIte, List.reverse_append,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, labelsRev,
    List.reverse_reverse, hnl, List.getD_cons_zero, List.length_append, List.length_cons,
    List.length_nil, Nat.add_sub_cancel, List.drop_succ_cons, List.drop_zero]
  exact cont_arm body p m a L ls _ s f

theorem brTarget_zero_loop (body : Expr) (p : List SeqStep) (m a : Nat) (L : LFrame)
    (ls : List LFrame) (V : List Val) (s : Store H) (f : Frame)
    (hnl : isLoopAt body p m = true) (hloop : L.loop = true) :
    brTarget body (p ++ [(m, a)]) 0 L (L :: ls) V s f =
      goto (entry body (p ++ [(m, a)]) 0) (p.length + 1) (L :: ls) (topVals L.arity V) s f := by
  simp [brTarget, hloop, labelsRev, hnl]

/-- **Completeness at every level**: a region run of a code that stands for machine state `st`
is matched by machine runs from `st`, as `Reach` says. -/
theorem complete {body : Expr} {s s' : Store H} {f f' : Frame} {vs : List Val}
    {code : List Admin} {o : Out} (h : RunC P host C s f vs code s' f' o) :
    ∀ (lv : Lv H) (st : MState H) (vs₀ : List Val) (code₀ : List Admin), vs₀ = vs →
      code₀ = code → Rep P host C body lv s f vs₀ code₀ st → Reach P host C body lv st s' f' o := by
  induction h with
  | nil =>
    intro lv st vs₀ code₀ hvs hcd hr
    cases hr with
    | fin => subst hvs; simp only [List.nil_eq, List.map_eq_nil_iff, vals] at hcd; subst hcd
             simp [Reach, seqLv]; exact .refl
    | blk hc hsg hbody hne hpre =>
      simp only [List.nil_eq, List.append_eq_nil_iff, vals, expression, List.map_eq_nil_iff] at hcd
      rcases hne with hne | hne
      · exact absurd hcd.2.1.1 hne
      · rw [Option.isSome_iff_exists] at hne; obtain ⟨t, ht⟩ := hne; simp [ht] at hcd
    | _ => simp at hcd
  | val hv h ih =>
    intro lv st vs₀ code₀ hvs hcd hr
    subst hvs
    cases hr with
    | blk hc hsg hbody hne hpre =>
      rcases vals_cons_eq hcd with ⟨w, V', rfl, rfl, rfl⟩ | ⟨rfl, hX⟩
      · simp at hv; subst hv
        exact ih _ _ _ _ rfl rfl (Rep.blk hc hsg hbody hne (by simpa using hpre))
      · rcases blk_head hne hX with ⟨x, sfx', rfl, rfl, rfl⟩ | ⟨rfl, t, ht, rfl, rfl⟩
        · exact blk_adv hc hsg hbody (by simpa using hpre) (.val hv .nil)
            (fun lv st hr => ih lv st _ _ rfl rfl hr)
        · rw [term_val_none hsg ht] at hv; cases hv
    | blkIf hc hsg ht hpre hstk =>
      rcases vals_cons_eq hcd with ⟨w, V', rfl, rfl, rfl⟩ | ⟨rfl, hX⟩
      · simp at hv; subst hv
        exact ih _ _ _ _ rfl rfl (Rep.blkIf hc hsg ht hpre (by simpa using hstk))
      · simp at hX; rw [← hX.1] at hv; simp [Admin.val?] at hv
    | @fin p ls _ _ _ V =>
      cases V with
      | nil => simp at hcd
      | cons w V' =>
        simp [vals] at hcd; obtain ⟨rfl, rfl⟩ := hcd
        simp at hv; subst hv
        simpa using ih _ _ _ _ rfl rfl (Rep.fin (P := P) (host := host) (C := C) (body := body) (p := p)
          (ls := ls) (V := V'))
    | lab hc hsg ht harm hkind hT hlo hW hin =>
      rcases vals_cons_eq hcd with ⟨w, V', rfl, rfl, rfl⟩ | ⟨rfl, hX⟩
      · simp at hv; subst hv
        exact ih _ _ _ _ rfl rfl (Rep.lab hc hsg ht harm hkind hT hlo (by simpa using hW) hin)
      · simp at hX; rw [← hX.1] at hv; simp [Admin.val?] at hv
    | hnd hc hsg ht harm hkind hT hW hin =>
      rcases vals_cons_eq hcd with ⟨w, V', rfl, rfl, rfl⟩ | ⟨rfl, hX⟩
      · simp at hv; subst hv
        exact ih _ _ _ _ rfl rfl (Rep.hnd hc hsg ht harm hkind hT (by simpa using hW) hin)
      · simp at hX; rw [← hX.1] at hv; simp [Admin.val?] at hv
    | hlab hin => simp at hcd; rw [← hcd.1] at hv; simp [Admin.val?] at hv
    | loopRe hc hsg ht hkind hlo hW hWl =>
      rcases vals_cons_eq hcd with ⟨w, V', rfl, rfl, rfl⟩ | ⟨rfl, hX⟩
      · simp at hv; subst hv
        simpa using ih _ _ _ _ rfl rfl (Rep.loopRe hc hsg ht hkind hlo (by simpa using hW) hWl)
      · simp at hX; rw [← hX.1] at hv; simp [Admin.val?] at hv
  | simple hi h₁ h ih =>
    intro lv st vs₀ code₀ hvs hcd hr
    subst hvs hcd
    cases rep_head hr (val_none_of_noncontrol hi) with
    | body hc hsg hbody hx hpre =>
      exact blk_adv hc hsg hbody hpre (.simple hi h₁ .nil) (fun lv st hr => ih lv st _ _ rfl rfl hr)
    | term hc hsg ht hpre =>
      cases term_noncontrol hsg ht hi
      exact (steps_unreachable_not_vals h₁).elim
    | blkIf => simp [SingleThreaded.Det.famOf] at hi
    | loopRe => simp [SingleThreaded.Det.famOf] at hi
  | simpleTrap hi h₁ =>
    intro lv st vs₀ code₀ hvs hcd hr
    subst hvs hcd
    cases rep_head hr (val_none_of_noncontrol hi) with
    | body hc hsg hbody hx hpre =>
      refine .single (MStepC.bodyTrap (lookup_of hc hsg) ?_)
      rw [hbody]
      simpa [expression] using Proofs.Region.run_append hpre (by
        simp only [ThenC]; exact .simpleTrap hi h₁)
    | term hc hsg ht hpre =>
      exact .single (MStepC.termTrap (lookup_of hc hsg) ht hpre (.simpleTrap hi h₁))
    | blkIf => simp [SingleThreaded.Det.famOf] at hi
    | loopRe => simp [SingleThreaded.Det.famOf] at hi
  | trap =>
    intro lv st vs₀ code₀ hvs hcd hr
    subst hvs hcd
    cases rep_head hr rfl
  | br =>
    intro lv st vs₀ code₀ hvs hcd hr
    subst hvs hcd
    cases rep_head hr rfl with
    | body hc hsg hbody hx => simp [isTerminator] at hx
    | term hc hsg ht hpre =>
      refine ⟨fun L hL har hlo => ?_, fun hk => ⟨[], _, rfl,
        .single (MStepC.brOut (lookup_of hc hsg) ht hpre (by simpa [seqLv] using hk))⟩⟩
      rw [brTarget_eq]
      exact .single (MStepC.br (lookup_of hc hsg) ht hpre hL (by simpa [seqLv] using har) hlo)
  | ret =>
    intro lv st vs₀ code₀ hvs hcd hr
    subst hvs hcd
    cases rep_head hr rfl with
    | body hc hsg hbody hx => simp [isTerminator] at hx
    | term hc hsg ht hpre => exact ⟨[], _, rfl, .single (MStepC.ret (lookup_of hc hsg) ht hpre)⟩
  | @brIf s s' f f' ws k l code o h ih =>
    intro lv st vs₀ code₀ hvs hcd hr
    subst hvs hcd
    cases rep_head hr rfl with
    | body hc hsg hbody hx => simp [isTerminator] at hx
    | @term p ls c i sg t stk₀ s₀ f₀ _ hc hsg ht hpre =>
      by_cases hk : k = 0
      · subst hk
        simp only [↓reduceIte, List.nil_append] at h
        refine reach_step (MStepC.brIfNot (lookup_of hc hsg) ht hpre) ?_
        have hre := rep_entry (P := P) (host := host) (C := C) (s := s) (f := f) (i + 1) ls ws [] hc
        exact ih _ _ _ _ rfl rfl (by simpa using hre)
      · simp only [hk, ↓reduceIte, List.singleton_append] at h
        obtain ⟨rfl, rfl, rfl⟩ := run_br_inv h
        refine ⟨fun L hL har hlo => ?_, fun hk' => ⟨[], _, rfl,
          .single (MStepC.brIfOut (lookup_of hc hsg) ht hpre hk (by simpa [seqLv] using hk'))⟩⟩
        rw [brTarget_eq]
        exact .single (MStepC.brIfTaken (lookup_of hc hsg) ht hpre hk hL
          (by simpa [seqLv] using har) hlo)
  | @throw s f ws vs x ta ti ts code ht he hn =>
    intro lv st vs₀ code₀ hvs hcd hr
    subst hvs hcd
    cases rep_head hr rfl with
    | body hc hsg hbody hx => simp [isTerminator] at hx
    | term hc hsg htm hpre =>
      have hth : RunC P host C s f (ws ++ vs) [.plain (.throw x)] (s.addExn ⟨ta, vs⟩) f
          (.throw s.exns.length) := RunC.throw ht he hn
      refine ⟨fun j L us l L' hpass hL hT hc' hL' har hlo => ?_, fun hall => ?_,
        fun j L us l hpass hL hT hc' hout => ?_⟩
      · rw [brTarget_eq']
        exact .single (MStepC.catch_ (lookup_of hc hsg) htm trivial hpre hth hpass hL hT hc' hL'
          har hlo)
      · exact .single (MStepC.raise (lookup_of hc hsg) htm trivial hpre hth hall)
      · exact .single (MStepC.catchOut (lookup_of hc hsg) htm trivial hpre hth hpass hL hT hc'
          (by simpa [seqLv] using hout))
  | throwRefNull =>
    intro lv st vs₀ code₀ hvs hcd hr
    subst hvs hcd
    cases rep_head hr rfl with
    | body hc hsg hbody hx => simp [isTerminator] at hx
    | term hc hsg htm hpre =>
      exact .single (MStepC.termTrap (lookup_of hc hsg) htm hpre (.throwRefNull (code := [])))
  | @throwRefExn s f ws a code =>
    intro lv st vs₀ code₀ hvs hcd hr
    subst hvs hcd
    cases rep_head hr rfl with
    | body hc hsg hbody hx => simp [isTerminator] at hx
    | term hc hsg htm hpre =>
      have hth : RunC P host C s f (ws ++ [.ref (.exn a)]) [.plain .throwRef] s f (.throw a) :=
        RunC.throwRefExn
      refine ⟨fun j L us l L' hpass hL hT hc' hL' har hlo => ?_, fun hall => ?_,
        fun j L us l hpass hL hT hc' hout => ?_⟩
      · rw [brTarget_eq']
        exact .single (MStepC.catch_ (lookup_of hc hsg) htm trivial hpre hth hpass hL hT hc' hL'
          har hlo)
      · exact .single (MStepC.raise (lookup_of hc hsg) htm trivial hpre hth hall)
      · exact .single (MStepC.catchOut (lookup_of hc hsg) htm trivial hpre hth hpass hL hT hc'
          (by simpa [seqLv] using hout))
  | @brData s s' f f' ws us us' i X code o hb h ih =>
    intro lv st vs₀ code₀ hvs hcd hr
    subst hvs hcd
    cases rep_head hr (brStep_val_none hb) with
    | body hc hsg hbody hx => cases hb <;> simp [isTerminator] at hx
    | @term p ls c i' sg t stk₀ s₀ f₀ _ hc hsg ht hpre =>
      rcases brStep_X hb with rfl | ⟨l, rfl⟩
      · refine reach_step (MStepC.brDataNot (lookup_of hc hsg) ht hpre hb) ?_
        have hre := rep_entry (P := P) (host := host) (C := C) (s := s) (f := f) (i' + 1) ls
          (ws ++ us') [] hc
        exact ih _ _ _ _ rfl rfl (by simpa using hre)
      · simp only [List.singleton_append] at h
        obtain ⟨rfl, rfl, rfl⟩ := run_br_inv h
        refine ⟨fun L hL har hlo => ?_, fun hk' => ⟨[], _, rfl,
          .single (MStepC.brDataOut (ws := ws) (us := us) (us' := us') (lookup_of hc hsg) ht hpre hb
            (by simpa [seqLv] using hk'))⟩⟩
        rw [brTarget_eq]
        exact .single (MStepC.brDataTaken (ws := ws) (us := us) (us' := us') (lookup_of hc hsg) ht
          hpre hb hL
          (by simpa [seqLv] using har) hlo)
    | blkIf => cases hb
    | loopRe => cases hb
  | @block s s' f f' ws us bt b t₁ t₂ code o hbt hm h ih =>
    intro lv st vs₀ code₀ hvs hcd hr
    subst hvs hcd
    cases rep_head hr rfl with
    | body hc hsg hbody hx => simp [isTerminator] at hx
    | @term p ls c i sg t stk₀ s₀ f₀ _ hc hsg ht hpre =>
      refine reach_step (MStepC.enter (a := 0) (lookup_of hc hsg) ht rfl .block hpre
        (.plain (by intros; simp)) hbt hm) ?_
      exact ih _ _ _ _ rfl rfl (Rep.lab (V := []) (L := ⟨t₂.length, ws, false, false, [], bt⟩)
        hc hsg ht rfl .block rfl (by simp [LoopOk]) (by simp)
        (rep_arm ls _ us hc hsg ht rfl))
    | @blkIf p ls c i sg bt' te ee k stk₀ ws' s₀ f₀ hc hsg ht hpre =>
      by_cases hk : k = 0
      · subst hk
        simp only [↓reduceIte] at ih ⊢
        refine reach_step (MStepC.enter (a := 1) (lookup_of hc hsg) ht rfl .if_ hpre
          CondArm.ifFalse hbt hm) ?_
        exact ih _ _ _ _ rfl rfl (Rep.lab (V := []) (L := ⟨t₂.length, ws, false, false, [], bt⟩)
          hc hsg ht rfl .if_ rfl (by simp [LoopOk]) (by simp)
          (rep_arm ls _ us hc hsg ht rfl))
      · simp only [hk, ↓reduceIte] at ih ⊢
        refine reach_step (MStepC.enter (a := 0) (lookup_of hc hsg) ht rfl .if_ hpre
          (CondArm.ifTrue hk) hbt hm) ?_
        exact ih _ _ _ _ rfl rfl (Rep.lab (V := []) (L := ⟨t₂.length, ws, false, false, [], bt⟩)
          hc hsg ht rfl .if_ rfl (by simp [LoopOk]) (by simp)
          (rep_arm ls _ us hc hsg ht rfl))
  | @if_ s s' f f' ws k bt te ee code o h ih =>
    intro lv st vs₀ code₀ hvs hcd hr
    subst hvs hcd
    cases rep_head hr rfl with
    | body hc hsg hbody hx => simp [isTerminator] at hx
    | term hc hsg ht hpre =>
      exact ih _ _ _ _ rfl rfl (by simpa using Rep.blkIf (V := []) hc hsg ht hpre (by simp))
  | @tryTable s s' f f' ws us bt cs b t₁ t₂ code o hbt hm h ih =>
    intro lv st vs₀ code₀ hvs hcd hr
    subst hvs hcd
    cases rep_head hr rfl with
    | body hc hsg hbody hx => simp [isTerminator] at hx
    | @term p ls c i sg t stk₀ s₀ f₀ _ hc hsg ht hpre =>
      refine reach_step (MStepC.enter (a := 0) (lookup_of hc hsg) ht rfl .tryTable hpre
        (.plain (by intros; simp)) hbt hm) ?_
      exact ih _ _ _ _ rfl rfl (Rep.hnd (V := []) (L := ⟨t₂.length, ws, false, true, cs, bt⟩)
        hc hsg ht rfl .tryTable rfl (by simp)
        (Rep.hlab (isLoopAt_kind hc hsg ht .tryTable) rfl (rep_arm ls _ us hc hsg ht rfl)))
  | @loop s s' f f' ws us bt b t₁ t₂ code o hbt hm h ih =>
    intro lv st vs₀ code₀ hvs hcd hr
    subst hvs hcd
    cases rep_head hr rfl with
    | body hc hsg hbody hx => simp [isTerminator] at hx
    | @term p ls c i sg t stk₀ s₀ f₀ _ hc hsg ht hpre =>
      refine reach_step (MStepC.enter (a := 0) (lookup_of hc hsg) ht rfl .loop hpre
        (.plain (by intros; simp)) hbt hm) ?_
      exact ih _ _ _ _ rfl rfl (Rep.lab (V := []) (L := ⟨t₁.length, ws, true, false, [], bt⟩)
        hc hsg ht rfl .loop rfl (fun _ => ⟨t₁, t₂, hbt, rfl⟩) (by simp)
        (rep_arm ls _ us hc hsg ht rfl))
    | @loopRe p ls c m sg _ _ L W hc hsg ht hkind hlo hWl _ hW =>
      have hL : L.loop = true ∧ L.bt = bt ∧ L.tryT = false ∧ L.catches = [] := by
        generalize hl : L.loop = lp at hkind
        generalize hb : L.bt = bb at hkind
        generalize hy : L.tryT = ty at hkind
        generalize hcs : L.catches = cc at hkind
        cases hkind; exact ⟨rfl, rfl, rfl, rfl⟩
      obtain ⟨hlp, hbb, hty, hcc⟩ := hL
      obtain ⟨t₁', t₂', hbt', hlen⟩ := hlo hlp
      rw [hbb, hbt] at hbt'
      simp only [Option.some.injEq, Prod.mk.injEq] at hbt'
      obtain ⟨rfl, rfl⟩ := hbt'
      have hl2 : us.length = W.length := by rw [hm, hlen, hWl]
      obtain ⟨rfl, rfl⟩ := List.append_inj' hW hl2
      have hin := rep_arm (P := P) (host := host) (C := C) (s := s) (f := f) (a := 0) ls L us hc hsg ht rfl
      have := Rep.lab (V := []) (vs := L.outer) hc hsg ht rfl hkind hty hlo (by simp) hin
      rw [hlp] at this
      simp only [↓reduceIte] at this
      rw [hlen] at h ih
      exact ih _ _ _ _ rfl rfl (by simpa using this)
  | @labelNormal s s₁ s' f f₁ f' vs us n cont inner code o hin h ih_in ih =>
    intro lv st vs₀ code₀ hvs hcd hr
    subst hvs hcd
    cases rep_head hr rfl with
    | @lab p ls c m a sg t c' L _ _ hc hsg ht harm hkind hT hlo _ hW hrin =>
      subst hW
      have h1 : MRun P host C body st _ := ih_in _ _ _ _ rfl rfl hrin
      rw [show (seqLv body (p ++ [(m, a)]) (L :: ls)).cont us s₁ f₁ = _ from
        seqLv_cont_arm body p m a L ls us s₁ f₁] at h1
      have hre := rep_entry (P := P) (host := host) (C := C) (s := s₁) (f := f₁) (m + 1) ls
        (L.outer ++ us) [] hc
      exact reach_mono h1 (ih _ _ _ _ rfl rfl (by simpa using hre))
    | @hlab p ls m a L _ _ _ hv _ hcode hnl hloop hrin =>
      subst hv hcode
      have h1 : MRun P host C body st _ := ih_in _ _ _ _ rfl rfl hrin
      rw [show (seqLv body (p ++ [(m, a)]) (L :: ls)).cont us s₁ f₁ = _ from
        seqLv_cont_arm body p m a L ls us s₁ f₁] at h1
      cases h
      show MRun P host C body st ((hlLv body p m a L ls).cont us s₁ f₁)
      rw [hlLv_cont]; simpa using h1
  | @labelBr0 s s₁ s' f f₁ f' vs us₁ us₂ n cont inner code o hin hn h ih_in ih =>
    intro lv st vs₀ code₀ hvs hcd hr
    subst hvs hcd
    have hmod := Proofs.Machine.run_module hin
    have htop : topVals n (us₁ ++ us₂) = us₂ := by
      simp [topVals, ← hn]
    cases rep_head hr rfl with
    | @lab p ls c m a sg t c' L _ _ hc hsg ht harm hkind hT hlo _ hW hrin =>
      subst hW
      have hb := (ih_in _ _ _ _ rfl rfl hrin).1 L (by simp [seqLv]) (by simp [brVals, seqLv]; omega)
        (loopOk_of_module hmod hlo)
      simp only [seqLv, List.nil_append, brVals] at hb
      have hnl := isLoopAt_kind hc hsg ht hkind
      cases hlp : L.loop
      · rw [brTarget_zero_out body p m a L ls _ s₁ f₁ (hnl.trans hlp) hlp, htop] at hb
        simp only [hlp, Bool.false_eq_true, ↓reduceIte, expression, List.map_nil,
          List.append_nil] at h ih
        have hre := rep_entry (P := P) (host := host) (C := C) (s := s₁) (f := f₁) (m + 1) ls L.outer us₂ hc
        exact reach_mono hb.to_reflTransGen (ih _ _ _ _ rfl rfl hre)
      · rw [brTarget_zero_loop body p m a L ls _ s₁ f₁ (hnl.trans hlp) hlp, htop] at hb
        obtain ⟨cb, rfl, -, -⟩ := Proofs.Machine.structKind_loop (hlp ▸ hkind)
        cases kind_arm_loop harm
        simp only [hlp, ↓reduceIte, expression, List.map_cons, List.map_nil,
          List.singleton_append, List.append_assoc] at h ih
        have hre := Rep.loopRe (P := P) (host := host) (C := C) (s := s₁) (ls := ls) (vs := L.outer)
          (V := us₂)
          (W := us₂) hc hsg ht hkind (loopOk_of_module hmod hlo) rfl (by omega)
        exact reach_mono hb.to_reflTransGen
          (ih _ _ _ _ rfl rfl (by simpa [expression] using hre))
    | @hlab p ls m a L _ _ _ hv _ hcode hnl hloop hrin =>
      subst hv hcode
      have hb := (ih_in _ _ _ _ rfl rfl hrin).1 L (by simp [seqLv]) (by simp [brVals, seqLv]; omega)
        (by simp [LoopOk, hloop])
      simp only [seqLv, List.nil_append, brVals] at hb
      rw [brTarget_zero_out body p m a L ls _ s₁ f₁ hnl hloop, htop] at hb
      obtain ⟨rfl, rfl, rfl⟩ := run_vals_only (by simpa [expression] using h)
      show MRun P host C body st ((hlLv body p m a L ls).cont us₂ _ _)
      rw [hlLv_cont]; simpa using hb.to_reflTransGen
  | @labelBrSucc s s₁ f f₁ vs us n l cont inner code hin ih_in =>
    intro lv st vs₀ code₀ hvs hcd hr
    subst hvs hcd
    cases rep_head hr rfl with
    | @lab p ls c m a sg t c' L _ _ hc hsg ht harm hkind hT hlo _ hW hrin =>
      subst hW
      have ih := ih_in _ _ _ _ rfl rfl hrin
      refine ⟨fun L' hL' har hlo' => ?_, fun hk => ?_⟩
      · have hb := ih.1 L' (by simpa [seqLv] using hL')
          (by simpa [brVals, seqLv] using har) hlo'
        simpa [seqLv, brVals, brTarget_succ] using hb
      · obtain ⟨W, stk, he, hm⟩ := ih.2 (by simp [seqLv] at hk ⊢; omega)
        rw [he]; exact ⟨_, stk, (List.append_assoc _ _ _).symm, hm⟩
    | @hlab p ls m a L _ _ _ hv _ hcode hnl hloop hrin =>
      subst hv hcode
      have ih := ih_in _ _ _ _ rfl rfl hrin
      refine ⟨fun L' hL' har hlo' => ?_, fun hk => ?_⟩
      · have hb := ih.1 L' (by simpa [seqLv, hlLv] using hL')
          (by simpa [brVals, seqLv, hlLv] using har) hlo'
        simpa [seqLv, hlLv, brVals, brTarget_succ] using hb
      · obtain ⟨W, stk, he, hm⟩ := ih.2 (by simp [seqLv, hlLv] at hk ⊢; omega)
        rw [he]; exact ⟨_, stk, (List.append_assoc _ _ _).symm, hm⟩
  | @labelRet s s₁ f f₁ vs us n cont inner code hin ih_in =>
    intro lv st vs₀ code₀ hvs hcd hr
    subst hcd hvs
    cases rep_head hr rfl with
    | lab hc hsg ht harm hkind hT hlo hW hrin =>
      obtain ⟨W, stk, rfl, hm⟩ := ih_in _ _ _ _ rfl rfl hrin
      exact ⟨vs₀ ++ W, stk, by simp, hm⟩
    | hlab hv hcode hnl hloop hrin =>
      obtain ⟨W, stk, rfl, hm⟩ := ih_in _ _ _ _ rfl rfl hrin
      exact ⟨vs₀ ++ W, stk, by simp, hm⟩
  | labelTrap hin ih_in =>
    intro lv st vs₀ code₀ hvs hcd hr
    subst hvs hcd
    cases rep_head hr rfl with
    | lab hc hsg ht harm hkind hT hlo hW hrin =>
      have := ih_in _ _ _ _ rfl rfl hrin; exact this
    | hlab hv hcode hnl hloop hrin =>
      have := ih_in _ _ _ _ rfl rfl hrin; exact this
  | @labelThrow s s₁ f f₁ vs n cont inner code a hin ih_in =>
    intro lv st vs₀ code₀ hvs hcd hr
    subst hvs hcd
    cases rep_head hr rfl with
    | @lab p ls c m a' sg t c' L _ _ hc hsg ht harm hkind hT hlo _ hW hrin =>
      obtain ⟨hcatch, hraise, hcout⟩ := ih_in _ _ _ _ rfl rfl hrin
      refine ⟨fun j L₀ us l L' hpass hL hT' hc' hL' har hlo' => ?_, fun hall => ?_,
        fun j L₀ us l hpass hL hT' hc' hout => ?_⟩
      rotate_left 2
      · exact hcout (j + 1) L₀ us l
          (fun k L₁ hk hL₁ hT₁ => by
            cases k with
            | zero => simp [seqLv] at hL₁; subst hL₁; rw [hT] at hT₁; cases hT₁
            | succ k => exact hpass k L₁ (by omega) (by simpa [seqLv] using hL₁) hT₁)
          (by simpa [seqLv] using hL) hT' hc' (by simp [seqLv] at hout ⊢; omega)
      · have hb := hcatch (j + 1) L₀ us l L'
          (fun k L₁ hk hL₁ hT₁ => by
            cases k with
            | zero => simp [seqLv] at hL₁; subst hL₁; rw [hT] at hT₁; cases hT₁
            | succ k => exact hpass k L₁ (by omega) (by simpa [seqLv] using hL₁) hT₁)
          (by simpa [seqLv] using hL) hT' hc'
          (by simpa [seqLv, show j + 1 + 1 + l.toNat = (j + 1 + l.toNat) + 1 by omega] using hL')
          (by simpa [seqLv] using har) hlo'
        simpa [seqLv, show j + 1 + 1 + l.toNat = (j + 1 + l.toNat) + 1 by omega, brTarget_succ]
          using hb
      · refine hraise (fun k L₁ hL₁ hT₁ => ?_)
        cases k with
        | zero => simp [seqLv] at hL₁; subst hL₁; rw [hT] at hT₁; cases hT₁
        | succ k => exact hall k L₁ (by simpa [seqLv] using hL₁) hT₁
    | hlab hv hcode hnl hloop hrin =>
      have := ih_in _ _ _ _ rfl rfl hrin; exact this
  | @handlerNormal s s₁ s' f f₁ f' vs us n cs inner code o hin h ih_in ih =>
    intro lv st vs₀ code₀ hvs hcd hr
    subst hvs hcd
    cases rep_head hr rfl with
    | @hnd p ls c m a sg t c' L _ _ hc hsg ht harm hkind hT _ hW hrin =>
      subst hW
      have h1 : MRun P host C body st _ := ih_in _ _ _ _ rfl rfl hrin
      rw [hlLv_cont] at h1
      have hre := rep_entry (P := P) (host := host) (C := C) (s := s₁) (f := f₁) (m + 1) ls
        (L.outer ++ us) [] hc
      exact reach_mono h1 (ih _ _ _ _ rfl rfl (by simpa using hre))
  | @handlerBr s s₁ f f₁ vs us n l cs inner code hin ih_in =>
    intro lv st vs₀ code₀ hvs hcd hr
    subst hvs hcd
    cases rep_head hr rfl with
    | @hnd p ls c m a sg t c' L _ _ hc hsg ht harm hkind hT _ hW hrin =>
      subst hW
      have ih := ih_in _ _ _ _ rfl rfl hrin
      refine ⟨fun L' hL' har hlo' => ?_, fun hk => ?_⟩
      · have hb := ih.1 L' (by simpa [seqLv, hlLv] using hL')
          (by simpa [seqLv, hlLv] using har) hlo'
        simpa [seqLv, hlLv] using hb
      · obtain ⟨W, stk, he, hm⟩ := ih.2 (by simpa [seqLv, hlLv] using hk)
        rw [he]; exact ⟨_, stk, (List.append_assoc _ _ _).symm, hm⟩
  | @handlerRet s s₁ f f₁ vs us n cs inner code hin ih_in =>
    intro lv st vs₀ code₀ hvs hcd hr
    subst hcd hvs
    cases rep_head hr rfl with
    | hnd hc hsg ht harm hkind hT hW hrin =>
      obtain ⟨W, stk, rfl, hm⟩ := ih_in _ _ _ _ rfl rfl hrin
      exact ⟨vs₀ ++ W, stk, by simp, hm⟩
  | handlerTrap hin ih_in =>
    intro lv st vs₀ code₀ hvs hcd hr
    subst hvs hcd
    cases rep_head hr rfl with
    | hnd hc hsg ht harm hkind hT hW hrin =>
      have := ih_in _ _ _ _ rfl rfl hrin; exact this
  | @handlerCatch s s₁ f f₁ vs us n a l cs inner code hin hc' ih_in =>
    intro lv st vs₀ code₀ hvs hcd hr
    subst hvs hcd
    cases rep_head hr rfl with
    | @hnd p ls c m a' sg t c' L _ _ hc hsg ht harm hkind hT _ hW hrin =>
      subst hW
      have ih := ih_in _ _ _ _ rfl rfl hrin
      refine ⟨fun L' hL' har hlo' => ?_, fun hk => ?_⟩
      · have hb := ih.1 0 L us l L'
          (fun k _ hk => absurd hk (Nat.not_lt_zero k)) (by simp [hlLv]) hT hc'
          (by rw [show 0 + 1 + l.toNat = l.toNat + 1 by omega]; simpa [hlLv, seqLv] using hL')
          (by simpa [seqLv, hlLv] using har) hlo'
        rw [show 0 + 1 + l.toNat = l.toNat + 1 by omega] at hb
        simpa [seqLv, hlLv, brTarget_succ] using hb
      · exact ⟨[], _, rfl, ih.2.2 0 L us l (fun k _ hk => absurd hk (Nat.not_lt_zero k))
          (by simp [hlLv]) hT hc' (by simp [hlLv, seqLv] at hk ⊢; omega)⟩
  | @handlerRethrow s s₁ f f₁ vs n a cs inner code hin hc' ih_in =>
    intro lv st vs₀ code₀ hvs hcd hr
    subst hvs hcd
    cases rep_head hr rfl with
    | @hnd p ls c m a' sg t c' L _ _ hc hsg ht harm hkind hT _ hW hrin =>
      obtain ⟨hcatch, hraise, hcout⟩ := ih_in _ _ _ _ rfl rfl hrin
      refine ⟨fun j L₀ us l L' hpass hL hT' hc₀ hL' har hlo' => ?_, fun hall => ?_,
        fun j L₀ us l hpass hL hT' hc₀ hout => ?_⟩
      rotate_left 2
      · exact hcout (j + 1) L₀ us l
          (fun k L₁ hk hL₁ hT₁ => by
            cases k with
            | zero => simp [hlLv, seqLv] at hL₁; subst hL₁; exact hc'
            | succ k => exact hpass k L₁ (by omega) (by simpa [hlLv, seqLv] using hL₁) hT₁)
          (by simpa [hlLv, seqLv] using hL) hT' hc₀ (by simp [hlLv, seqLv] at hout ⊢; omega)
      · have hb := hcatch (j + 1) L₀ us l L'
          (fun k L₁ hk hL₁ hT₁ => by
            cases k with
            | zero => simp [hlLv, seqLv] at hL₁; subst hL₁; exact hc'
            | succ k => exact hpass k L₁ (by omega) (by simpa [hlLv, seqLv] using hL₁) hT₁)
          (by simpa [hlLv, seqLv] using hL) hT' hc₀
          (by simpa [hlLv, seqLv, show j + 1 + 1 + l.toNat = (j + 1 + l.toNat) + 1 by omega]
            using hL')
          (by simpa [hlLv, seqLv] using har) hlo'
        simpa [hlLv, seqLv, show j + 1 + 1 + l.toNat = (j + 1 + l.toNat) + 1 by omega,
          brTarget_succ] using hb
      · refine hraise (fun k L₁ hL₁ hT₁ => ?_)
        cases k with
        | zero => simp [hlLv, seqLv] at hL₁; subst hL₁; exact hc'
        | succ k => exact hall k L₁ (by simpa [hlLv, seqLv] using hL₁) hT₁
  | call hfi hty hn hcall hvs h ih =>
    intro lv st vs₀ code₀ hvs₀ hcd hr
    subst hvs₀ hcd
    cases rep_head hr rfl with
    | body hc hsg hbody hx hpre =>
      exact blk_adv hc hsg hbody hpre (.call hfi hty hn hcall hvs .nil)
        (fun lv st hr => ih lv st _ _ rfl rfl hr)
    | term hc hsg ht hpre => exact absurd (term_isTerminator hsg ht) (by simp [isTerminator])
  | callTrap hfi hty hn hcall =>
    intro lv st vs₀ code₀ hvs₀ hcd hr
    subst hvs₀ hcd
    cases rep_head hr rfl with
    | body hc hsg hbody hx hpre =>
      refine .single (MStepC.bodyTrap (lookup_of hc hsg) ?_)
      rw [hbody]
      simpa [expression] using Proofs.Region.run_append hpre (by
        simp only [ThenC]; exact .callTrap hfi hty hn hcall)
    | term hc hsg ht hpre => exact absurd (term_isTerminator hsg ht) (by simp [isTerminator])
  | @callThrow s s₁ f ws us x a t fi ps rs code hfi hty hn hcall =>
    intro lv st vs₀ code₀ hvs₀ hcd hr
    subst hvs₀ hcd
    cases rep_head hr rfl with
    | @body p ls c i sg pre sfx x' stk₀ s₀ f₀ _ hc hsg hbody hx hpre =>
      have hbr : RunC P host C s₀ f₀ stk₀ (expression sg.body) s₁ f (.throw t) := by
        rw [hbody]
        simpa [expression] using Proofs.Region.run_append hpre (by
          simp only [ThenC]; exact .callThrow hfi hty hn hcall)
      refine ⟨fun j L us l L' hpass hL hT hc' hL' har hlo => ?_, fun hall => ?_,
        fun j L us l hpass hL hT hc' hout => ?_⟩
      · rw [brTarget_eq']
        exact .single (MStepC.bodyCatch (lookup_of hc hsg) hbr hpass hL hT hc' hL' har hlo)
      · exact .single (MStepC.bodyRaise (lookup_of hc hsg) hbr hall)
      · exact .single (MStepC.bodyCatchOut (lookup_of hc hsg) hbr hpass hL hT hc'
          (by simpa [seqLv] using hout))
    | term hc hsg ht hpre => exact absurd (term_isTerminator hsg ht) (by simp [isTerminator])
  | callInd hres hfi hty hn hcall hvs h ih =>
    intro lv st vs₀ code₀ hvs₀ hcd hr
    subst hvs₀ hcd
    cases rep_head hr rfl with
    | body hc hsg hbody hx hpre =>
      exact blk_adv hc hsg hbody hpre (.callInd hres hfi hty hn hcall hvs .nil)
        (fun lv st hr => ih lv st _ _ rfl rfl hr)
    | term hc hsg ht hpre => exact absurd (term_isTerminator hsg ht) (by simp [isTerminator])
  | callIndTrap hres hfi hty hn hcall =>
    intro lv st vs₀ code₀ hvs₀ hcd hr
    subst hvs₀ hcd
    cases rep_head hr rfl with
    | body hc hsg hbody hx hpre =>
      refine .single (MStepC.bodyTrap (lookup_of hc hsg) ?_)
      rw [hbody]
      simpa [expression] using Proofs.Region.run_append hpre (by
        simp only [ThenC]; exact .callIndTrap hres hfi hty hn hcall)
    | term hc hsg ht hpre => exact absurd (term_isTerminator hsg ht) (by simp [isTerminator])
  | @callIndThrow s s₁ f ws us x y ad i fa t fi ps rs code hres hfi hty hn hcall =>
    intro lv st vs₀ code₀ hvs₀ hcd hr
    subst hvs₀ hcd
    cases rep_head hr rfl with
    | @body p ls c i sg pre sfx x' stk₀ s₀ f₀ _ hc hsg hbody hx hpre =>
      have hbr : RunC P host C s₀ f₀ stk₀ (expression sg.body) s₁ f (.throw t) := by
        rw [hbody]
        simpa [expression] using Proofs.Region.run_append hpre (by
          simp only [ThenC]; exact .callIndThrow hres hfi hty hn hcall)
      refine ⟨fun j L us l L' hpass hL hT hc' hL' har hlo => ?_, fun hall => ?_,
        fun j L us l hpass hL hT hc' hout => ?_⟩
      · rw [brTarget_eq']
        exact .single (MStepC.bodyCatch (lookup_of hc hsg) hbr hpass hL hT hc' hL' har hlo)
      · exact .single (MStepC.bodyRaise (lookup_of hc hsg) hbr hall)
      · exact .single (MStepC.bodyCatchOut (lookup_of hc hsg) hbr hpass hL hT hc'
          (by simpa [seqLv] using hout))
    | term hc hsg ht hpre => exact absurd (term_isTerminator hsg ht) (by simp [isTerminator])
  | callIndRes hres =>
    intro lv st vs₀ code₀ hvs₀ hcd hr
    subst hvs₀ hcd
    cases rep_head hr rfl with
    | body hc hsg hbody hx hpre =>
      refine .single (MStepC.bodyTrap (lookup_of hc hsg) ?_)
      rw [hbody]
      simpa [expression] using Proofs.Region.run_append hpre (by
        simp only [ThenC]; exact .callIndRes hres)
    | term hc hsg ht hpre => exact absurd (term_isTerminator hsg ht) (by simp [isTerminator])
  | callRef hfi hty hn hcall hvs h ih =>
    intro lv st vs₀ code₀ hvs₀ hcd hr
    subst hvs₀ hcd
    cases rep_head hr rfl with
    | body hc hsg hbody hx hpre =>
      exact blk_adv hc hsg hbody hpre (.callRef hfi hty hn hcall hvs .nil)
        (fun lv st hr => ih lv st _ _ rfl rfl hr)
    | term hc hsg ht hpre => exact absurd (term_isTerminator hsg ht) (by simp [isTerminator])
  | callRefTrap hfi hty hn hcall =>
    intro lv st vs₀ code₀ hvs₀ hcd hr
    subst hvs₀ hcd
    cases rep_head hr rfl with
    | body hc hsg hbody hx hpre =>
      refine .single (MStepC.bodyTrap (lookup_of hc hsg) ?_)
      rw [hbody]
      simpa [expression] using Proofs.Region.run_append hpre (by
        simp only [ThenC]; exact .callRefTrap hfi hty hn hcall)
    | term hc hsg ht hpre => exact absurd (term_isTerminator hsg ht) (by simp [isTerminator])
  | @callRefThrow s s₁ f ws us y fa t fi ps rs code hfi hty hn hcall =>
    intro lv st vs₀ code₀ hvs₀ hcd hr
    subst hvs₀ hcd
    cases rep_head hr rfl with
    | @body p ls c i sg pre sfx x' stk₀ s₀ f₀ _ hc hsg hbody hx hpre =>
      have hbr : RunC P host C s₀ f₀ stk₀ (expression sg.body) s₁ f (.throw t) := by
        rw [hbody]
        simpa [expression] using Proofs.Region.run_append hpre (by
          simp only [ThenC]; exact .callRefThrow hfi hty hn hcall)
      refine ⟨fun j L us l L' hpass hL hT hc' hL' har hlo => ?_, fun hall => ?_,
        fun j L us l hpass hL hT hc' hout => ?_⟩
      · rw [brTarget_eq']
        exact .single (MStepC.bodyCatch (lookup_of hc hsg) hbr hpass hL hT hc' hL' har hlo)
      · exact .single (MStepC.bodyRaise (lookup_of hc hsg) hbr hall)
      · exact .single (MStepC.bodyCatchOut (lookup_of hc hsg) hbr hpass hL hT hc'
          (by simpa [seqLv] using hout))
    | term hc hsg ht hpre => exact absurd (term_isTerminator hsg ht) (by simp [isTerminator])
  | callRefNull =>
    intro lv st vs₀ code₀ hvs₀ hcd hr
    subst hvs₀ hcd
    cases rep_head hr rfl with
    | body hc hsg hbody hx hpre =>
      refine .single (MStepC.bodyTrap (lookup_of hc hsg) ?_)
      rw [hbody]
      simpa [expression] using Proofs.Region.run_append hpre (by
        simp only [ThenC]; exact .callRefNull)
    | term hc hsg ht hpre => exact absurd (term_isTerminator hsg ht) (by simp [isTerminator])
  | returnCall hfi₀ =>
    intro lv st vs₀ code₀ hvs hcd hr
    subst hvs hcd
    cases rep_head hr rfl with
    | body hc hsg hbody hx => simp [isTerminator] at hx
    | term hc hsg ht hpre =>
      intro fi ps rs W₀ args fl s₃ st' hfi hty hargs hn hcall hend
      exact .single (MStepC.tail (lookup_of hc hsg) ht trivial hpre (.returnCall (code := []) hfi₀)
        hfi hty (by simpa [seqLv] using hargs) hn hcall hend)
  | @returnCallRef s f ws a₀ c code hc =>
    intro lv st vs₀ code₀ hvs hcd hr
    subst hvs hcd
    cases rep_head hr (Proofs.Region.isRetCallRef_val hc) with
    | term hc' hsg ht hpre =>
      obtain ⟨y, rfl⟩ := Proofs.Region.isRetCallRef_plain hc
      intro fi ps rs W₀ args fl s₃ st' hfi hty hargs hn hcall hend
      exact .single (MStepC.tail (lookup_of hc' hsg) ht trivial hpre
        (.returnCallRef (code := []) hc) hfi hty (by simpa [seqLv] using hargs) hn hcall hend)
    | body hc' hsg hbody hx =>
      obtain ⟨y, rfl⟩ := Proofs.Region.isRetCallRef_plain hc
      simp [isTerminator] at hx
    | _ => simp [Admin.IsReturnCallRef] at hc
  | @labelTail s s₁ f f₁ vs us n cont inner code a₀ c hin ih_in =>
    intro lv st vs₀ code₀ hvs hcd hr
    subst hvs hcd
    cases rep_head hr rfl with
    | lab hc hsg ht harm hkind hT hlo hW hrin =>
      subst hW
      intro fi ps rs W₀ args fl s₃ st' hfi hty hargs hn hcall hend
      exact ih_in _ _ _ _ rfl rfl hrin fi ps rs W₀ args fl s₃ st' hfi hty
        (by simpa [seqLv, brVals] using hargs) hn hcall hend
    | hlab hv hcode hnl hloop hrin =>
      subst hv
      intro fi ps rs W₀ args fl s₃ st' hfi hty hargs hn hcall hend
      exact ih_in _ _ _ _ rfl rfl hrin fi ps rs W₀ args fl s₃ st' hfi hty
        (by simpa [seqLv, hlLv, brVals] using hargs) hn hcall hend
  | @handlerTail s s₁ f f₁ vs us n cs inner code a₀ c hin ih_in =>
    intro lv st vs₀ code₀ hvs hcd hr
    subst hvs hcd
    cases rep_head hr rfl with
    | hnd hc hsg ht harm hkind hT hW hrin =>
      subst hW
      intro fi ps rs W₀ args fl s₃ st' hfi hty hargs hn hcall hend
      exact ih_in _ _ _ _ rfl rfl hrin fi ps rs W₀ args fl s₃ st' hfi hty
        (by simpa [seqLv, hlLv] using hargs) hn hcall hend
  | @returnCallRefNull s f ws c code hc =>
    intro lv st vs₀ code₀ hvs hcd hr
    subst hvs hcd
    cases rep_head hr (Proofs.Region.isRetCallRef_val hc) with
    | term hc' hsg ht hpre =>
      obtain ⟨y, rfl⟩ := Proofs.Region.isRetCallRef_plain hc
      exact .single (MStepC.tailNull (lookup_of hc' hsg) ht trivial hpre
        (.returnCallRefNull (code := []) hc))
    | body hc' hsg hbody hx =>
      obtain ⟨y, rfl⟩ := Proofs.Region.isRetCallRef_plain hc
      simp [isTerminator] at hx
    | _ => simp [Admin.IsReturnCallRef] at hc
  | @returnCallIndirect s s' f f' vs x y code o h _ =>
    intro lv st vs₀ code₀ hvs hcd hr
    subst hvs hcd
    obtain ⟨hth, ho⟩ := run_rci (.returnCallIndirect h)
    cases rep_head hr rfl with
    | body hc hsg hbody hx => simp [isTerminator] at hx
    | term hc hsg ht hpre =>
      rcases ho with rfl | ⟨W, a, c, rfl⟩ | ⟨W, c, rfl⟩
      · exact .single (MStepC.termTrap (lookup_of hc hsg) ht hpre hth)
      · intro fi ps rs W₀ args fl s₃ st' hfi hty hargs hn hcall hend
        exact .single (MStepC.tail (lookup_of hc hsg) ht trivial hpre hth hfi hty
          (by simpa [seqLv] using hargs) hn hcall hend)
      · exact .single (MStepC.tailNull (lookup_of hc hsg) ht trivial hpre hth)
  | labelTailNull hin ih_in =>
    intro lv st vs₀ code₀ hvs hcd hr
    subst hvs hcd
    cases rep_head hr rfl with
    | lab hc hsg ht harm hkind hT hlo hW hrin =>
      have := ih_in _ _ _ _ rfl rfl hrin; exact this
    | hlab hv hcode hnl hloop hrin =>
      have := ih_in _ _ _ _ rfl rfl hrin; exact this
  | handlerTailNull hin ih_in =>
    intro lv st vs₀ code₀ hvs hcd hr
    subst hvs hcd
    cases rep_head hr rfl with
    | hnd hc hsg ht harm hkind hT hW hrin =>
      have := ih_in _ _ _ _ rfl rfl hrin; exact this

end Silmaril.Wasm.Cfg.Proofs.MachineComplete

namespace Silmaril.Wasm.Cfg.Proofs.MachineComplete

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H}

/-- **Completeness from the CFG entry**: every region run of a function body that does not end
in a branch out of the body is a machine run from the initial state to a sink, ending as `Ends`
says, in the same final store and frame. -/
theorem run_complete_initial_out {body : Expr} {s s' : Store H} {f f' : Frame} {o : Out}
    (h : RunC P host C s f [] (expression body) s' f' o) (ho : ∀ k us, o = .br k us → k = 0)
    (hto : ∀ W a c, o ≠ .tail W a c) :
    ∃ st', MRun P host C body (initial body s f) st' ∧ Ends st' o ∧ st'.store = s' ∧
      st'.frame = f' := by
  have hinit : initial body s f = goto (entry body [] 0) ([] : List SeqStep).length [] [] s f := by
    simp [initial, goto, popL, cfgEntry]
  have hrep := rep_entry (P := P) (host := host) (C := C) (body := body) (s := s) (f := f) 0 [] [] []
    (q := []) (c := body) rfl
  simp only [Proofs.Machine.restAt_zero, vals, List.map_nil, List.nil_append] at hrep
  have hr := complete h _ _ _ _ rfl rfl hrep
  rw [← hinit] at hr
  cases o with
  | normal us =>
    exact ⟨_, hr, by simp [Ends, seqLv, goto, contRev, popL], by simp [seqLv, goto],
      by simp [seqLv, goto]⟩
  | br k us =>
    obtain rfl := ho k us rfl
    obtain ⟨W, stk, rfl, hm⟩ := hr.2 (by simp [seqLv])
    exact ⟨_, hm, Or.inr (Or.inr ⟨W, rfl⟩), rfl, rfl⟩
  | ret us =>
    obtain ⟨W, stk, rfl, hm⟩ := hr
    exact ⟨_, hm, Or.inr (Or.inl ⟨W, rfl⟩), rfl, rfl⟩
  | trap => exact ⟨_, hr, Or.inl rfl, rfl, rfl⟩
  | throw a =>
    exact ⟨_, hr.2.1 (fun k L hL => by simp [seqLv] at hL), ⟨a, rfl, rfl⟩, rfl, rfl⟩
  | tail W a c => exact absurd rfl (hto W a c)
  | tailNull W c => exact ⟨_, hr, Or.inr ⟨W, c, rfl⟩, rfl, rfl⟩

/-- **Completeness from the CFG entry, without branches out of the body** (the earlier statement,
a corollary of `run_complete_initial_out`). -/
theorem run_complete_initial {body : Expr} {s s' : Store H} {f f' : Frame} {o : Out}
    (h : RunC P host C s f [] (expression body) s' f' o) (ho : ∀ k us, o ≠ .br k us)
    (hto : ∀ W a c, o ≠ .tail W a c) :
    ∃ st', MRun P host C body (initial body s f) st' ∧ Ends st' o ∧ st'.store = s' ∧
      st'.frame = f' :=
  run_complete_initial_out h (fun k us he => absurd he (ho k us)) hto

/-- **Completeness for a tail call, from the CFG entry**: a region run of a function body that
ends in a pending tail call of `a`, together with an answer of `C` to that call (on the top
`ps.length` values), is a machine run from the initial state to the sink of the answer. -/
theorem run_complete_tail_initial {body : Expr} {s s' s₃ : Store H} {f f' : Frame}
    {W W₀ args : List Val} {a : Nat} {c : Admin} {fi : FuncInst H} {ps rs : List Validation.CValType}
    {fl : Binaryen.Flow} {st' : MState H}
    (h : RunC P host C s f [] (expression body) s' f' (.tail W a c))
    (hfi : s'.funcs[a]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hW : W = W₀ ++ args) (hn : args.length = ps.length) (hcall : C s' a args (s₃, fl))
    (hend : tailEnd rs.length s₃ f' fl = some st') :
    MRun P host C body (initial body s f) st' := by
  have hinit : initial body s f = goto (entry body [] 0) ([] : List SeqStep).length [] [] s f := by
    simp [initial, goto, popL, cfgEntry]
  have hrep := rep_entry (P := P) (host := host) (C := C) (body := body) (s := s) (f := f) 0 [] []
    [] (q := []) (c := body) rfl
  simp only [Proofs.Machine.restAt_zero, vals, List.map_nil, List.nil_append] at hrep
  have hr := complete h _ _ _ _ rfl rfl hrep
  rw [hinit]
  exact hr fi ps rs W₀ args fl s₃ st' hfi hty (by simpa [seqLv, brVals] using hW) hn hcall hend

end Silmaril.Wasm.Cfg.Proofs.MachineComplete
