module

public import Silmaril.Proofs.Wasm.Cfg.MachineLFwd

@[expose] public section

/-!
# The logged machine against the logged relation: the converse (H2, proofs)

Continuation passing over the native derivation. `MEnds body Fin st l`: the machine runs from
`st` with the log `l` to an end (a sink, or a pending tail call) standing for a native result
satisfying `Fin`. `ExitE`: what the machine must do once a sequence ends with a native outcome.
-/

namespace Silmaril.Wasm.Cfg.Proofs.MachineLBwd

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Abstract (EvalLXPS SCall)
open Silmaril.Wasm.Abstract.CallXP (POut)
open Silmaril.Wasm.Cfg.Region (Catches)
open Silmaril.Wasm.Cfg.Proofs.Machine (restAt_cons restAt_end restAt_zero seg_of_lookup lookup_eq)
open Silmaril.Wasm.Cfg.Proofs.MachineLFwd

variable {H : Type}

/-- **The machine finishes**: from `st`, with the log `l`, it runs to a sink, or to a block whose
straight-line code ends in a pending tail call, standing for a native result satisfying `Fin`. -/
def MEnds (body : Expr) (Fin : Store H × Frame × POut → Prop) (st : MState H)
    (l : List (SCall H)) : Prop :=
  ∃ (st' : MState H) (r : Store H × Frame × POut) (l₁ l₂ : List (SCall H)),
    MRunL body st l₁ st' ∧ l = l₁ ++ l₂ ∧ Fin r ∧
      ((st'.node.IsSink ∧ l₂ = [] ∧ EndRel st' r) ∨ TailL body st' l₂ r)

theorem mEnds_step {body : Expr} {Fin : Store H × Frame × POut → Prop} {st st' : MState H}
    {l₀ l : List (SCall H)} (hs : MStepL body st l₀ st') (h : MEnds body Fin st' l) :
    MEnds body Fin st (l₀ ++ l) := by
  obtain ⟨st'', r, l₁, l₂, hr, rfl, hF, hend⟩ := h
  exact ⟨st'', r, l₀ ++ l₁, l₂, .step hs hr, by simp, hF, hend⟩

/-- A sink standing for a native result satisfying `Fin` finishes. -/
theorem mEnds_sink {body : Expr} {Fin : Store H × Frame × POut → Prop} {st : MState H}
    {r : Store H × Frame × POut} (hs : st.node.IsSink) (hE : EndRel st r) (hF : Fin r) :
    MEnds body Fin st [] :=
  ⟨st, r, [], [], .refl _, rfl, hF, .inl ⟨hs, rfl, hE⟩⟩

/-- **What the machine must do once the sequence at `p` ends with the native outcome `r`**, under
the frames `ls`, the rest of the log being `l'`: falling through, finish from the sequence's
continuation; a pending tail call, nothing (`l' = []`, `Fin r`); any other outcome, finish from
from a target `DispL` gives it. -/
def ExitE (body : Expr) (Fin : Store H × Frame × POut → Prop) (p : List SeqStep)
    (ls : List LFrame) (r : Store H × Frame × POut) (l' : List (SCall H)) : Prop :=
  match r.2.2 with
  | .flow (.normal ws) => ∃ st, gotoN (contRev body p.reverse) p.length ls ws.reverse r.1 r.2.1 =
      some st ∧ MEnds body Fin st l'
  | .tail .. => l' = [] ∧ Fin r
  | _ => ∃ st, DispL body ⟨p, 0⟩ ls r st ∧ MEnds body Fin st l'

/-- `DispL` on an abrupt outcome does not depend on the block's position. -/
theorem dispL_idx {body : Expr} {b : BlockId} {ls : List LFrame} {r : Store H × Frame × POut}
    {st : MState H} (hn : ¬ r.2.2.IsNormal) (hd : DispL body b ls r st) :
    DispL body ⟨b.seq, 0⟩ ls r st := by
  cases hd with
  | next => exact absurd trivial hn
  | br hL hg => exact .br hL (by simpa [branchN] using hg)
  | brOut hk => exact .brOut hk
  | ret => exact .ret
  | trap => exact .trap
  | raise hT => exact .raise hT
  | catch_ hpass hL hT hc hL' hg => exact .catch_ hpass hL hT hc hL' (by simpa [branchN] using hg)
  | catchOut hpass hL hT hc hout => exact .catchOut hpass hL hT hc hout

theorem dispL_idx' {body : Expr} {b : BlockId} {ls : List LFrame} {r : Store H × Frame × POut}
    {st : MState H} (hn : ¬ r.2.2.IsNormal) (hd : DispL body ⟨b.seq, 0⟩ ls r st) :
    DispL body b ls r st := by
  cases hd with
  | next => exact absurd trivial hn
  | br hL hg => exact .br hL (by simpa [branchN] using hg)
  | brOut hk => exact .brOut hk
  | ret => exact .ret
  | trap => exact .trap
  | raise hT => exact .raise hT
  | catch_ hpass hL hT hc hL' hg => exact .catch_ hpass hL hT hc hL' (by simpa [branchN] using hg)
  | catchOut hpass hL hT hc hout => exact .catchOut hpass hL hT hc hout

/-- **A block's straight-line code ran, ending abruptly or in a pending tail call**: the machine
finishes from the block. -/
theorem block_abrupt {body : Expr} {Fin : Store H × Frame × POut → Prop} {b : BlockId}
    {sg : Segment} {stk : List Val} {ls : List LFrame} {s : Store H} {f : Frame}
    {l l' : List (SCall H)} {r : Store H × Frame × POut} (hb : lookup body b = some sg)
    (ht : ∀ i, sg.term = some i → ¬ Instr.IsStruct i)
    (hr : EvalLXPS s f stk.reverse (liftInstrs (MachineL.codeOf sg)) l r)
    (hn : ¬ r.2.2.IsNormal) (hx : ExitE body Fin b.seq ls r l') :
    MEnds body Fin ⟨.block b, stk, ls, s, f⟩ (l ++ l') := by
  obtain ⟨s₁, f₁, o⟩ := r
  unfold ExitE at hx
  rcases o with fl | ⟨fa, args, n⟩
  · cases fl with
    | normal => exact absurd trivial hn
    | _ =>
      obtain ⟨st, hd, hE⟩ := hx
      exact mEnds_step (.run hb ht hr (dispL_idx' hn hd)) hE
  · obtain ⟨rfl, hF⟩ := hx
    exact ⟨_, _, [], l, .refl _, by simp, hF, .inr (.tail hb ht hr)⟩

/-! ## Exit obligations across a frame -/

theorem branchN_succ (body : Expr) (p : List SeqStep) (x : SeqStep) (L₀ : LFrame)
    (ls : List LFrame) (k : Nat) (L : LFrame) (N : List Val) (s : Store H) (f : Frame) :
    branchN body ⟨p ++ [x], 0⟩ (L₀ :: ls) (k + 1) L N s f = branchN body ⟨p, 0⟩ ls k L N s f := by
  rw [branchN_eq, branchN_eq]
  simpa using branchR_succ body x p.reverse L₀ ls k L N s f

/-- **A branch passing the frame**: `brk (k + 1)` inside is `brk k` outside. -/
theorem exit_brk_succ {body : Expr} {Fin : Store H × Frame × POut → Prop} {p : List SeqStep}
    {x : SeqStep} {L : LFrame} {ls : List LFrame} {s : Store H} {f : Frame} {k : Nat}
    {ws : List Val} {l' : List (SCall H)}
    (hx : ExitE body Fin p ls (s, f, .flow (.brk k ws)) l') :
    ExitE body Fin (p ++ [x]) (L :: ls) (s, f, .flow (.brk (k + 1) ws)) l' := by
  obtain ⟨st, hd, hE⟩ := hx
  refine ⟨st, ?_, hE⟩
  cases hd with
  | br hL hg => exact .br (by simpa using hL) (by rw [branchN_succ]; exact hg)
  | brOut hk => exact .brOut (by simp [hk])

/-- **An escaping outcome passing the frame** (a return, a trap, a pending tail call, or an
exception the frame does not catch). -/
theorem exit_esc {body : Expr} {Fin : Store H × Frame × POut → Prop} {p : List SeqStep}
    {x : SeqStep} {L : LFrame} {ls : List LFrame} {s : Store H} {f : Frame} {o : POut}
    {l' : List (SCall H)} (ho : o.Escapes)
    (hpass : ∀ a, o = .flow (.throw a) → L.tryT = true → Catches s f a L.catches none)
    (hx : ExitE body Fin p ls (s, f, o) l') : ExitE body Fin (p ++ [x]) (L :: ls) (s, f, o) l' := by
  rcases o with fl | ⟨fa, args, n⟩
  · cases fl with
    | normal => exact absurd ho id
    | brk => exact absurd ho id
    | ret ws =>
      obtain ⟨st, hd, hE⟩ := hx
      refine ⟨st, ?_, hE⟩
      cases hd; exact .ret
    | trap =>
      obtain ⟨st, hd, hE⟩ := hx
      refine ⟨st, ?_, hE⟩
      cases hd; exact .trap
    | throw a =>
      obtain ⟨st, hd, hE⟩ := hx
      refine ⟨st, ?_, hE⟩
      cases hd with
      | raise hT =>
        refine .raise fun k L' hL' hTL => ?_
        rcases k with _ | k
        · simp only [List.getElem?_cons_zero, Option.some.injEq] at hL'; subst hL'
          exact hpass a rfl hTL
        · exact hT k L' (by simpa using hL') hTL
      | @catch_ _ _ _ j _ _ _ lb _ hpass' hL hT hc hL' hg =>
        refine .catch_ (j := j + 1) (fun k L' hk hL'' hTL => ?_) (by simpa using hL) hT hc
          (by rw [show j + 1 + 1 + lb.toNat = (j + 1 + lb.toNat) + 1 by omega]; simpa using hL') ?_
        · rcases k with _ | k
          · simp only [List.getElem?_cons_zero, Option.some.injEq] at hL''; subst hL''
            exact hpass a rfl hTL
          · exact hpass' k L' (by omega) (by simpa using hL'') hTL
        · rw [show j + 1 + 1 + lb.toNat = (j + 1 + lb.toNat) + 1 by omega, branchN_succ]; exact hg
      | catchOut hpass' hL hT hc hout =>
        refine .catchOut (j := _ + 1) (fun k L' hk hL'' hTL => ?_) (by simpa using hL) hT hc
          (by simp; omega)
        rcases k with _ | k
        · simp only [List.getElem?_cons_zero, Option.some.injEq] at hL''; subst hL''
          exact hpass a rfl hTL
        · exact hpass' k L' (by omega) (by simpa using hL'') hTL
  · exact hx

/-- **A caught exception**: the frame's `try_table` catches it (`tryCatch`), a branch from
outside it with the caught values over its outer values. -/
theorem exit_catch {body : Expr} {Fin : Store H × Frame × POut → Prop} {p : List SeqStep}
    {x : SeqStep} {L : LFrame} {ls : List LFrame} {s : Store H} {f : Frame} {a : Nat}
    {us : List Val} {lb : LabelIdx} {l' : List (SCall H)} (hT : L.tryT = true)
    (hc : Catches s f a L.catches (some (us, lb)))
    (hx : ExitE body Fin p ls (s, f, .flow (.brk lb.toNat (us.reverse ++ L.outer.reverse))) l') :
    ExitE body Fin (p ++ [x]) (L :: ls) (s, f, .flow (.throw a)) l' := by
  obtain ⟨st, hd, hE⟩ := hx
  refine ⟨st, ?_, hE⟩
  cases hd with
  | br hL hg =>
    have h01 : 0 + 1 + lb.toNat = lb.toNat + 1 := by omega
    exact .catch_ (j := 0) (fun _ _ h => absurd h (Nat.not_lt_zero _)) rfl hT hc
      (by rw [h01]; simpa using hL) (by rw [h01, branchN_succ]; exact hg)
  | brOut hk =>
    have := DispL.catchOut (body := body) (b := ⟨p ++ [x], 0⟩) (ls := L :: ls) (j := 0)
      (fun _ _ h => absurd h (Nat.not_lt_zero _)) rfl hT hc (by simp [hk]; omega)
    simpa using this

theorem gotoN_pop {t : Target} {d : Nat} {L : LFrame} {ls : List LFrame} {W : List Val}
    {s : Store H} {f : Frame} (hd : depthT t ≤ d) :
    gotoN t (d + 1) (L :: ls) W s f =
      (arity f L.bt).bind fun a => gotoN t d ls (L.outer ++ topVals a.2 W) s f := by
  unfold gotoN
  rw [show d + 1 - depthT t = (d - depthT t) + 1 by omega]
  simp only [popN]
  cases arity f L.bt <;> simp

theorem contRev_cons_entry (body : Expr) (p : List SeqStep) (i a : Nat) :
    contRev body ((i, a) :: p.reverse) = entry body p (i + 1) := by
  simp [contRev, entry, cont]

theorem topVals_rev (n : Nat) (ws : List Val) : topVals n ws.reverse = (ws.take n).reverse := by
  rw [← List.reverse_reverse (topVals n ws.reverse), topVals_reverse, List.reverse_reverse]

/-- **Falling out of the arm**: the frame continues after its instruction with the top `nr`
values over its outer values. -/
theorem exit_fall {body : Expr} {Fin : Store H × Frame × POut → Prop} {p : List SeqStep}
    {i a : Nat} {L : LFrame} {ls : List LFrame} {s : Store H} {f : Frame} {ws : List Val}
    {np nr : Nat} {l' : List (SCall H)} (har : arity f L.bt = some (np, nr))
    (hx : ∃ st, gotoN (entry body p (i + 1)) p.length ls (L.outer ++ (ws.take nr).reverse) s f =
      some st ∧ MEnds body Fin st l') :
    ExitE body Fin (p ++ [(i, a)]) (L :: ls) (s, f, .flow (.normal ws)) l' := by
  obtain ⟨st, hg, hE⟩ := hx
  refine ⟨st, ?_, hE⟩
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, List.length_append, List.length_singleton]
  have hdep : depthT (entry body p (i + 1)) ≤ p.length := by
    rw [← contRev_cons_entry body p i a]
    simpa using Proofs.Machine.depth_contRev_cons body i a p.reverse
  rw [contRev_cons_entry, gotoN_pop hdep, har]
  simp only [Option.bind_some]
  rw [topVals_rev]; exact hg

/-- **A branch to the frame's own label, not a loop**: as falling out of the arm. -/
theorem exit_brk0 {body : Expr} {Fin : Store H × Frame × POut → Prop} {p : List SeqStep}
    {i a : Nat} {L : LFrame} {ls : List LFrame} {s : Store H} {f : Frame} {ws : List Val}
    {np nr : Nat} {l' : List (SCall H)}
    (hok : FramesOk body ((i, a) :: p.reverse) (L :: ls)) (hloop : L.loop = false)
    (har : arity f L.bt = some (np, nr))
    (hx : ∃ st, gotoN (entry body p (i + 1)) p.length ls (L.outer ++ (ws.take nr).reverse) s f =
      some st ∧ MEnds body Fin st l') :
    ExitE body Fin (p ++ [(i, a)]) (L :: ls) (s, f, .flow (.brk 0 ws)) l' := by
  obtain ⟨st, hg, hE⟩ := hx
  have hlev := Proofs.Machine.levelLoop_of_framesOk 0 _ _ hok rfl
  simp only [levelLoop, List.drop_zero, List.reverse_reverse] at hlev
  refine ⟨st, .br rfl ?_, hE⟩
  rw [branchN_eq]
  simp only [branchR, har, Option.bind_some, hloop, Bool.false_eq_true, ↓reduceIte,
    List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, List.length_cons, Nat.add_sub_cancel, List.length_reverse]
  rw [Proofs.Machine.labelsRev_getD 0 ((i, a) :: p.reverse) rfl]
  simp only [List.reverse_reverse] at hlev ⊢
  rw [hlev, hloop]
  simpa [contRev_cons_entry] using hg

/-- **A branch to the frame's own label, a loop**: the loop is re-entered as `loopBack` re-runs
it. -/
theorem exit_loopBack {body : Expr} {Fin : Store H × Frame × POut → Prop} {p : List SeqStep}
    {i a : Nat} {L : LFrame} {ls : List LFrame} {s : Store H} {f : Frame} {ws : List Val}
    {np nr : Nat} {l' : List (SCall H)}
    (hok : FramesOk body ((i, a) :: p.reverse) (L :: ls)) (hloop : L.loop = true)
    (har : arity f L.bt = some (np, nr))
    (hx : ∃ st, gotoN (entry body (p ++ [(i, a)]) 0) (p.length + 1)
      (⟨np, ((ws.take np ++ L.outer.reverse).drop np).reverse, true, L.tryT, L.catches, L.bt⟩ :: ls)
      ((ws.take np ++ L.outer.reverse).take np).reverse s f = some st ∧ MEnds body Fin st l') :
    ExitE body Fin (p ++ [(i, a)]) (L :: ls) (s, f, .flow (.brk 0 ws)) l' := by
  obtain ⟨st, hg, hE⟩ := hx
  have hlev := Proofs.Machine.levelLoop_of_framesOk 0 _ _ hok rfl
  simp only [levelLoop, List.drop_zero, List.reverse_reverse] at hlev
  refine ⟨st, .br rfl ?_, hE⟩
  rw [branchN_eq]
  simp only [branchR, har, Option.bind_some, hloop, ↓reduceIte, List.reverse_append,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
    List.length_cons, Nat.sub_zero, List.length_reverse]
  rw [Proofs.Machine.labelsRev_getD 0 ((i, a) :: p.reverse) rfl]
  simp only [List.reverse_reverse] at hlev ⊢
  rw [hlev, hloop]
  obtain ⟨ar, ou, lp, tt, cs, bt⟩ := L
  simp only at hloop; subst hloop
  simpa using hg

/-! ## The induction on native derivations -/

/-- **A position in a block**: block `i` of the sequence `c` at path `p`, its instructions split
as `pre ++ post`, `post` nonempty, and a structured terminator never in `pre`. -/
structure Pos (body : Expr) (p : List SeqStep) (c : List Instr) (i : Nat) (sg : Segment)
    (pre post : List Instr) : Prop where
  hc : seqAt body p = some c
  hsg : (segment c)[i]? = some sg
  hinstrs : sg.instrs = pre ++ post
  hpost : post ≠ []
  hstruct : ∀ t, sg.term = some t → Instr.IsStruct t → pre.length ≤ sg.body.length

/-- **The motive**: a native run of the code at a position, followed by what the machine does
when the sequence ends (`ExitE`), is a finishing machine run: from the block, once the prefix has
run (the block clause), and, for a structured instruction, from the entry of its arm (the arm
clause, which a loop's re-entry also reaches). -/
def Mot (body : Expr) (Fin : Store H × Frame × POut → Prop) (s : Store H) (f : Frame)
    (N : List Val) (es : List BExpr) (l : List (SCall H)) (r : Store H × Frame × POut) : Prop :=
  ∀ (p : List SeqStep) (c : List Instr) (i : Nat) (sg : Segment) (pre post : List Instr)
    (ls : List LFrame) (l' : List (SCall H)), Pos body p c i sg pre post →
    es = liftInstrs post ++ liftInstrs (restAt c (i + 1)) → FramesOk body p.reverse ls →
    ExitE body Fin p ls r l' →
    (∀ (s₀ : Store H) (f₀ : Frame) (N₀ : List Val) (l₀ : List (SCall H)),
      EvalLXPS s₀ f₀ N₀ (liftInstrs pre) l₀ (s, f, .flow (.normal N)) →
      MEnds body Fin ⟨.block ⟨p, i⟩, N₀.reverse, ls, s₀, f₀⟩ (l₀ ++ l ++ l')) ∧
    (∀ (t : Instr) (a : Nat) (c' : List Instr) (V' : List Val) (np nr : Nat) (bt : BlockType)
      (loop tryT : Bool) (cs : List Catch), post = [t] → StructKind t bt loop tryT cs →
      ArmSel t N a V' → armOf t a = some c' → arity f bt = some (np, nr) →
      ∃ st₁, gotoN (entry body (p ++ [(i, a)]) 0) (p.length + 1)
        (⟨if loop then np else nr, (V'.drop np).reverse, loop, tryT, cs, bt⟩ :: ls)
        (V'.take np).reverse s f = some st₁ ∧ MEnds body Fin st₁ (l ++ l'))

theorem nil_inv {s s' : Store H} {f f' : Frame} {N : List Val} {l : List (SCall H)} {o : POut}
    (h : EvalLXPS s f N [] l (s', f', o)) : s' = s ∧ f' = f ∧ o = .flow (.normal N) ∧ l = [] := by
  generalize he : ([] : List BExpr) = es at h
  cases h <;> first | (exact ⟨rfl, rfl, rfl, rfl⟩) | cases he

/-- **Reaching a sequence position natively** (`gotoN (entry …)`), given the motive for the
native run of the rest of the sequence from there. -/
theorem at_boundary {body : Expr} {Fin : Store H × Frame × POut → Prop} {p : List SeqStep}
    {c : List Instr} {j : Nat} {ls : List LFrame} {s : Store H} {f : Frame} {N : List Val}
    {l l' : List (SCall H)} {r : Store H × Frame × POut}
    (hD : EvalLXPS s f N (liftInstrs (restAt c j)) l r)
    (hM : Mot body Fin s f N (liftInstrs (restAt c j)) l r)
    (hc : seqAt body p = some c) (hok : FramesOk body p.reverse ls)
    (hx : ExitE body Fin p ls r l') :
    ∃ st, gotoN (entry body p j) p.length ls N.reverse s f = some st ∧
      MEnds body Fin st (l ++ l') := by
  unfold entry
  split
  · next hsome =>
    obtain ⟨sg, hsg⟩ := Option.isSome_iff_exists.mp hsome
    rw [lookup_eq] at hsg
    simp only [hc, Option.bind_some] at hsg
    have hne : sg.instrs ≠ [] :=
      (segment_isSegmentation c).2.2.2 sg (List.mem_of_getElem? hsg)
    refine ⟨⟨.block ⟨p, j⟩, N.reverse, ls, s, f⟩, by simp [gotoN, depthT, popN], ?_⟩
    have hpos : Pos body p c j sg [] sg.instrs :=
      ⟨hc, hsg, rfl, hne, fun _ _ _ => Nat.zero_le _⟩
    have := (hM p c j sg [] sg.instrs ls l' hpos
      (by rw [restAt_cons hsg, MachineLSeq.liftInstrs_append]) hok hx).1 s f N [] .nil
    simpa using this
  · next hnone =>
    have hend : (segment c)[j]? = none := by
      rw [lookup_eq] at hnone; simpa [hc] using hnone
    rw [restAt_end hend] at hD
    obtain ⟨s', f', o⟩ := r
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_inv hD
    obtain ⟨st, hg, hE⟩ := hx
    exact ⟨st, by simpa [cont] using hg, by simpa using hE⟩

/-- **The main induction**: every native run satisfies the motive. -/
theorem mot {body : Expr} {Fin : Store H × Frame × POut → Prop} {s : Store H} {f : Frame}
    {N : List Val} {es : List BExpr} {l : List (SCall H)} {r : Store H × Frame × POut}
    (h : EvalLXPS s f N es l r) : Mot body Fin s f N es l r := by
  sorry

/-- **The converse, finished outcomes**: a native run of the body from the empty stack, to an
outcome other than a branch past the function label, is a logged machine run from the CFG entry
to an end standing for it (a sink, or a pending tail call), with exactly the native log. -/
theorem backward {body : Expr} {s : Store H} {f : Frame} {l : List (SCall H)}
    {r : Store H × Frame × POut} (h : EvalLXPS s f [] (liftInstrs body) l r)
    (hr : ∀ k ws, r.2.2 ≠ .flow (.brk (k + 1) ws)) :
    ∃ (st : MState H) (l₁ l₂ : List (SCall H)), MRunL body (initial body s f) l₁ st ∧
      l = l₁ ++ l₂ ∧ ((st.node.IsSink ∧ l₂ = [] ∧ EndRel st r) ∨ TailL body st l₂ r) := by
  have hx : ExitE body (· = r) [] [] r [] := by
    obtain ⟨s', f', o⟩ := r
    rcases o with fl | ⟨fa, args, n⟩
    · cases fl with
      | normal ws =>
        exact ⟨_, rfl, mEnds_sink (st := ⟨.exit, ws.reverse, [], s', f'⟩) trivial
          ⟨_, rfl, by simp [Flow.retVals]⟩ rfl⟩
      | brk k ws =>
        rcases k with _ | k
        · exact ⟨_, .brOut rfl, mEnds_sink trivial ⟨_, rfl, by simp [Flow.retVals]⟩ rfl⟩
        · exact absurd rfl (hr k ws)
      | ret ws => exact ⟨_, .ret, mEnds_sink trivial ⟨_, rfl, by simp [Flow.retVals]⟩ rfl⟩
      | trap => exact ⟨_, .trap, mEnds_sink trivial rfl rfl⟩
      | throw a =>
        exact ⟨_, .raise (fun _ _ h => by simp at h), mEnds_sink trivial ⟨a, rfl, rfl⟩ rfl⟩
    · exact ⟨rfl, rfl⟩
  have hD : EvalLXPS s f [] (liftInstrs (restAt body 0)) l r := by rwa [restAt_zero]
  obtain ⟨st, hg, hE⟩ := at_boundary (p := []) (ls := []) hD (mot hD) rfl (by simp [FramesOk]) hx
  have hst : st = initial body s f := by
    rw [List.reverse_nil, initial_eq] at hg; exact (Option.some.inj hg).symm
  subst hst
  obtain ⟨st', r', l₁, l₂, hrun, hl, rfl, hend⟩ := hE
  exact ⟨st', l₁, l₂, hrun, by simpa using hl, hend⟩

end Silmaril.Wasm.Cfg.Proofs.MachineLBwd
