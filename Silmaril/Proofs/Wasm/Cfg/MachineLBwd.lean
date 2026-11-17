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

theorem mEnds_congr {body : Expr} {Fin : Store H × Frame × POut → Prop} {st : MState H}
    {l l' : List (SCall H)} (h : l = l') (hE : MEnds body Fin st l) : MEnds body Fin st l' :=
  h ▸ hE

theorem mEnds_congr' {body : Expr} {Fin : Store H × Frame × POut → Prop} {l l' : List (SCall H)}
    (h : l' = l) {P : MState H → Prop}
    (hE : ∃ st, P st ∧ MEnds body Fin st l') : ∃ st, P st ∧ MEnds body Fin st l := h ▸ hE

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

/-! ## Positions -/

theorem isStruct_terminator {t : Instr} (h : Instr.IsStruct t) : isTerminator t = true := by
  obtain ⟨_, _, _, _, hk⟩ := h; cases hk <;> rfl

theorem seg_wf {c : List Instr} {i : Nat} {sg : Segment} (hsg : (segment c)[i]? = some sg) :
    sg.WellFormed := (segment_isSegmentation c).2.1 sg (List.mem_of_getElem? hsg)

/-- A terminator in `post` is the segment's terminator, `post` ending there. -/
theorem pos_term {body : Expr} {p : List SeqStep} {c : List Instr} {i : Nat} {sg : Segment}
    {pre post' : List Instr} {e : Instr} (hp : Pos body p c i sg pre (e :: post'))
    (he : isTerminator e = true) : sg.term = some e ∧ post' = [] ∧ pre = sg.body := by
  have hwf := seg_wf hp.hsg
  have hi := hp.hinstrs
  simp only [Segment.instrs] at hi
  have hlen : sg.body.length ≤ pre.length := by
    by_contra hlt
    push Not at hlt
    have h1 : (sg.body ++ sg.term.toList)[pre.length]? = some e := by rw [hi]; simp
    rw [List.getElem?_append_left hlt] at h1
    have := hwf.1 e (List.mem_of_getElem? h1)
    rw [he] at this; cases this
  obtain ⟨X, hX⟩ : ∃ X, pre = sg.body ++ X := by
    refine ⟨pre.drop sg.body.length, ?_⟩
    have := congrArg (List.take sg.body.length) hi
    simp [List.take_append_of_le_length hlen] at this
    conv_lhs => rw [← List.take_append_drop sg.body.length pre]
    rw [← this]
  subst hX
  simp only [List.append_assoc, List.append_cancel_left_eq] at hi
  rcases ht : sg.term with _ | t
  · rw [ht] at hi; simp at hi
  · rw [ht] at hi
    rcases X with _ | ⟨x, X⟩
    · simp only [Option.toList_some, List.nil_append, List.cons.injEq] at hi
      exact ⟨by rw [hi.1], hi.2.symm, by simp⟩
    · simp at hi

/-- The last instruction of a segment, not structured: the segment's terminator is not
structured. -/
theorem pos_last_nonstruct {body : Expr} {p : List SeqStep} {c : List Instr} {i : Nat}
    {sg : Segment} {pre : List Instr} {e : Instr} (hp : Pos body p c i sg pre [e])
    (he : ¬ Instr.IsStruct e) : ∀ t, sg.term = some t → ¬ Instr.IsStruct t := by
  intro t ht hs
  have hi := hp.hinstrs
  simp only [Segment.instrs, ht, Option.toList_some] at hi
  have := congrArg List.getLast? hi
  simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
    Option.some.injEq] at this
  subst this
  exact he hs

/-- Before a structured terminator, a non-structured instruction is in the body. -/
theorem pos_body_prefix {body : Expr} {p : List SeqStep} {c : List Instr} {i : Nat}
    {sg : Segment} {pre post' : List Instr} {e t : Instr} (hp : Pos body p c i sg pre (e :: post'))
    (he : ¬ Instr.IsStruct e) (ht : sg.term = some t) (hts : Instr.IsStruct t) :
    ∃ X, sg.body = pre ++ e :: X := by
  have hi := hp.hinstrs
  simp only [Segment.instrs, ht, Option.toList_some] at hi
  have hle := hp.hstruct t ht hts
  rcases Nat.lt_or_ge pre.length sg.body.length with hlt | hge
  · refine ⟨sg.body.drop (pre.length + 1), ?_⟩
    have h1 := congrArg (List.take pre.length) hi
    simp [List.take_append_of_le_length hle] at h1
    have h2 : sg.body[pre.length]? = some e := by
      have := congrArg (·[pre.length]?) hi
      simp only [List.getElem?_append_left hlt] at this
      simpa using this
    simp [List.getElem?_eq_getElem hlt] at h2
    calc sg.body = sg.body.take pre.length ++ sg.body.drop pre.length :=
          (List.take_append_drop _ _).symm
      _ = pre ++ e :: sg.body.drop (pre.length + 1) := by
          rw [h1, List.drop_eq_getElem_cons hlt, h2]
  · have heq : pre.length = sg.body.length := by omega
    have h3 : (sg.body ++ [t])[sg.body.length]? = some t := by simp
    have h4 : (pre ++ e :: post')[pre.length]? = some e := by simp
    rw [hi, ← heq, h4] at h3
    cases h3
    exact absurd hts he

/-- One more non-structured instruction of `post` moves into `pre`. -/
theorem pos_next {body : Expr} {p : List SeqStep} {c : List Instr} {i : Nat} {sg : Segment}
    {pre post' : List Instr} {e e' : Instr} (hp : Pos body p c i sg pre (e :: e' :: post'))
    (he : ¬ Instr.IsStruct e) : Pos body p c i sg (pre ++ [e]) (e' :: post') where
  hc := hp.hc
  hsg := hp.hsg
  hinstrs := by rw [hp.hinstrs]; simp
  hpost := by simp
  hstruct t ht hts := by
    obtain ⟨X, hX⟩ := pos_body_prefix hp he ht hts
    rw [hX]; simp

/-- **The block clause, continuing**: a non-structured instruction ran normally, and the
motive holds for the rest. -/
theorem blk_cont {body : Expr} {Fin : Store H × Frame × POut → Prop} {p : List SeqStep}
    {c : List Instr} {i : Nat} {sg : Segment} {pre post' : List Instr} {e : Instr}
    {ls : List LFrame} {l' : List (SCall H)} {s s₂ : Store H} {f f₂ : Frame} {N N₂ : List Val}
    {l_e l_k : List (SCall H)} {r : Store H × Frame × POut}
    (hp : Pos body p c i sg pre (e :: post')) (hok : FramesOk body p.reverse ls)
    (hx : ExitE body Fin p ls r l') (he : ¬ Instr.IsStruct e)
    (hstep : EvalLXPS s f N [liftInstr e] l_e (s₂, f₂, .flow (.normal N₂)))
    (hk : EvalLXPS s₂ f₂ N₂ (liftInstrs post' ++ liftInstrs (restAt c (i + 1))) l_k r)
    (ihk : Mot body Fin s₂ f₂ N₂ (liftInstrs post' ++ liftInstrs (restAt c (i + 1))) l_k r)
    (s₀ : Store H) (f₀ : Frame) (N₀ : List Val) (l₀ : List (SCall H))
    (hpre : EvalLXPS s₀ f₀ N₀ (liftInstrs pre) l₀ (s, f, .flow (.normal N))) :
    MEnds body Fin ⟨.block ⟨p, i⟩, N₀.reverse, ls, s₀, f₀⟩ (l₀ ++ (l_e ++ l_k) ++ l') := by
  have hpre' : EvalLXPS s₀ f₀ N₀ (liftInstrs (pre ++ [e])) (l₀ ++ l_e)
      (s₂, f₂, .flow (.normal N₂)) := by
    rw [MachineLSeq.liftInstrs_append]
    exact (MachineLSeq.append hpre _).2 _ _ _ rfl _ _ (by simpa [liftInstrs] using hstep)
  rcases post' with _ | ⟨e', post''⟩
  · have ht := pos_last_nonstruct hp he
    have hb : lookup body ⟨p, i⟩ = some sg := by rw [lookup_eq]; simp [hp.hc, hp.hsg]
    simp only [liftInstrs, List.nil_append] at hk ihk
    obtain ⟨st, hg, hE⟩ := at_boundary hk ihk hp.hc hok hx
    have hr : EvalLXPS s₀ f₀ (N₀.reverse).reverse (liftInstrs (MachineL.codeOf sg)) (l₀ ++ l_e)
        (s₂, f₂, .flow (.normal N₂)) := by
      rw [List.reverse_reverse, codeOf_eq, hp.hinstrs]; exact hpre'
    have := mEnds_step (MStepL.run hb ht hr (.next (by simpa using hg))) hE
    simpa [List.append_assoc] using this
  · have := (ihk p c i sg (pre ++ [e]) (e' :: post'') ls l' (pos_next hp he) rfl hok hx).1
      s₀ f₀ N₀ (l₀ ++ l_e) hpre'
    simpa [List.append_assoc] using this

/-- **The block clause, abrupt**: a non-structured instruction of `post` ended the code. -/
theorem blk_abrupt {body : Expr} {Fin : Store H × Frame × POut → Prop} {p : List SeqStep}
    {c : List Instr} {i : Nat} {sg : Segment} {pre post' : List Instr} {e : Instr}
    {ls : List LFrame} {l' : List (SCall H)} {s : Store H} {f : Frame} {N : List Val}
    {l_e : List (SCall H)} {r : Store H × Frame × POut}
    (hp : Pos body p c i sg pre (e :: post')) (hx : ExitE body Fin p ls r l')
    (he : ¬ Instr.IsStruct e) (hstep : EvalLXPS s f N [liftInstr e] l_e r)
    (hn : ¬ r.2.2.IsNormal)
    (htail : ∀ fa args n, r.2.2 = .tail fa args n → isTerminator e = true)
    (s₀ : Store H) (f₀ : Frame) (N₀ : List Val) (l₀ : List (SCall H))
    (hpre : EvalLXPS s₀ f₀ N₀ (liftInstrs pre) l₀ (s, f, .flow (.normal N))) :
    MEnds body Fin ⟨.block ⟨p, i⟩, N₀.reverse, ls, s₀, f₀⟩ (l₀ ++ l_e ++ l') := by
  have hrun : EvalLXPS s₀ f₀ N₀ (liftInstrs (pre ++ [e])) (l₀ ++ l_e) r := by
    rw [MachineLSeq.liftInstrs_append]
    exact (MachineLSeq.append hpre _).2 _ _ _ rfl _ _ (by simpa [liftInstrs] using hstep)
  have hb : lookup body ⟨p, i⟩ = some sg := by rw [lookup_eq]; simp [hp.hc, hp.hsg]
  by_cases hts : ∃ t, sg.term = some t ∧ Instr.IsStruct t
  · obtain ⟨t, ht, hst⟩ := hts
    obtain ⟨X, hX⟩ := pos_body_prefix hp he ht hst
    have hr : EvalLXPS s₀ f₀ (N₀.reverse).reverse (liftInstrs sg.body) (l₀ ++ l_e) r := by
      rw [List.reverse_reverse, hX, show pre ++ e :: X = (pre ++ [e]) ++ X by simp,
        MachineLSeq.liftInstrs_append]
      exact (MachineLSeq.append hrun _).1 hn
    obtain ⟨s', f', o⟩ := r
    rcases o with fl | ⟨fa, args, n⟩
    · unfold ExitE at hx
      cases fl with
      | normal => exact absurd trivial hn
      | _ =>
        obtain ⟨st, hd, hE⟩ := hx
        exact mEnds_step (MStepL.abort hb hr hn (dispL_idx' hn hd)) hE
    · have := htail fa args n rfl
      have hwf := (seg_wf hp.hsg).1 e (by rw [hX]; simp)
      rw [this] at hwf; cases hwf
  · push Not at hts
    have hr : EvalLXPS s₀ f₀ (N₀.reverse).reverse (liftInstrs (MachineL.codeOf sg)) (l₀ ++ l_e) r := by
      rw [List.reverse_reverse, codeOf_eq, hp.hinstrs,
        show pre ++ e :: post' = (pre ++ [e]) ++ post' by simp, MachineLSeq.liftInstrs_append]
      exact (MachineLSeq.append hrun _).1 hn
    simpa using block_abrupt hb (fun t ht h => hts t ht h) hr hn hx

/-- **The block clause, a structured terminator**, from the arm clause: the machine enters the
arm. -/
theorem blk_enter {body : Expr} {Fin : Store H × Frame × POut → Prop} {p : List SeqStep}
    {c : List Instr} {i : Nat} {sg : Segment} {pre : List Instr} {t : Instr}
    {ls : List LFrame} {l l' : List (SCall H)} {s : Store H} {f : Frame} {N V' : List Val}
    {a : Nat} {c' : List Instr} {np nr : Nat} {bt : BlockType} {loop tryT : Bool}
    {cs : List Catch} (hp : Pos body p c i sg pre [t]) (hk : StructKind t bt loop tryT cs)
    (hsel : ArmSel t N a V') (harm : armOf t a = some c') (har : arity f bt = some (np, nr))
    (hA : ∃ st₁, gotoN (entry body (p ++ [(i, a)]) 0) (p.length + 1)
      (⟨if loop then np else nr, (V'.drop np).reverse, loop, tryT, cs, bt⟩ :: ls)
      (V'.take np).reverse s f = some st₁ ∧ MEnds body Fin st₁ (l ++ l'))
    (s₀ : Store H) (f₀ : Frame) (N₀ : List Val) (l₀ : List (SCall H))
    (hpre : EvalLXPS s₀ f₀ N₀ (liftInstrs pre) l₀ (s, f, .flow (.normal N))) :
    MEnds body Fin ⟨.block ⟨p, i⟩, N₀.reverse, ls, s₀, f₀⟩ (l₀ ++ l ++ l') := by
  obtain ⟨ht, -, hpb⟩ := pos_term hp (isStruct_terminator ⟨_, _, _, _, hk⟩)
  subst hpb
  have hb : lookup body ⟨p, i⟩ = some sg := by rw [lookup_eq]; simp [hp.hc, hp.hsg]
  obtain ⟨st₁, hg, hE⟩ := hA
  have := mEnds_step (MStepL.enter hb ht harm hk (by rw [List.reverse_reverse]; exact hpre) hsel
    har hg) hE
  simpa [List.append_assoc] using this

/-! ## Inversions -/

theorem pos_head {body : Expr} {p : List SeqStep} {c : List Instr} {i : Nat} {sg : Segment}
    {pre post : List Instr} {hd : BExpr} {tl R : List BExpr} (hp : Pos body p c i sg pre post)
    (hes : hd :: tl = liftInstrs post ++ R) :
    ∃ e post', post = e :: post' ∧ hd = liftInstr e ∧ tl = liftInstrs post' ++ R := by
  rcases post with _ | ⟨e, post'⟩
  · exact absurd rfl hp.hpost
  · simp only [liftInstrs, List.cons_append, List.cons.injEq] at hes
    exact ⟨e, post', rfl, hes.1, hes.2⟩

theorem lift_op {e i : Instr} {args : List BExpr} (h : liftInstr e = .op i args) :
    e = i ∧ args = [] ∧ ¬ Instr.IsStruct e := by
  cases e <;> simp [liftInstr] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
    exact ⟨rfl, rfl, fun ⟨_, _, _, _, hk⟩ => nomatch hk⟩

theorem lift_block {e : Instr} {bt : BlockType} {b : List BExpr} (h : liftInstr e = .block bt b) :
    ∃ b₀, e = .block bt b₀ ∧ b = liftInstrs b₀ := by
  cases e <;> simp [liftInstr] at h
  obtain ⟨rfl, rfl⟩ := h; exact ⟨_, rfl, rfl⟩

theorem lift_loop {e : Instr} {bt : BlockType} {b : List BExpr} (h : liftInstr e = .loop bt b) :
    ∃ b₀, e = .loop bt b₀ ∧ b = liftInstrs b₀ := by
  cases e <;> simp [liftInstr] at h
  obtain ⟨rfl, rfl⟩ := h; exact ⟨_, rfl, rfl⟩

theorem lift_try {e : Instr} {bt : BlockType} {cs : List Catch} {b : List BExpr}
    (h : liftInstr e = .tryTable bt cs b) : ∃ b₀, e = .tryTable bt cs b₀ ∧ b = liftInstrs b₀ := by
  cases e <;> simp [liftInstr] at h
  obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨_, rfl, rfl⟩

theorem lift_if {e : Instr} {bt : BlockType} {cc t el : List BExpr}
    (h : liftInstr e = .if_ bt cc t el) :
    ∃ t₀ e₀, e = .if_ bt t₀ e₀ ∧ cc = [] ∧ t = liftInstrs t₀ ∧ el = liftInstrs e₀ := by
  cases e <;> simp [liftInstr] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact ⟨_, _, rfl, rfl, rfl, rfl⟩

/-- **The arm clause from the arm's native run**: entering arm `a` natively, the arm's run and
its exit obligation give a finishing machine run from the arm's entry. -/
theorem arm_entry {body : Expr} {Fin : Store H × Frame × POut → Prop} {p : List SeqStep}
    {c : List Instr} {i : Nat} {sg : Segment} {pre : List Instr} {t : Instr} {ls : List LFrame}
    {s : Store H} {f : Frame} {V' : List Val} {a : Nat} {c' : List Instr} {np nr : Nat}
    {bt : BlockType} {loop tryT : Bool} {cs : List Catch} {l₁ l₂ : List (SCall H)}
    {r₀ : Store H × Frame × POut} (hp : Pos body p c i sg pre [t])
    (hk : StructKind t bt loop tryT cs) (harm : armOf t a = some c')
    (hok : FramesOk body p.reverse ls)
    (hrun : EvalLXPS s f (V'.take np) (liftInstrs c') l₁ r₀)
    (ihrun : Mot body Fin s f (V'.take np) (liftInstrs c') l₁ r₀)
    (hx : ExitE body Fin (p ++ [(i, a)])
      (⟨if loop then np else nr, (V'.drop np).reverse, loop, tryT, cs, bt⟩ :: ls) r₀ l₂) :
    ∃ st₁, gotoN (entry body (p ++ [(i, a)]) 0) (p.length + 1)
      (⟨if loop then np else nr, (V'.drop np).reverse, loop, tryT, cs, bt⟩ :: ls)
      (V'.take np).reverse s f = some st₁ ∧ MEnds body Fin st₁ (l₁ ++ l₂) := by
  obtain ⟨ht, -, -⟩ := pos_term hp (isStruct_terminator ⟨_, _, _, _, hk⟩)
  have hcA : seqAt body (p ++ [(i, a)]) = some c' := by
    rw [Proofs.Machine.seqAt_append]; simp [hp.hc, hp.hsg, ht, harm]
  have hokA : FramesOk body (p ++ [(i, a)]).reverse
      (⟨if loop then np else nr, (V'.drop np).reverse, loop, tryT, cs, bt⟩ :: ls) := by
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, FramesOk]
    exact ⟨⟨c, sg, t, c', by simpa using hp.hc, hp.hsg, ht, harm, hk⟩, hok⟩
  rw [← restAt_zero c'] at hrun ihrun
  simpa using at_boundary hrun ihrun hcA hokA hx

theorem nil_inv_normal {s s' : Store H} {f f' : Frame} {N N' : List Val} {l : List (SCall H)}
    (h : EvalLXPS s f N [] l (s', f', .flow (.normal N'))) : s' = s ∧ f' = f ∧ N' = N ∧ l = [] := by
  obtain ⟨h1, h2, h3, h4⟩ := nil_inv h
  simp only [POut.flow.injEq, Flow.normal.injEq] at h3
  exact ⟨h1, h2, h3, h4⟩

theorem arm_ok {body : Expr} {p : List SeqStep} {c : List Instr} {i : Nat} {sg : Segment}
    {pre : List Instr} {t : Instr} {ls : List LFrame} {a : Nat} {c' : List Instr}
    {bt : BlockType} {loop tryT : Bool} {cs : List Catch} (hp : Pos body p c i sg pre [t])
    (hk : StructKind t bt loop tryT cs) (harm : armOf t a = some c')
    (hok : FramesOk body p.reverse ls) (n : Nat) (ou : List Val) :
    FramesOk body ((i, a) :: p.reverse) (⟨n, ou, loop, tryT, cs, bt⟩ :: ls) := by
  obtain ⟨ht, -, -⟩ := pos_term hp (isStruct_terminator ⟨_, _, _, _, hk⟩)
  exact ⟨⟨c, sg, t, c', by simpa using hp.hc, hp.hsg, ht, harm, hk⟩, hok⟩

/-- **The exit of a block-like frame** (`block`, `if`, `try_table`): falling out of the arm, or a
branch to its label, continues after the instruction. -/
theorem exit_ok_like {body : Expr} {Fin : Store H × Frame × POut → Prop} {p : List SeqStep}
    {i a : Nat} {L : LFrame} {ls : List LFrame} {s : Store H} {f : Frame} {fl : Flow}
    {vs : List Val} {np nr : Nat} {l' : List (SCall H)}
    (hokA : FramesOk body ((i, a) :: p.reverse) (L :: ls)) (hloop : L.loop = false)
    (har : arity f L.bt = some (np, nr)) (hvs : fl.blockVals = some vs)
    (hx : ∃ st, gotoN (entry body p (i + 1)) p.length ls (L.outer ++ (vs.take nr).reverse) s f =
      some st ∧ MEnds body Fin st l') :
    ExitE body Fin (p ++ [(i, a)]) (L :: ls) (s, f, .flow fl) l' := by
  cases fl with
  | normal ws => simp [Flow.blockVals] at hvs; subst hvs; exact exit_fall har hx
  | brk k ws =>
    rcases k with _ | k
    · simp [Flow.blockVals] at hvs; subst hvs; exact exit_brk0 hokA hloop har hx
    · simp [Flow.blockVals] at hvs
  | _ => simp [Flow.blockVals] at hvs

theorem armOf_if {bt : BlockType} {t e c' : List Instr} {b : Bool}
    (h : armOf (.if_ bt t e) (if b then 0 else 1) = some c') : c' = if b then t else e := by
  cases b <;> simp [armOf] at h <;> exact h.symm

theorem armOf_if' (bt : BlockType) (t e : List Instr) (b : Bool) :
    armOf (.if_ bt t e) (if b then 0 else 1) = some (if b then t else e) := by
  cases b <;> rfl

theorem liftInstrs_ite (b : Bool) (t e : List Instr) :
    (if b then liftInstrs t else liftInstrs e) = liftInstrs (if b then t else e) := by
  cases b <;> rfl

/-- **The main induction**: every native run satisfies the motive. -/
theorem mot {body : Expr} {Fin : Store H × Frame × POut → Prop} {s : Store H} {f : Frame}
    {N : List Val} {es : List BExpr} {l : List (SCall H)} {r : Store H × Frame × POut}
    (h : EvalLXPS s f N es l r) : Mot body Fin s f N es l r := by
  induction h with
  | nil =>
    intro p c i sg pre post ls l' hp hes
    rcases post with _ | ⟨e, post'⟩
    · exact absurd rfl hp.hpost
    · simp [liftInstrs] at hes
  | argsAbort hargs ho =>
    intro p c i sg pre post ls l' hp hes
    obtain ⟨e, post', rfl, hhd, -⟩ := pos_head hp hes
    obtain ⟨rfl, rfl, -⟩ := lift_op hhd.symm
    obtain ⟨-, -, rfl, -⟩ := nil_inv hargs
    exact absurd trivial ho
  | callRet hargs hfi hty hk _ ihk =>
    intro p c i sg pre post ls l' hp hes hok hx
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    have hl := hhd.symm
    obtain ⟨rfl, rfl, hns⟩ := lift_op hhd.symm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_inv_normal hargs
    subst htl
    refine ⟨fun s₀ f₀ N₀ l₀ hpre => ?_, fun t _ _ _ _ _ _ _ _ _ hpost hk' => ?_⟩
    · refine mEnds_congr ?_ (blk_cont hp hok hx hns (by rw [hl]; exact EvalLXPS.callRet .nil hfi hty .nil) hk ihk s₀ f₀ N₀ l₀ hpre)
      simp
    · simp only [List.cons.injEq] at hpost; obtain ⟨rfl, -⟩ := hpost
      exact absurd ⟨_, _, _, _, hk'⟩ hns
  | callThrow hargs hfi hty =>
    intro p c i sg pre post ls l' hp hes hok hx
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    have hl := hhd.symm
    obtain ⟨rfl, rfl, hns⟩ := lift_op hhd.symm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_inv_normal hargs
    refine ⟨fun s₀ f₀ N₀ l₀ hpre => ?_, fun t _ _ _ _ _ _ _ _ _ hpost hk' => ?_⟩
    · refine mEnds_congr ?_ (blk_abrupt hp hx hns (by rw [hl]; exact EvalLXPS.callThrow (es := []) .nil hfi hty)
        (by simp [POut.IsNormal, Flow.IsNormal]) (fun _ _ _ h => by cases h) s₀ f₀ N₀ l₀ hpre)
      simp
    · simp only [List.cons.injEq] at hpost; obtain ⟨rfl, -⟩ := hpost
      exact absurd ⟨_, _, _, _, hk'⟩ hns
  | opOk hi hargs hflat hk _ ihk =>
    intro p c i sg pre post ls l' hp hes hok hx
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    have hl := hhd.symm
    obtain ⟨rfl, rfl, hns⟩ := lift_op hhd.symm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_inv_normal hargs
    subst htl
    refine ⟨fun s₀ f₀ N₀ l₀ hpre => ?_, fun t _ _ _ _ _ _ _ _ _ hpost hk' => ?_⟩
    · refine mEnds_congr ?_ (blk_cont hp hok hx hns (by rw [hl]; exact EvalLXPS.opOk (es := []) hi .nil hflat .nil) hk ihk s₀ f₀ N₀ l₀ hpre)
      simp
    · simp only [List.cons.injEq] at hpost; obtain ⟨rfl, -⟩ := hpost
      exact absurd ⟨_, _, _, _, hk'⟩ hns
  | indRet hargs hres hfi hty hy hk _ ihk =>
    intro p c i sg pre post ls l' hp hes hok hx
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    have hl := hhd.symm
    obtain ⟨rfl, rfl, hns⟩ := lift_op hhd.symm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_inv_normal hargs
    subst htl
    refine ⟨fun s₀ f₀ N₀ l₀ hpre => ?_, fun t _ _ _ _ _ _ _ _ _ hpost hk' => ?_⟩
    · refine mEnds_congr ?_ (blk_cont hp hok hx hns (by rw [hl]; exact EvalLXPS.indRet (es := []) .nil hres hfi hty hy .nil) hk ihk s₀ f₀ N₀ l₀ hpre)
      simp
    · simp only [List.cons.injEq] at hpost; obtain ⟨rfl, -⟩ := hpost
      exact absurd ⟨_, _, _, _, hk'⟩ hns
  | refRet hargs hfi hty hy hk _ ihk =>
    intro p c i sg pre post ls l' hp hes hok hx
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    have hl := hhd.symm
    obtain ⟨rfl, rfl, hns⟩ := lift_op hhd.symm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_inv_normal hargs
    subst htl
    refine ⟨fun s₀ f₀ N₀ l₀ hpre => ?_, fun t _ _ _ _ _ _ _ _ _ hpost hk' => ?_⟩
    · refine mEnds_congr ?_ (blk_cont hp hok hx hns (by rw [hl]; exact EvalLXPS.refRet (es := []) .nil hfi hty hy .nil) hk ihk s₀ f₀ N₀ l₀ hpre)
      simp
    · simp only [List.cons.injEq] at hpost; obtain ⟨rfl, -⟩ := hpost
      exact absurd ⟨_, _, _, _, hk'⟩ hns
  | callTrap hargs hfi hty =>
    intro p c i sg pre post ls l' hp hes hok hx
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    have hl := hhd.symm
    obtain ⟨rfl, rfl, hns⟩ := lift_op hhd.symm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_inv_normal hargs
    refine ⟨fun s₀ f₀ N₀ l₀ hpre => ?_, fun t _ _ _ _ _ _ _ _ _ hpost hk' => ?_⟩
    · refine mEnds_congr ?_ (blk_abrupt hp hx hns (by rw [hl]; exact EvalLXPS.callTrap (es := []) .nil hfi hty)
        (by simp [POut.IsNormal, Flow.IsNormal]) (fun _ _ _ h => by cases h) s₀ f₀ N₀ l₀ hpre)
      simp
    · simp only [List.cons.injEq] at hpost; obtain ⟨rfl, -⟩ := hpost
      exact absurd ⟨_, _, _, _, hk'⟩ hns
  | opStop hi hargs hflat hfl =>
    intro p c i sg pre post ls l' hp hes hok hx
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    have hl := hhd.symm
    obtain ⟨rfl, rfl, hns⟩ := lift_op hhd.symm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_inv_normal hargs
    refine ⟨fun s₀ f₀ N₀ l₀ hpre => ?_, fun t _ _ _ _ _ _ _ _ _ hpost hk' => ?_⟩
    · refine mEnds_congr ?_ (blk_abrupt hp hx hns (by rw [hl]; exact EvalLXPS.opStop (es := []) hi .nil hflat hfl)
        (hfl) (fun _ _ _ h => by cases h) s₀ f₀ N₀ l₀ hpre)
      simp
    · simp only [List.cons.injEq] at hpost; obtain ⟨rfl, -⟩ := hpost
      exact absurd ⟨_, _, _, _, hk'⟩ hns
  | indThrow hargs hres hfi hty hy =>
    intro p c i sg pre post ls l' hp hes hok hx
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    have hl := hhd.symm
    obtain ⟨rfl, rfl, hns⟩ := lift_op hhd.symm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_inv_normal hargs
    refine ⟨fun s₀ f₀ N₀ l₀ hpre => ?_, fun t _ _ _ _ _ _ _ _ _ hpost hk' => ?_⟩
    · refine mEnds_congr ?_ (blk_abrupt hp hx hns (by rw [hl]; exact EvalLXPS.indThrow (es := []) .nil hres hfi hty hy)
        (by simp [POut.IsNormal, Flow.IsNormal]) (fun _ _ _ h => by cases h) s₀ f₀ N₀ l₀ hpre)
      simp
    · simp only [List.cons.injEq] at hpost; obtain ⟨rfl, -⟩ := hpost
      exact absurd ⟨_, _, _, _, hk'⟩ hns
  | indTrap hargs hres hfi hty hy =>
    intro p c i sg pre post ls l' hp hes hok hx
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    have hl := hhd.symm
    obtain ⟨rfl, rfl, hns⟩ := lift_op hhd.symm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_inv_normal hargs
    refine ⟨fun s₀ f₀ N₀ l₀ hpre => ?_, fun t _ _ _ _ _ _ _ _ _ hpost hk' => ?_⟩
    · refine mEnds_congr ?_ (blk_abrupt hp hx hns (by rw [hl]; exact EvalLXPS.indTrap (es := []) .nil hres hfi hty hy)
        (by simp [POut.IsNormal, Flow.IsNormal]) (fun _ _ _ h => by cases h) s₀ f₀ N₀ l₀ hpre)
      simp
    · simp only [List.cons.injEq] at hpost; obtain ⟨rfl, -⟩ := hpost
      exact absurd ⟨_, _, _, _, hk'⟩ hns
  | indRes hargs hres =>
    intro p c i sg pre post ls l' hp hes hok hx
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    have hl := hhd.symm
    obtain ⟨rfl, rfl, hns⟩ := lift_op hhd.symm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_inv_normal hargs
    refine ⟨fun s₀ f₀ N₀ l₀ hpre => ?_, fun t _ _ _ _ _ _ _ _ _ hpost hk' => ?_⟩
    · refine mEnds_congr ?_ (blk_abrupt hp hx hns (by rw [hl]; exact EvalLXPS.indRes (es := []) .nil hres)
        (by simp [POut.IsNormal, Flow.IsNormal]) (fun _ _ _ h => by cases h) s₀ f₀ N₀ l₀ hpre)
      simp
    · simp only [List.cons.injEq] at hpost; obtain ⟨rfl, -⟩ := hpost
      exact absurd ⟨_, _, _, _, hk'⟩ hns
  | refThrow hargs hfi hty hy =>
    intro p c i sg pre post ls l' hp hes hok hx
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    have hl := hhd.symm
    obtain ⟨rfl, rfl, hns⟩ := lift_op hhd.symm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_inv_normal hargs
    refine ⟨fun s₀ f₀ N₀ l₀ hpre => ?_, fun t _ _ _ _ _ _ _ _ _ hpost hk' => ?_⟩
    · refine mEnds_congr ?_ (blk_abrupt hp hx hns (by rw [hl]; exact EvalLXPS.refThrow (es := []) .nil hfi hty hy)
        (by simp [POut.IsNormal, Flow.IsNormal]) (fun _ _ _ h => by cases h) s₀ f₀ N₀ l₀ hpre)
      simp
    · simp only [List.cons.injEq] at hpost; obtain ⟨rfl, -⟩ := hpost
      exact absurd ⟨_, _, _, _, hk'⟩ hns
  | refTrap hargs hfi hty hy =>
    intro p c i sg pre post ls l' hp hes hok hx
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    have hl := hhd.symm
    obtain ⟨rfl, rfl, hns⟩ := lift_op hhd.symm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_inv_normal hargs
    refine ⟨fun s₀ f₀ N₀ l₀ hpre => ?_, fun t _ _ _ _ _ _ _ _ _ hpost hk' => ?_⟩
    · refine mEnds_congr ?_ (blk_abrupt hp hx hns (by rw [hl]; exact EvalLXPS.refTrap (es := []) .nil hfi hty hy)
        (by simp [POut.IsNormal, Flow.IsNormal]) (fun _ _ _ h => by cases h) s₀ f₀ N₀ l₀ hpre)
      simp
    · simp only [List.cons.injEq] at hpost; obtain ⟨rfl, -⟩ := hpost
      exact absurd ⟨_, _, _, _, hk'⟩ hns
  | refNull hargs =>
    intro p c i sg pre post ls l' hp hes hok hx
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    have hl := hhd.symm
    obtain ⟨rfl, rfl, hns⟩ := lift_op hhd.symm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_inv_normal hargs
    refine ⟨fun s₀ f₀ N₀ l₀ hpre => ?_, fun t _ _ _ _ _ _ _ _ _ hpost hk' => ?_⟩
    · refine mEnds_congr ?_ (blk_abrupt hp hx hns (by rw [hl]; exact EvalLXPS.refNull (es := []) .nil)
        (by simp [POut.IsNormal, Flow.IsNormal]) (fun _ _ _ h => by cases h) s₀ f₀ N₀ l₀ hpre)
      simp
    · simp only [List.cons.injEq] at hpost; obtain ⟨rfl, -⟩ := hpost
      exact absurd ⟨_, _, _, _, hk'⟩ hns
  | tail hargs hres hfi hty hy =>
    intro p c i sg pre post ls l' hp hes hok hx
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    have hl := hhd.symm
    obtain ⟨rfl, rfl, hns⟩ := lift_op hhd.symm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_inv_normal hargs
    refine ⟨fun s₀ f₀ N₀ l₀ hpre => ?_, fun t _ _ _ _ _ _ _ _ _ hpost hk' => ?_⟩
    · refine mEnds_congr ?_ (blk_abrupt hp hx hns (by rw [hl]; exact EvalLXPS.tail (es := []) .nil hres hfi hty hy)
        (id) (fun _ _ _ _ => by cases hres <;> rfl) s₀ f₀ N₀ l₀ hpre)
      simp
    · simp only [List.cons.injEq] at hpost; obtain ⟨rfl, -⟩ := hpost
      exact absurd ⟨_, _, _, _, hk'⟩ hns
  | tailRes hargs hres =>
    intro p c i sg pre post ls l' hp hes hok hx
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    have hl := hhd.symm
    obtain ⟨rfl, rfl, hns⟩ := lift_op hhd.symm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_inv_normal hargs
    refine ⟨fun s₀ f₀ N₀ l₀ hpre => ?_, fun t _ _ _ _ _ _ _ _ _ hpost hk' => ?_⟩
    · refine mEnds_congr ?_ (blk_abrupt hp hx hns (by rw [hl]; exact EvalLXPS.tailRes (es := []) .nil hres)
        (by simp [POut.IsNormal, Flow.IsNormal]) (fun _ _ _ h => by cases h) s₀ f₀ N₀ l₀ hpre)
      simp
    · simp only [List.cons.injEq] at hpost; obtain ⟨rfl, -⟩ := hpost
      exact absurd ⟨_, _, _, _, hk'⟩ hns
  | throw hargs ht he hn =>
    intro p c i sg pre post ls l' hp hes hok hx
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    have hl := hhd.symm
    obtain ⟨rfl, rfl, hns⟩ := lift_op hhd.symm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_inv_normal hargs
    refine ⟨fun s₀ f₀ N₀ l₀ hpre => ?_, fun t _ _ _ _ _ _ _ _ _ hpost hk' => ?_⟩
    · refine mEnds_congr ?_ (blk_abrupt hp hx hns (by rw [hl]; exact EvalLXPS.throw (es := []) .nil ht he hn)
        (by simp [POut.IsNormal, Flow.IsNormal]) (fun _ _ _ h => by cases h) s₀ f₀ N₀ l₀ hpre)
      simp
    · simp only [List.cons.injEq] at hpost; obtain ⟨rfl, -⟩ := hpost
      exact absurd ⟨_, _, _, _, hk'⟩ hns
  | throwRefNull hargs =>
    intro p c i sg pre post ls l' hp hes hok hx
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    have hl := hhd.symm
    obtain ⟨rfl, rfl, hns⟩ := lift_op hhd.symm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_inv_normal hargs
    refine ⟨fun s₀ f₀ N₀ l₀ hpre => ?_, fun t _ _ _ _ _ _ _ _ _ hpost hk' => ?_⟩
    · refine mEnds_congr ?_ (blk_abrupt hp hx hns (by rw [hl]; exact EvalLXPS.throwRefNull (es := []) .nil)
        (by simp [POut.IsNormal, Flow.IsNormal]) (fun _ _ _ h => by cases h) s₀ f₀ N₀ l₀ hpre)
      simp
    · simp only [List.cons.injEq] at hpost; obtain ⟨rfl, -⟩ := hpost
      exact absurd ⟨_, _, _, _, hk'⟩ hns
  | throwRefExn hargs =>
    intro p c i sg pre post ls l' hp hes hok hx
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    have hl := hhd.symm
    obtain ⟨rfl, rfl, hns⟩ := lift_op hhd.symm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_inv_normal hargs
    refine ⟨fun s₀ f₀ N₀ l₀ hpre => ?_, fun t _ _ _ _ _ _ _ _ _ hpost hk' => ?_⟩
    · refine mEnds_congr ?_ (blk_abrupt hp hx hns (by rw [hl]; exact EvalLXPS.throwRefExn (es := []) .nil)
        (by simp [POut.IsNormal, Flow.IsNormal]) (fun _ _ _ h => by cases h) s₀ f₀ N₀ l₀ hpre)
      simp
    · simp only [List.cons.injEq] at hpost; obtain ⟨rfl, -⟩ := hpost
      exact absurd ⟨_, _, _, _, hk'⟩ hns
  | blockOk har hbody hvs hk ihb ihk =>
    intro p c i sg pre post ls l' hp hes hok hx
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    obtain ⟨b₀, rfl, rfl⟩ := lift_block hhd.symm
    obtain ⟨-, rfl, -⟩ := pos_term hp rfl
    simp only [liftInstrs, List.nil_append] at htl
    subst htl
    refine (fun harmC => ⟨fun s₀ f₀ N₀ l₀ hpre => ?blk, harmC⟩) ?arm
    case arm =>
      intro t a c' V' np nr bt' loop tryT cs hpost hk' hsel harm' har'
      simp only [List.cons.injEq, and_true] at hpost; subst hpost
      cases hk'
      cases hsel
      simp only [armOf, Option.some.injEq] at harm'; subst harm'
      have har₀ := har
      rw [har'] at har₀; simp only [Option.some.injEq, Prod.mk.injEq] at har₀
      obtain ⟨rfl, rfl⟩ := har₀
      have hokA := arm_ok (a := 0) hp .block rfl hok
      have har₁ := (arity_congr (MachineLSeq.module_eq hbody) _).trans har'
      obtain ⟨st, hg, hE⟩ := at_boundary hk ihk hp.hc hok hx
      exact mEnds_congr' (by simp) (arm_entry hp .block rfl hok hbody ihb (exit_ok_like (hokA _ _) rfl har₁ hvs ⟨st, by simpa [List.reverse_append] using hg, hE⟩))
    case blk =>
    exact blk_enter hp .block (.plain (fun _ _ _ => nofun)) rfl har
      (harmC _ 0 _ _ _ _ _ false false [] rfl .block (.plain (fun _ _ _ => nofun)) rfl har)
      s₀ f₀ N₀ l₀ hpre
  | blockBrk har hbody ihb =>
    intro p c i sg pre post ls l' hp hes hok hx
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    obtain ⟨b₀, rfl, rfl⟩ := lift_block hhd.symm
    obtain ⟨-, rfl, -⟩ := pos_term hp rfl
    simp only [liftInstrs, List.nil_append] at htl
    subst htl
    refine (fun harmC => ⟨fun s₀ f₀ N₀ l₀ hpre => ?blk, harmC⟩) ?arm
    case arm =>
      intro t a c' V' np nr bt' loop tryT cs hpost hk' hsel harm' har'
      simp only [List.cons.injEq, and_true] at hpost; subst hpost
      cases hk'
      cases hsel
      simp only [armOf, Option.some.injEq] at harm'; subst harm'
      have har₀ := har
      rw [har'] at har₀; simp only [Option.some.injEq, Prod.mk.injEq] at har₀
      obtain ⟨rfl, rfl⟩ := har₀
      have hokA := arm_ok (a := 0) hp .block rfl hok
      have har₁ := (arity_congr (MachineLSeq.module_eq hbody) _).trans har'
      exact mEnds_congr' (by simp) (arm_entry hp .block rfl hok hbody ihb (exit_brk_succ hx))
    case blk =>
    exact blk_enter hp .block (.plain (fun _ _ _ => nofun)) rfl har
      (harmC _ 0 _ _ _ _ _ false false [] rfl .block (.plain (fun _ _ _ => nofun)) rfl har)
      s₀ f₀ N₀ l₀ hpre
  | blockEsc har hbody ho ihb =>
    intro p c i sg pre post ls l' hp hes hok hx
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    obtain ⟨b₀, rfl, rfl⟩ := lift_block hhd.symm
    obtain ⟨-, rfl, -⟩ := pos_term hp rfl
    simp only [liftInstrs, List.nil_append] at htl
    subst htl
    refine (fun harmC => ⟨fun s₀ f₀ N₀ l₀ hpre => ?blk, harmC⟩) ?arm
    case arm =>
      intro t a c' V' np nr bt' loop tryT cs hpost hk' hsel harm' har'
      simp only [List.cons.injEq, and_true] at hpost; subst hpost
      cases hk'
      cases hsel
      simp only [armOf, Option.some.injEq] at harm'; subst harm'
      have har₀ := har
      rw [har'] at har₀; simp only [Option.some.injEq, Prod.mk.injEq] at har₀
      obtain ⟨rfl, rfl⟩ := har₀
      have hokA := arm_ok (a := 0) hp .block rfl hok
      have har₁ := (arity_congr (MachineLSeq.module_eq hbody) _).trans har'
      exact mEnds_congr' (by simp) (arm_entry hp .block rfl hok hbody ihb (exit_esc ho (fun _ _ h => by cases h) hx))
    case blk =>
    exact blk_enter hp .block (.plain (fun _ _ _ => nofun)) rfl har
      (harmC _ 0 _ _ _ _ _ false false [] rfl .block (.plain (fun _ _ _ => nofun)) rfl har)
      s₀ f₀ N₀ l₀ hpre
  | loopOk har hbody hk ihb ihk =>
    intro p c i sg pre post ls l' hp hes hok hx
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    obtain ⟨b₀, rfl, rfl⟩ := lift_loop hhd.symm
    obtain ⟨-, rfl, -⟩ := pos_term hp rfl
    simp only [liftInstrs, List.nil_append] at htl
    subst htl
    refine (fun harmC => ⟨fun s₀ f₀ N₀ l₀ hpre => ?blk, harmC⟩) ?arm
    case arm =>
      intro t a c' V' np nr bt' loop tryT cs hpost hk' hsel harm' har'
      simp only [List.cons.injEq, and_true] at hpost; subst hpost
      cases hk'
      cases hsel
      simp only [armOf, Option.some.injEq] at harm'; subst harm'
      have har₀ := har
      rw [har'] at har₀; simp only [Option.some.injEq, Prod.mk.injEq] at har₀
      obtain ⟨rfl, rfl⟩ := har₀
      have hokA := arm_ok (a := 0) hp .loop rfl hok
      have har₁ := (arity_congr (MachineLSeq.module_eq hbody) _).trans har'
      obtain ⟨st, hg, hE⟩ := at_boundary hk ihk hp.hc hok hx
      exact mEnds_congr' (by simp) (arm_entry hp .loop rfl hok hbody ihb (exit_fall har₁ ⟨st, by simpa [List.reverse_append] using hg, hE⟩))
    case blk =>
    exact blk_enter hp .loop (.plain (fun _ _ _ => nofun)) rfl har
      (harmC _ 0 _ _ _ _ _ true false [] rfl .loop (.plain (fun _ _ _ => nofun)) rfl har)
      s₀ f₀ N₀ l₀ hpre
  | loopBack har hbody hk ihb ihk =>
    intro p c i sg pre post ls l' hp hes hok hx
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    obtain ⟨b₀, rfl, rfl⟩ := lift_loop hhd.symm
    obtain ⟨-, rfl, -⟩ := pos_term hp rfl
    simp only [liftInstrs, List.nil_append] at htl
    subst htl
    refine (fun harmC => ⟨fun s₀ f₀ N₀ l₀ hpre => ?blk, harmC⟩) ?arm
    case arm =>
      intro t a c' V' np nr bt' loop tryT cs hpost hk' hsel harm' har'
      simp only [List.cons.injEq, and_true] at hpost; subst hpost
      cases hk'
      cases hsel
      simp only [armOf, Option.some.injEq] at harm'; subst harm'
      have har₀ := har
      rw [har'] at har₀; simp only [Option.some.injEq, Prod.mk.injEq] at har₀
      obtain ⟨rfl, rfl⟩ := har₀
      have hokA := arm_ok (a := 0) hp .loop rfl hok
      have har₁ := (arity_congr (MachineLSeq.module_eq hbody) _).trans har'
      obtain ⟨st, hg, hE⟩ := (ihk p c i sg pre _ ls l' hp (by simp [liftInstrs, liftInstr]) hok
        hx).2 _ 0 _ _ np nr _ true false [] rfl .loop (.plain (fun _ _ _ => nofun)) rfl har₁
      exact mEnds_congr' (by simp) (arm_entry hp .loop rfl hok hbody ihb (exit_loopBack (hokA _ _) rfl har₁ ⟨st, by simpa using hg, hE⟩))
    case blk =>
    exact blk_enter hp .loop (.plain (fun _ _ _ => nofun)) rfl har
      (harmC _ 0 _ _ _ _ _ true false [] rfl .loop (.plain (fun _ _ _ => nofun)) rfl har)
      s₀ f₀ N₀ l₀ hpre
  | loopBrk har hbody ihb =>
    intro p c i sg pre post ls l' hp hes hok hx
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    obtain ⟨b₀, rfl, rfl⟩ := lift_loop hhd.symm
    obtain ⟨-, rfl, -⟩ := pos_term hp rfl
    simp only [liftInstrs, List.nil_append] at htl
    subst htl
    refine (fun harmC => ⟨fun s₀ f₀ N₀ l₀ hpre => ?blk, harmC⟩) ?arm
    case arm =>
      intro t a c' V' np nr bt' loop tryT cs hpost hk' hsel harm' har'
      simp only [List.cons.injEq, and_true] at hpost; subst hpost
      cases hk'
      cases hsel
      simp only [armOf, Option.some.injEq] at harm'; subst harm'
      have har₀ := har
      rw [har'] at har₀; simp only [Option.some.injEq, Prod.mk.injEq] at har₀
      obtain ⟨rfl, rfl⟩ := har₀
      have hokA := arm_ok (a := 0) hp .loop rfl hok
      have har₁ := (arity_congr (MachineLSeq.module_eq hbody) _).trans har'
      exact mEnds_congr' (by simp) (arm_entry hp .loop rfl hok hbody ihb (exit_brk_succ hx))
    case blk =>
    exact blk_enter hp .loop (.plain (fun _ _ _ => nofun)) rfl har
      (harmC _ 0 _ _ _ _ _ true false [] rfl .loop (.plain (fun _ _ _ => nofun)) rfl har)
      s₀ f₀ N₀ l₀ hpre
  | loopEsc har hbody ho ihb =>
    intro p c i sg pre post ls l' hp hes hok hx
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    obtain ⟨b₀, rfl, rfl⟩ := lift_loop hhd.symm
    obtain ⟨-, rfl, -⟩ := pos_term hp rfl
    simp only [liftInstrs, List.nil_append] at htl
    subst htl
    refine (fun harmC => ⟨fun s₀ f₀ N₀ l₀ hpre => ?blk, harmC⟩) ?arm
    case arm =>
      intro t a c' V' np nr bt' loop tryT cs hpost hk' hsel harm' har'
      simp only [List.cons.injEq, and_true] at hpost; subst hpost
      cases hk'
      cases hsel
      simp only [armOf, Option.some.injEq] at harm'; subst harm'
      have har₀ := har
      rw [har'] at har₀; simp only [Option.some.injEq, Prod.mk.injEq] at har₀
      obtain ⟨rfl, rfl⟩ := har₀
      have hokA := arm_ok (a := 0) hp .loop rfl hok
      have har₁ := (arity_congr (MachineLSeq.module_eq hbody) _).trans har'
      exact mEnds_congr' (by simp) (arm_entry hp .loop rfl hok hbody ihb (exit_esc ho (fun _ _ h => by cases h) hx))
    case blk =>
    exact blk_enter hp .loop (.plain (fun _ _ _ => nofun)) rfl har
      (harmC _ 0 _ _ _ _ _ true false [] rfl .loop (.plain (fun _ _ _ => nofun)) rfl har)
      s₀ f₀ N₀ l₀ hpre
  | tryOk har hbody hvs hk ihb ihk =>
    intro p c i sg pre post ls l' hp hes hok hx
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    obtain ⟨b₀, rfl, rfl⟩ := lift_try hhd.symm
    obtain ⟨-, rfl, -⟩ := pos_term hp rfl
    simp only [liftInstrs, List.nil_append] at htl
    subst htl
    refine (fun harmC => ⟨fun s₀ f₀ N₀ l₀ hpre => ?blk, harmC⟩) ?arm
    case arm =>
      intro t a c' V' np nr bt' loop tryT cs hpost hk' hsel harm' har'
      simp only [List.cons.injEq, and_true] at hpost; subst hpost
      cases hk'
      cases hsel
      simp only [armOf, Option.some.injEq] at harm'; subst harm'
      have har₀ := har
      rw [har'] at har₀; simp only [Option.some.injEq, Prod.mk.injEq] at har₀
      obtain ⟨rfl, rfl⟩ := har₀
      have hokA := arm_ok (a := 0) hp .tryTable rfl hok
      have har₁ := (arity_congr (MachineLSeq.module_eq hbody) _).trans har'
      obtain ⟨st, hg, hE⟩ := at_boundary hk ihk hp.hc hok hx
      exact mEnds_congr' (by simp) (arm_entry hp .tryTable rfl hok hbody ihb (exit_ok_like (hokA _ _) rfl har₁ hvs ⟨st, by simpa [List.reverse_append] using hg, hE⟩))
    case blk =>
    exact blk_enter hp .tryTable (.plain (fun _ _ _ => nofun)) rfl har
      (harmC _ 0 _ _ _ _ _ false true _ rfl .tryTable (.plain (fun _ _ _ => nofun)) rfl har)
      s₀ f₀ N₀ l₀ hpre
  | tryBrk har hbody ihb =>
    intro p c i sg pre post ls l' hp hes hok hx
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    obtain ⟨b₀, rfl, rfl⟩ := lift_try hhd.symm
    obtain ⟨-, rfl, -⟩ := pos_term hp rfl
    simp only [liftInstrs, List.nil_append] at htl
    subst htl
    refine (fun harmC => ⟨fun s₀ f₀ N₀ l₀ hpre => ?blk, harmC⟩) ?arm
    case arm =>
      intro t a c' V' np nr bt' loop tryT cs hpost hk' hsel harm' har'
      simp only [List.cons.injEq, and_true] at hpost; subst hpost
      cases hk'
      cases hsel
      simp only [armOf, Option.some.injEq] at harm'; subst harm'
      have har₀ := har
      rw [har'] at har₀; simp only [Option.some.injEq, Prod.mk.injEq] at har₀
      obtain ⟨rfl, rfl⟩ := har₀
      have hokA := arm_ok (a := 0) hp .tryTable rfl hok
      have har₁ := (arity_congr (MachineLSeq.module_eq hbody) _).trans har'
      exact mEnds_congr' (by simp) (arm_entry hp .tryTable rfl hok hbody ihb (exit_brk_succ hx))
    case blk =>
    exact blk_enter hp .tryTable (.plain (fun _ _ _ => nofun)) rfl har
      (harmC _ 0 _ _ _ _ _ false true _ rfl .tryTable (.plain (fun _ _ _ => nofun)) rfl har)
      s₀ f₀ N₀ l₀ hpre
  | tryEsc har hbody ho hnt ihb =>
    intro p c i sg pre post ls l' hp hes hok hx
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    obtain ⟨b₀, rfl, rfl⟩ := lift_try hhd.symm
    obtain ⟨-, rfl, -⟩ := pos_term hp rfl
    simp only [liftInstrs, List.nil_append] at htl
    subst htl
    refine (fun harmC => ⟨fun s₀ f₀ N₀ l₀ hpre => ?blk, harmC⟩) ?arm
    case arm =>
      intro t a c' V' np nr bt' loop tryT cs hpost hk' hsel harm' har'
      simp only [List.cons.injEq, and_true] at hpost; subst hpost
      cases hk'
      cases hsel
      simp only [armOf, Option.some.injEq] at harm'; subst harm'
      have har₀ := har
      rw [har'] at har₀; simp only [Option.some.injEq, Prod.mk.injEq] at har₀
      obtain ⟨rfl, rfl⟩ := har₀
      have hokA := arm_ok (a := 0) hp .tryTable rfl hok
      have har₁ := (arity_congr (MachineLSeq.module_eq hbody) _).trans har'
      exact mEnds_congr' (by simp) (arm_entry hp .tryTable rfl hok hbody ihb (exit_esc ho (fun _ h _ => by subst h; exact absurd hnt id) hx))
    case blk =>
    exact blk_enter hp .tryTable (.plain (fun _ _ _ => nofun)) rfl har
      (harmC _ 0 _ _ _ _ _ false true _ rfl .tryTable (.plain (fun _ _ _ => nofun)) rfl har)
      s₀ f₀ N₀ l₀ hpre
  | tryCatch har hbody hc ihb =>
    intro p c i sg pre post ls l' hp hes hok hx
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    obtain ⟨b₀, rfl, rfl⟩ := lift_try hhd.symm
    obtain ⟨-, rfl, -⟩ := pos_term hp rfl
    simp only [liftInstrs, List.nil_append] at htl
    subst htl
    refine (fun harmC => ⟨fun s₀ f₀ N₀ l₀ hpre => ?blk, harmC⟩) ?arm
    case arm =>
      intro t a c' V' np nr bt' loop tryT cs hpost hk' hsel harm' har'
      simp only [List.cons.injEq, and_true] at hpost; subst hpost
      cases hk'
      cases hsel
      simp only [armOf, Option.some.injEq] at harm'; subst harm'
      have har₀ := har
      rw [har'] at har₀; simp only [Option.some.injEq, Prod.mk.injEq] at har₀
      obtain ⟨rfl, rfl⟩ := har₀
      have hokA := arm_ok (a := 0) hp .tryTable rfl hok
      have har₁ := (arity_congr (MachineLSeq.module_eq hbody) _).trans har'
      exact mEnds_congr' (by simp) (arm_entry hp .tryTable rfl hok hbody ihb (exit_catch (l' := l') rfl hc (by simpa using hx)))
    case blk =>
    exact blk_enter hp .tryTable (.plain (fun _ _ _ => nofun)) rfl har
      (harmC _ 0 _ _ _ _ _ false true _ rfl .tryTable (.plain (fun _ _ _ => nofun)) rfl har)
      s₀ f₀ N₀ l₀ hpre
  | tryRethrow har hbody hc ihb =>
    intro p c i sg pre post ls l' hp hes hok hx
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    obtain ⟨b₀, rfl, rfl⟩ := lift_try hhd.symm
    obtain ⟨-, rfl, -⟩ := pos_term hp rfl
    simp only [liftInstrs, List.nil_append] at htl
    subst htl
    refine (fun harmC => ⟨fun s₀ f₀ N₀ l₀ hpre => ?blk, harmC⟩) ?arm
    case arm =>
      intro t a c' V' np nr bt' loop tryT cs hpost hk' hsel harm' har'
      simp only [List.cons.injEq, and_true] at hpost; subst hpost
      cases hk'
      cases hsel
      simp only [armOf, Option.some.injEq] at harm'; subst harm'
      have har₀ := har
      rw [har'] at har₀; simp only [Option.some.injEq, Prod.mk.injEq] at har₀
      obtain ⟨rfl, rfl⟩ := har₀
      have hokA := arm_ok (a := 0) hp .tryTable rfl hok
      have har₁ := (arity_congr (MachineLSeq.module_eq hbody) _).trans har'
      exact mEnds_congr' (by simp) (arm_entry hp .tryTable rfl hok hbody ihb (exit_esc trivial (fun _ h _ => by cases h; exact hc) hx))
    case blk =>
    exact blk_enter hp .tryTable (.plain (fun _ _ _ => nofun)) rfl har
      (harmC _ 0 _ _ _ _ _ false true _ rfl .tryTable (.plain (fun _ _ _ => nofun)) rfl har)
      s₀ f₀ N₀ l₀ hpre
  | ifOk hc hb har harm hvs hk _ iha ihk =>
    intro p c i sg pre post ls l' hp hes hok hx
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    obtain ⟨t₀, e₀, rfl, rfl, rfl, rfl⟩ := lift_if hhd.symm
    obtain ⟨-, rfl, -⟩ := pos_term hp rfl
    simp only [liftInstrs, List.nil_append] at htl
    subst htl
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_inv_normal hc
    rw [liftInstrs_ite] at harm iha
    refine (fun harmC => ⟨fun s₀ f₀ N₀ l₀ hpre => ?blk, harmC⟩) ?arm
    case arm =>
      intro t a c' V' np nr bt' loop tryT cs hpost hk' hsel harm' har'
      simp only [List.cons.injEq, and_true] at hpost; subst hpost
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
        obtain ⟨st, hg, hE⟩ := at_boundary hk ihk hp.hc hok hx
        exact mEnds_congr' (by simp) (arm_entry hp .if_ harm' hok harm iha (exit_ok_like (hokA _ _) rfl har₁ hvs ⟨st, by simpa [List.reverse_append] using hg, hE⟩))
      | plain hi => exact absurd rfl (hi _ _ _)
    case blk =>
    exact mEnds_congr (by simp) (blk_enter hp .if_ (.cond hb) (armOf_if' _ _ _ _) har
      (harmC _ _ _ _ _ _ _ false false [] rfl .if_ (.cond hb) (armOf_if' _ _ _ _) har)
      s₀ f₀ N₀ l₀ hpre)
  | ifBrk hc hb har harm _ iha =>
    intro p c i sg pre post ls l' hp hes hok hx
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    obtain ⟨t₀, e₀, rfl, rfl, rfl, rfl⟩ := lift_if hhd.symm
    obtain ⟨-, rfl, -⟩ := pos_term hp rfl
    simp only [liftInstrs, List.nil_append] at htl
    subst htl
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_inv_normal hc
    rw [liftInstrs_ite] at harm iha
    refine (fun harmC => ⟨fun s₀ f₀ N₀ l₀ hpre => ?blk, harmC⟩) ?arm
    case arm =>
      intro t a c' V' np nr bt' loop tryT cs hpost hk' hsel harm' har'
      simp only [List.cons.injEq, and_true] at hpost; subst hpost
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
        exact mEnds_congr' (by simp) (arm_entry hp .if_ harm' hok harm iha (exit_brk_succ hx))
      | plain hi => exact absurd rfl (hi _ _ _)
    case blk =>
    exact mEnds_congr (by simp) (blk_enter hp .if_ (.cond hb) (armOf_if' _ _ _ _) har
      (harmC _ _ _ _ _ _ _ false false [] rfl .if_ (.cond hb) (armOf_if' _ _ _ _) har)
      s₀ f₀ N₀ l₀ hpre)
  | ifEsc hc hb har harm ho _ iha =>
    intro p c i sg pre post ls l' hp hes hok hx
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    obtain ⟨t₀, e₀, rfl, rfl, rfl, rfl⟩ := lift_if hhd.symm
    obtain ⟨-, rfl, -⟩ := pos_term hp rfl
    simp only [liftInstrs, List.nil_append] at htl
    subst htl
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_inv_normal hc
    rw [liftInstrs_ite] at harm iha
    refine (fun harmC => ⟨fun s₀ f₀ N₀ l₀ hpre => ?blk, harmC⟩) ?arm
    case arm =>
      intro t a c' V' np nr bt' loop tryT cs hpost hk' hsel harm' har'
      simp only [List.cons.injEq, and_true] at hpost; subst hpost
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
        exact mEnds_congr' (by simp) (arm_entry hp .if_ harm' hok harm iha (exit_esc ho (fun _ _ h => by cases h) hx))
      | plain hi => exact absurd rfl (hi _ _ _)
    case blk =>
    exact mEnds_congr (by simp) (blk_enter hp .if_ (.cond hb) (armOf_if' _ _ _ _) har
      (harmC _ _ _ _ _ _ _ false false [] rfl .if_ (.cond hb) (armOf_if' _ _ _ _) har)
      s₀ f₀ N₀ l₀ hpre)
  | ifAbort hc ho =>
    intro p c i sg pre post ls l' hp hes
    obtain ⟨e, post', rfl, hhd, -⟩ := pos_head hp hes
    obtain ⟨t₀, e₀, rfl, rfl, -, -⟩ := lift_if hhd.symm
    obtain ⟨-, -, rfl, -⟩ := nil_inv hc
    exact absurd trivial ho

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
