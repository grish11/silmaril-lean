module

public import Silmaril.Wasm.Cfg.MachineL.Defs
public import Silmaril.Proofs.Wasm.Cfg.MachineLSeq
public import Silmaril.Proofs.Wasm.Cfg.Machine

@[expose] public section

/-!
# The logged machine against the logged relation: the forward direction (H1, proofs)

The invariant `Good`: at a block state, the rest of its sequence (`restAt`) runs in `EvalLXPS`
from the reversed stack, and its outcome is carried out of the label frames by `KL`, whose
frame case `WrapL` is the native rule of the frame's structured instruction applied to the
arm's outcome (`blockOk`, `loopBack`, `ifOk`, `tryCatch`, …), down to a native result of the
function body satisfying a predicate `Fin`.
-/

namespace Silmaril.Wasm.Cfg.Proofs.MachineLFwd

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Abstract (EvalLXPS SCall)
open Silmaril.Wasm.Abstract.CallXP (POut)
open Silmaril.Wasm.Cfg.Region (Catches)
open Silmaril.Wasm.Cfg.Proofs.Machine (restAt_cons restAt_end restAt_zero seg_of_lookup lookup_eq)

variable {H : Type}

/-- **A frame's structured instruction, natively, after its arm ended with `r₀`**: the parent
continues with `rest` (`EvalLXPS`'s `blockOk`/`ifOk`/`tryOk`, `loopOk`, `loopBack`), or the
outcome leaves the frame (`blockBrk`, the escape rules, `tryCatch`, `tryRethrow`). -/
inductive WrapL (L : LFrame) (t : Instr) (rest : List Instr) :
    Store H × Frame × POut → List (SCall H) → Store H × Frame × POut → Prop where
  | ok {s : Store H} {f : Frame} {fl : Flow} {vs : List Val} {np nr : Nat} {l : List (SCall H)}
      {r : Store H × Frame × POut} (hloop : L.loop = false) (har : arity f L.bt = some (np, nr))
      (hvs : fl.blockVals = some vs)
      (hk : EvalLXPS s f (vs.take nr ++ L.outer.reverse) (liftInstrs rest) l r) :
      WrapL L t rest (s, f, .flow fl) l r
  | loopOk {s : Store H} {f : Frame} {vs : List Val} {np nr : Nat} {l : List (SCall H)}
      {r : Store H × Frame × POut} (hloop : L.loop = true) (har : arity f L.bt = some (np, nr))
      (hk : EvalLXPS s f (vs.take nr ++ L.outer.reverse) (liftInstrs rest) l r) :
      WrapL L t rest (s, f, .flow (.normal vs)) l r
  | loopBack {s : Store H} {f : Frame} {vs : List Val} {np nr : Nat} {l : List (SCall H)}
      {r : Store H × Frame × POut} (hloop : L.loop = true) (har : arity f L.bt = some (np, nr))
      (hk : EvalLXPS s f (vs.take np ++ L.outer.reverse) (liftInstr t :: liftInstrs rest) l r) :
      WrapL L t rest (s, f, .flow (.brk 0 vs)) l r
  | brk {s : Store H} {f : Frame} {k : Nat} {vs : List Val} :
      WrapL L t rest (s, f, .flow (.brk (k + 1) vs)) [] (s, f, .flow (.brk k vs))
  | esc {s : Store H} {f : Frame} {o : POut} (ho : o.Escapes) (hnt : L.tryT = true → o.NotThrow) :
      WrapL L t rest (s, f, o) [] (s, f, o)
  | catch_ {s : Store H} {f : Frame} {a : Nat} {us : List Val} {l' : LabelIdx}
      (hT : L.tryT = true) (hc : Catches s f a L.catches (some (us, l'))) :
      WrapL L t rest (s, f, .flow (.throw a)) []
        (s, f, .flow (.brk l'.toNat (us.reverse ++ L.outer.reverse)))
  | rethrow {s : Store H} {f : Frame} {a : Nat} (hT : L.tryT = true)
      (hc : Catches s f a L.catches none) :
      WrapL L t rest (s, f, .flow (.throw a)) [] (s, f, .flow (.throw a))

/-- **Carrying an outcome out of the label frames** at reversed path `rp` (innermost first) to a
native result of the body satisfying `Fin`. -/
inductive KL (body : Expr) (Fin : Store H × Frame × POut → Prop) :
    List SeqStep → List LFrame → Store H × Frame × POut → List (SCall H) → Prop where
  | top {r : Store H × Frame × POut} (h : Fin r) : KL body Fin [] [] r []
  | frame {m a : Nat} {rp : List SeqStep} {L : LFrame} {ls : List LFrame} {pc : List Instr}
      {sg : Segment} {t : Instr} {c : List Instr} {r₀ r₁ : Store H × Frame × POut}
      {l₁ l₂ : List (SCall H)} (hpc : seqAt body rp.reverse = some pc)
      (hsg : (segment pc)[m]? = some sg) (ht : sg.term = some t) (harm : armOf t a = some c)
      (hk : StructKind t L.bt L.loop L.tryT L.catches)
      (hw : WrapL L t (restAt pc (m + 1)) r₀ l₁ r₁) (hrest : KL body Fin rp ls r₁ l₂) :
      KL body Fin ((m, a) :: rp) (L :: ls) r₀ (l₁ ++ l₂)

/-- **What a sink state stands for natively**: `exit` a flow returning its stack (top first),
`trap` a trap, `raise` the exception on its stack, all in its store and frame. -/
def EndRel (st : MState H) (r : Store H × Frame × POut) : Prop :=
  match st.node with
  | .exit => ∃ fl, r = (st.store, st.frame, .flow fl) ∧ fl.retVals = some st.stk.reverse
  | .trap => r = (st.store, st.frame, .flow .trap)
  | .raise => ∃ a, st.stk = [.ref (.exn a)] ∧ r = (st.store, st.frame, .flow (.throw a))
  | _ => False

/-- **The forward invariant**: at a block, the rest of its sequence runs natively and `KL` carries
the outcome out of the frames to a result satisfying `Fin`; at a sink, every result it stands for
satisfies `Fin`. The log is the native runs' logs in order. -/
def Good (body : Expr) (Fin : Store H × Frame × POut → Prop) (st : MState H)
    (l : List (SCall H)) : Prop :=
  match st.node with
  | .block b => ∃ (c : List Instr) (l₀ l₁ : List (SCall H)) (r₀ : Store H × Frame × POut),
      seqAt body b.seq = some c ∧
      EvalLXPS st.store st.frame st.stk.reverse (liftInstrs (restAt c b.idx)) l₀ r₀ ∧
      KL body Fin b.seq.reverse st.lbls r₀ l₁ ∧ l = l₀ ++ l₁
  | .exit | .trap | .raise => l = [] ∧ ∀ r, EndRel st r → Fin r
  | .invalid => False

/-! ## Native frame popping -/

theorem topVals_reverse (n : Nat) (V : List Val) : (topVals n V).reverse = V.reverse.take n := by
  simp only [topVals, List.reverse_drop]
  by_cases hn : n ≤ V.length
  · congr 1; omega
  · rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp; omega)]

theorem arity_congr {f f' : Frame} (h : f'.module = f.module) (bt : BlockType) :
    arity f' bt = arity f bt := by
  cases bt <;> simp [arity, Frame.type?, h]

theorem popN_fst {f : Frame} : ∀ (k : Nat) (ls : List LFrame) (stk : List Val)
    {p : List LFrame × List Val}, popN f k ls stk = some p → p.1 = ls.drop k
  | 0, _, _, _, h => by simp [popN] at h; subst h; rfl
  | _ + 1, [], _, _, h => by simp [popN] at h
  | k + 1, L :: ls, stk, p, h => by
    simp only [popN, Option.bind_eq_some_iff] at h
    obtain ⟨_, -, h⟩ := h
    simpa using popN_fst k ls _ h

/-- `gotoN` reaches the node and frames `goto` does: it keeps the state invariant. -/
theorem gotoN_ok {body : Expr} {t : Target} {d : Nat} {ls : List LFrame} {W : List Val}
    {s : Store H} {f : Frame} {st' : MState H} (h : gotoN t d ls W s f = some st')
    (ht : t ≠ .raise) (hok : MInv body (goto t d ls W s f)) : MInv body st' := by
  simp only [gotoN, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl⟩ := h
  have h1 := popN_fst _ _ _ hp
  have h2 := Proofs.Machine.popL_fst (d - depthT t) ls W
  unfold MInv at hok ⊢
  simp only [goto] at hok
  cases t <;> simp_all

theorem retVals_normal (vs : List Val) : (Flow.normal vs).retVals = some vs := rfl

/-- One native pop of `gotoN` at a target no deeper than the rest of the path. -/
theorem gotoN_cons {t : Target} {d : Nat} {L : LFrame} {ls : List LFrame} {W : List Val}
    {s : Store H} {f : Frame} {st' : MState H} (hd : depthT t ≤ d)
    (h : gotoN t (d + 1) (L :: ls) W s f = some st') :
    ∃ np nr, arity f L.bt = some (np, nr) ∧ gotoN t d ls (L.outer ++ topVals nr W) s f = some st' := by
  unfold gotoN at h ⊢
  rw [show d + 1 - depthT t = (d - depthT t) + 1 by omega] at h
  simp only [popN, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
  obtain ⟨p, ⟨⟨np, nr⟩, har, hp⟩, rfl⟩ := h
  exact ⟨np, nr, har, by simp [hp]⟩

/-- `gotoN` to a block at its own depth moves there with the stack and frames. -/
theorem gotoN_block {b : BlockId} {ls : List LFrame} {W : List Val} {s : Store H} {f : Frame}
    {st' : MState H} (h : gotoN (.block b) b.seq.length ls W s f = some st') :
    st' = ⟨.block b, W, ls, s, f⟩ := by
  simp [gotoN, depthT, popN] at h; exact h.symm

/-- **Leaving a frame normally with the stack `W`**: the native arm ends normally, its frame
continues with the parent's rest (`WrapL.ok` or `loopOk`) on the top values over the outer
ones. -/
theorem wrap_fall {L : LFrame} {t : Instr} {rest : List Instr} {s : Store H} {f : Frame}
    {W : List Val} {np nr : Nat} (har : arity f L.bt = some (np, nr)) {l : List (SCall H)}
    {r : Store H × Frame × POut}
    (hk : EvalLXPS s f (L.outer ++ topVals nr W).reverse (liftInstrs rest) l r) :
    WrapL L t rest (s, f, .flow (.normal W.reverse)) l r := by
  rw [List.reverse_append, topVals_reverse] at hk
  cases hl : L.loop
  · exact .ok hl har rfl hk
  · exact .loopOk hl har hk

/-- **The continuation of a finished sequence** (`contRev`, reached natively by `gotoN`): the
sequence's normal end with the stack `W` is carried out by `KL`. -/
theorem cont_good {body : Expr} {Fin : Store H × Frame × POut → Prop} :
    ∀ (rp : List SeqStep) (ls : List LFrame) (W : List Val) (s : Store H) (f : Frame)
      (st' : MState H) (l : List (SCall H)), FramesOk body rp ls →
      gotoN (contRev body rp) rp.length ls W s f = some st' → Good body Fin st' l →
      KL body Fin rp ls (s, f, .flow (.normal W.reverse)) l
  | [], [], W, s, f, st', l, _, hg, hG => by
    simp only [contRev, gotoN, depthT, List.length_nil, Nat.sub_self, popN, Option.map_some,
      Option.some.injEq] at hg
    subst hg
    obtain ⟨rfl, hF⟩ := hG
    exact .top (hF _ ⟨_, rfl, retVals_normal _⟩)
  | [], _ :: _, _, _, _, _, _, h, _, _ => by simp [FramesOk] at h
  | _ :: _, [], _, _, _, _, _, h, _, _ => by simp [FramesOk] at h
  | (m, a) :: rp, L :: ls, W, s, f, st', l, hok, hg, hG => by
    obtain ⟨⟨pc, sg, t, c, hpc, hsg, ht, harm, hkind⟩, hok'⟩ := hok
    rw [List.length_cons] at hg
    obtain ⟨np, nr, har, hg'⟩ := gotoN_cons (Proofs.Machine.depth_contRev_cons body m a rp) hg
    unfold contRev at hg'
    split at hg'
    · next hsome =>
      rw [show rp.length = (⟨rp.reverse, m + 1⟩ : BlockId).seq.length by simp] at hg'
      have := gotoN_block hg'
      subst this
      obtain ⟨c', l₀, l₁, r₀, hc', hrun, hkl, rfl⟩ := hG
      simp only at hc' hrun hkl
      rw [hpc] at hc'; cases hc'
      exact .frame hpc hsg ht harm hkind (wrap_fall har hrun) (by simpa using hkl)
    · next hnone =>
      have hend : (segment pc)[m + 1]? = none := by
        rw [lookup_eq] at hnone
        simpa [hpc] using hnone
      have hnil : restAt pc (m + 1) = [] := restAt_end hend
      have hkl := cont_good rp ls _ s f st' l hok' hg' hG
      have hw : WrapL L t (restAt pc (m + 1)) (s, f, .flow (.normal W.reverse)) []
          (s, f, .flow (.normal (L.outer ++ topVals nr W).reverse)) :=
        wrap_fall har (by rw [hnil]; exact .nil)
      simpa using KL.frame hpc hsg ht harm hkind hw hkl

/-- **Reaching position `i` of the sequence at `p`** natively (`gotoN (entry …)`): the rest of
the sequence from `i` runs natively and its outcome is carried out by `KL`. -/
theorem entry_good {body : Expr} {Fin : Store H × Frame × POut → Prop} {p : List SeqStep}
    {c : List Instr} {i : Nat} {ls : List LFrame} {W : List Val} {s : Store H} {f : Frame}
    {st' : MState H} {l : List (SCall H)} (hok : FramesOk body p.reverse ls)
    (hc : seqAt body p = some c) (hg : gotoN (entry body p i) p.length ls W s f = some st')
    (hG : Good body Fin st' l) :
    ∃ (l₀ l₁ : List (SCall H)) (r₀ : Store H × Frame × POut),
      EvalLXPS s f W.reverse (liftInstrs (restAt c i)) l₀ r₀ ∧
      KL body Fin p.reverse ls r₀ l₁ ∧ l = l₀ ++ l₁ := by
  unfold entry at hg
  split at hg
  · rw [show p.length = (⟨p, i⟩ : BlockId).seq.length from rfl] at hg
    have := gotoN_block hg
    subst this
    obtain ⟨c', l₀, l₁, r₀, hc', hrun, hkl, rfl⟩ := hG
    simp only at hc' hrun hkl
    rw [hc] at hc'; cases hc'
    exact ⟨l₀, l₁, r₀, by simpa using hrun, hkl, rfl⟩
  · next hnone =>
    have hend : (segment c)[i]? = none := by
      rw [lookup_eq] at hnone
      simpa [hc] using hnone
    rw [restAt_end hend]
    refine ⟨[], l, _, .nil, ?_, rfl⟩
    exact cont_good p.reverse ls W s f st' l hok (by simpa [cont] using hg) hG

/-- The straight-line code of a block is its segment's instructions. -/
theorem codeOf_eq (sg : Segment) : codeOf sg = sg.instrs := rfl

/-- **A block's straight-line code, then the rest**: a normal end continues into the rest of the
sequence; an abrupt one ends it. -/
theorem restAt_run {c : List Instr} {i : Nat} {sg : Segment} (hsg : (segment c)[i]? = some sg)
    {s : Store H} {f : Frame} {V : List Val} {l : List (SCall H)} {r : Store H × Frame × POut}
    (hr : EvalLXPS s f V (liftInstrs (codeOf sg)) l r) :
    (¬ r.2.2.IsNormal → EvalLXPS s f V (liftInstrs (restAt c i)) l r) ∧
    (∀ s₁ f₁ ws, r = (s₁, f₁, .flow (.normal ws)) → ∀ l₂ r₂,
      EvalLXPS s₁ f₁ ws (liftInstrs (restAt c (i + 1))) l₂ r₂ →
      EvalLXPS s f V (liftInstrs (restAt c i)) (l ++ l₂) r₂) := by
  rw [restAt_cons hsg, MachineLSeq.liftInstrs_append]
  exact MachineLSeq.append hr _

/-- **Falling through** (`DispL.next`). -/
theorem next_good {body : Expr} {Fin : Store H × Frame × POut → Prop} {b : BlockId}
    {sg : Segment} {stk : List Val} {ls : List LFrame} {s s₁ : Store H} {f f₁ : Frame}
    {ws : List Val} {l l' : List (SCall H)} {st' : MState H} (hok : FramesOk body b.seq.reverse ls)
    (hb : lookup body b = some sg)
    (hr : EvalLXPS s f stk.reverse (liftInstrs (codeOf sg)) l (s₁, f₁, .flow (.normal ws)))
    (hg : gotoN (entry body b.seq (b.idx + 1)) b.seq.length ls ws.reverse s₁ f₁ = some st')
    (hG : Good body Fin st' l') : Good body Fin ⟨.block b, stk, ls, s, f⟩ (l ++ l') := by
  obtain ⟨c, hc, hsg⟩ := seg_of_lookup hb
  obtain ⟨l₀, l₁, r₀, hrun, hkl, rfl⟩ := entry_good (by simpa using hok) hc hg hG
  refine ⟨c, l ++ l₀, l₁, r₀, hc, ?_, hkl, by simp⟩
  exact (restAt_run hsg hr).2 _ _ _ rfl _ _ (by simpa using hrun)

/-- **An escaping outcome leaves every frame unchanged**: a return, a trap, a pending tail call
(which bypasses handlers), or an exception no `try_table` frame catches. -/
theorem kl_esc {body : Expr} {Fin : Store H × Frame × POut → Prop} {s : Store H} {f : Frame}
    {o : POut} (ho : o.Escapes) (hF : Fin (s, f, o)) :
    ∀ (rp : List SeqStep) (ls : List LFrame), FramesOk body rp ls →
      (∀ a, o = .flow (.throw a) → ∀ (k : Nat) (L : LFrame), ls[k]? = some L →
        L.tryT = true → Catches s f a L.catches none) →
      KL body Fin rp ls (s, f, o) []
  | [], [], _, _ => .top hF
  | [], _ :: _, h, _ => by simp [FramesOk] at h
  | _ :: _, [], h, _ => by simp [FramesOk] at h
  | (m, a) :: rp, L :: ls, hok, hT => by
    obtain ⟨⟨pc, sg, t, c, hpc, hsg, ht, harm, hkind⟩, hok'⟩ := hok
    have hT' : ∀ a', o = .flow (.throw a') → ∀ (k : Nat) (L' : LFrame), ls[k]? = some L' →
        L'.tryT = true → Catches s f a' L'.catches none :=
      fun a' h k L' hL' => hT a' h (k + 1) L' (by simpa using hL')
    have hw : WrapL L t (restAt pc (m + 1)) (s, f, o) [] (s, f, o) := by
      by_cases hth : ∃ a', o = .flow (.throw a')
      · obtain ⟨a', rfl⟩ := hth
        cases htt : L.tryT
        · exact .esc ho (fun h => by rw [htt] at h; cases h)
        · exact .rethrow htt (hT a' rfl 0 L rfl htt)
      · refine .esc ho fun _ => ?_
        rcases o with fl | _
        · cases fl <;> simp_all [POut.NotThrow]
        · trivial
    simpa using KL.frame hpc hsg ht harm hkind hw (kl_esc ho hF rp ls hok' hT')

/-- **A block whose straight-line code ends abruptly**: the rest of the sequence is skipped. -/
theorem abrupt_good {body : Expr} {Fin : Store H × Frame × POut → Prop} {b : BlockId}
    {sg : Segment} {stk : List Val} {ls : List LFrame} {s : Store H} {f : Frame}
    {l l₁ : List (SCall H)} {r : Store H × Frame × POut} {is : List Instr}
    (hb : lookup body b = some sg) (his : is = MachineL.codeOf sg ∨ (is = sg.body ∧ ∃ t, sg.term = some t))
    (hr : EvalLXPS s f stk.reverse (liftInstrs is) l r) (hn : ¬ r.2.2.IsNormal)
    (hkl : KL body Fin b.seq.reverse ls r l₁) :
    Good body Fin ⟨.block b, stk, ls, s, f⟩ (l ++ l₁) := by
  obtain ⟨c, hc, hsg⟩ := seg_of_lookup hb
  refine ⟨c, l, l₁, r, hc, ?_, hkl, rfl⟩
  rcases his with rfl | ⟨rfl, t, ht⟩
  · exact (restAt_run hsg hr).1 hn
  · have hr' : EvalLXPS s f stk.reverse (liftInstrs (codeOf sg)) l r := by
      rw [MachineL.codeOf, ht, Option.toList_some, MachineLSeq.liftInstrs_append]
      exact (MachineLSeq.append hr _).1 hn
    exact (restAt_run hsg hr').1 hn

/-- The sink a trap, `return`, an uncaught exception or an exit stands for. -/
theorem fin_of_sink {body : Expr} {Fin : Store H × Frame × POut → Prop} {st : MState H}
    {l : List (SCall H)} (hG : Good body Fin st l) (hs : st.node.IsSink) {r : Store H × Frame × POut}
    (hE : EndRel st r) : l = [] ∧ Fin r := by
  obtain ⟨node, stk, ls, s, f⟩ := st
  cases node <;> simp only [Target.IsSink] at hs <;> exact ⟨hG.1, hG.2 r hE⟩

/-! ## The native rules of the structured instructions -/

theorem take_append_len {us W : List Val} {n : Nat} (h : us.length = n) :
    (us ++ W).take n = us ∧ (us ++ W).drop n = W := by
  subst h; simp

/-- **A structured instruction other than `if`, natively**: its arm ran from the parameters `us`
to `r₀`, and its frame carried `r₀` on (`WrapL`), so the instruction runs from `us` over the
frame's outer values. -/
theorem wrap_sound {L : LFrame} {t : Instr} {rest c : List Instr} {a : Nat}
    (hk : StructKind t L.bt L.loop L.tryT L.catches) (harm : armOf t a = some c)
    (hnif : ∀ bt' tt ee, t ≠ .if_ bt' tt ee) {s : Store H} {f : Frame} {us : List Val}
    {np nr : Nat} (har : arity f L.bt = some (np, nr)) (hus : us.length = np)
    {l₀ l₁ : List (SCall H)} {r₀ r₁ : Store H × Frame × POut}
    (hrun : EvalLXPS s f us (liftInstrs c) l₀ r₀) (hw : WrapL L t rest r₀ l₁ r₁) :
    EvalLXPS s f (us ++ L.outer.reverse) (liftInstr t :: liftInstrs rest) (l₀ ++ l₁) r₁ := by
  have hmod := MachineLSeq.module_eq hrun
  obtain ⟨htk, hdr⟩ := take_append_len (W := L.outer.reverse) hus
  rw [← htk] at hrun
  obtain ⟨ar, ou, lp, tt, cs, bt⟩ := L
  simp only at hk har hw hrun hdr ⊢
  cases hk with
  | block =>
    rename_i bb
    obtain rfl : c = bb := by
      (rcases a with _ | _ | a <;> simp [armOf] at harm); exact harm.symm
    cases hw with
    | ok hloop har' hvs hk' =>
      rw [arity_congr hmod, har] at har'; cases har'
      exact .blockOk har hrun hvs (by rwa [hdr])
    | loopOk hloop => cases hloop
    | loopBack hloop => cases hloop
    | brk => simpa [liftInstr] using EvalLXPS.blockBrk har hrun
    | esc ho _ => simpa [liftInstr] using EvalLXPS.blockEsc har hrun ho
    | catch_ hT => cases hT
    | rethrow hT => cases hT
  | loop =>
    rename_i bb
    obtain rfl : c = bb := by
      (rcases a with _ | _ | a <;> simp [armOf] at harm); exact harm.symm
    cases hw with
    | ok hloop => cases hloop
    | loopOk hloop har' hk' =>
      rw [arity_congr hmod, har] at har'; cases har'
      exact .loopOk har hrun (by rwa [hdr])
    | loopBack hloop har' hk' =>
      rw [arity_congr hmod, har] at har'; cases har'
      exact .loopBack har hrun (by rwa [hdr])
    | brk => simpa [liftInstr] using EvalLXPS.loopBrk har hrun
    | esc ho _ => simpa [liftInstr] using EvalLXPS.loopEsc har hrun ho
    | catch_ hT => cases hT
    | rethrow hT => cases hT
  | if_ => exact absurd rfl (hnif _ _ _)
  | tryTable =>
    rename_i bb
    obtain rfl : c = bb := by
      (rcases a with _ | _ | a <;> simp [armOf] at harm); exact harm.symm
    cases hw with
    | ok hloop har' hvs hk' =>
      rw [arity_congr hmod, har] at har'; cases har'
      exact .tryOk har hrun hvs (by rwa [hdr])
    | loopOk hloop => cases hloop
    | loopBack hloop => cases hloop
    | brk => simpa [liftInstr] using EvalLXPS.tryBrk har hrun
    | esc ho hnt => simpa [liftInstr] using EvalLXPS.tryEsc har hrun ho (hnt rfl)
    | catch_ _ hc => simpa [liftInstr, hdr] using EvalLXPS.tryCatch har hrun hc
    | rethrow _ hc => simpa [liftInstr] using EvalLXPS.tryRethrow har hrun hc

/-- **`if`, natively**: the condition `k` on top chose the arm `a`, which ran from `us`. -/
theorem wrap_sound_if {L : LFrame} {bt : BlockType} {tt ee rest c : List Instr} {a : Nat}
    (hk : StructKind (.if_ bt tt ee) L.bt L.loop L.tryT L.catches)
    (harm : armOf (.if_ bt tt ee) a = some c) {k : BitVec 32} (hka : (k != 0) = (a == 0))
    {s : Store H} {f : Frame} {us : List Val} {np nr : Nat} (har : arity f L.bt = some (np, nr))
    (hus : us.length = np) {l₀ l₁ : List (SCall H)} {r₀ r₁ : Store H × Frame × POut}
    (hrun : EvalLXPS s f us (liftInstrs c) l₀ r₀) (hw : WrapL L (.if_ bt tt ee) rest r₀ l₁ r₁) :
    EvalLXPS s f (.i32 k :: (us ++ L.outer.reverse)) (liftInstr (.if_ bt tt ee) :: liftInstrs rest)
      (l₀ ++ l₁) r₁ := by
  have hmod := MachineLSeq.module_eq hrun
  obtain ⟨htk, hdr⟩ := take_append_len (W := L.outer.reverse) hus
  obtain ⟨ar, ou, lp, tt', cs, bt'⟩ := L
  simp only at hk har hw hdr ⊢
  cases hk
  have hc : EvalLXPS s f (.i32 k :: (us ++ ou.reverse)) [] [] (s, f, .flow (.normal (.i32 k :: (us ++ ou.reverse)))) :=
    .nil
  have htr : truthy (.i32 k) = some (a == 0) := by
    simp [truthy, Val.i32, asInt, ← hka]
    exact ⟨k, rfl, rfl⟩
  have harm' : (if (a == 0) then liftInstrs tt else liftInstrs ee) = liftInstrs c := by
    rcases a with _ | _ | a <;> simp [armOf] at harm <;> subst harm <;> rfl
  rw [← harm', ← htk] at hrun
  cases hw with
  | ok hloop har' hvs hk' =>
    rw [arity_congr hmod, har] at har'; cases har'
    simpa [liftInstr] using EvalLXPS.ifOk hc htr har hrun hvs (by rwa [hdr])
  | loopOk hloop => cases hloop
  | loopBack hloop => cases hloop
  | brk => simpa [liftInstr] using EvalLXPS.ifBrk hc htr har hrun
  | esc ho _ => simpa [liftInstr] using EvalLXPS.ifEsc hc htr har hrun ho
  | catch_ hT => cases hT
  | rethrow hT => cases hT

theorem kl_frame_inv {body : Expr} {Fin : Store H × Frame × POut → Prop} {m a : Nat}
    {rp : List SeqStep} {L : LFrame} {ls : List LFrame} {r₀ : Store H × Frame × POut}
    {l : List (SCall H)} (h : KL body Fin ((m, a) :: rp) (L :: ls) r₀ l) :
    ∃ (pc : List Instr) (sg : Segment) (t : Instr) (c : List Instr)
      (r₁ : Store H × Frame × POut) (l₁ l₂ : List (SCall H)),
      seqAt body rp.reverse = some pc ∧ (segment pc)[m]? = some sg ∧ sg.term = some t ∧
      armOf t a = some c ∧ WrapL L t (restAt pc (m + 1)) r₀ l₁ r₁ ∧
      KL body Fin rp ls r₁ l₂ ∧ l = l₁ ++ l₂ := by
  cases h with
  | frame hpc hsg ht harm _ hw hrest => exact ⟨_, _, _, _, _, _, _, hpc, hsg, ht, harm, hw, hrest, rfl⟩

theorem arity_of_blockType {f : Frame} {bt : BlockType} {t₁ t₂ : List Validation.CValType}
    (h : f.module.blockType? bt = some (t₁, t₂)) : arity f bt = some (t₁.length, t₂.length) := by
  cases bt with
  | empty => simp [ModuleInst.blockType?] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | value t => simp [ModuleInst.blockType?] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | typeIdx x =>
    simp only [ModuleInst.blockType?] at h
    simp [arity, Frame.type?, h]

/-- **Entering a structured terminator** (`MStepL.enter`). -/
theorem enter_good {body : Expr} {Fin : Store H × Frame × POut → Prop} {b : BlockId}
    {sg : Segment} {stk stk₁ ws us : List Val} {ls : List LFrame} {s s₁ : Store H}
    {f f₁ : Frame} {i : Instr} {a : Nat} {c : List Instr} {bt : BlockType}
    {t₁ t₂ : List Validation.CValType} {loop tryT : Bool} {cs : List Catch} {l l' : List (SCall H)}
    {st' : MState H} (hok : FramesOk body b.seq.reverse ls)
    (hb : lookup body b = some sg) (ht : sg.term = some i) (harm : armOf i a = some c)
    (hkind : StructKind i bt loop tryT cs)
    (hr : EvalLXPS s f stk.reverse (liftInstrs sg.body) l (s₁, f₁, .flow (.normal stk₁)))
    (hcond : CondArm i stk₁.reverse a ws us)
    (hbt : f₁.module.blockType? bt = some (t₁, t₂)) (hm : us.length = t₁.length)
    (hg : gotoN (entry body (b.seq ++ [(b.idx, a)]) 0) (b.seq.length + 1)
      (⟨labelArity loop t₁ t₂, ws, loop, tryT, cs, bt⟩ :: ls) us s₁ f₁ = some st')
    (hG : Good body Fin st' l') : Good body Fin ⟨.block b, stk, ls, s, f⟩ (l ++ l') := by
  obtain ⟨pc, hpc, hsg⟩ := seg_of_lookup hb
  have hcarm : seqAt body (b.seq ++ [(b.idx, a)]) = some c := by
    rw [Proofs.Machine.seqAt_append]; simp [hpc, hsg, ht, harm]
  set L : LFrame := ⟨labelArity loop t₁ t₂, ws, loop, tryT, cs, bt⟩ with hLdef
  have hokA : FramesOk body (b.seq ++ [(b.idx, a)]).reverse (L :: ls) := by
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, FramesOk]
    exact ⟨⟨pc, sg, i, c, by simpa using hpc, hsg, ht, harm, hkind⟩, hok⟩
  obtain ⟨l₀, l₁, r₀, hrun, hkl, rfl⟩ :=
    entry_good hokA hcarm (by simpa using hg) hG
  rw [restAt_zero] at hrun
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append] at hkl
  obtain ⟨pc', sg', t', c', r₁, l₁₁, l₁₂, hpc', hsg', ht', harm', hw, hrest, rfl⟩ :=
    kl_frame_inv hkl
  rw [List.reverse_reverse, hpc] at hpc'; cases hpc'
  rw [hsg] at hsg'; cases hsg'
  rw [ht] at ht'; cases ht'
  have har := arity_of_blockType (f := f₁) hbt
  have hus : us.reverse.length = t₁.length := by simpa using hm
  have hnat : EvalLXPS s₁ f₁ stk₁ (liftInstr i :: liftInstrs (restAt pc (b.idx + 1)))
      (l₀ ++ l₁₁) r₁ := by
    generalize hV : stk₁.reverse = V at hcond
    have hstk : stk₁ = V.reverse := by rw [← hV, List.reverse_reverse]
    subst hstk
    cases hcond with
    | plain hi =>
      simpa [List.reverse_append] using wrap_sound hkind harm hi har hus hrun hw
    | @ifTrue bt' tt ee _ _ k hk =>
      have hka : (k != 0) = (0 == 0) := by simpa using hk
      simpa [List.reverse_append, Val.i32] using
        wrap_sound_if hkind harm hka har hus hrun hw
    | @ifFalse bt' tt ee =>
      have hka : ((0 : BitVec 32) != 0) = (1 == 0) := by decide
      simpa [List.reverse_append, Val.i32] using
        wrap_sound_if hkind harm hka har hus hrun hw
  refine ⟨pc, l ++ (l₀ ++ l₁₁), l₁₂, r₁, hpc, ?_, hrest, by simp⟩
  have hsplit : liftInstrs (restAt pc b.idx) =
      liftInstrs sg.body ++ (liftInstr i :: liftInstrs (restAt pc (b.idx + 1))) := by
    rw [restAt_cons hsg, Segment.instrs, ht]
    simp [MachineLSeq.liftInstrs_append, liftInstrs]
  rw [hsplit]
  exact (MachineLSeq.append hr _).2 _ _ _ rfl _ _ hnat

/-! ## Branches -/

/-- **After leaving the frame of `(m, a)`** (its block's continuation `contRev`, reached natively
at the parent's depth): the parent's rest from `m + 1` runs natively and its outcome is carried
out. -/
theorem after_frame {body : Expr} {Fin : Store H × Frame × POut → Prop} {m a : Nat}
    {rp : List SeqStep} {ls : List LFrame} {pc : List Instr} {W : List Val} {s : Store H}
    {f : Frame} {st' : MState H} {l : List (SCall H)} (hok : FramesOk body rp ls)
    (hpc : seqAt body rp.reverse = some pc)
    (hg : gotoN (contRev body ((m, a) :: rp)) rp.length ls W s f = some st')
    (hG : Good body Fin st' l) :
    ∃ (l₁ l₂ : List (SCall H)) (r₁ : Store H × Frame × POut),
      EvalLXPS s f W.reverse (liftInstrs (restAt pc (m + 1))) l₁ r₁ ∧
      KL body Fin rp ls r₁ l₂ ∧ l = l₁ ++ l₂ := by
  unfold contRev at hg
  split at hg
  · rw [show rp.length = (⟨rp.reverse, m + 1⟩ : BlockId).seq.length by simp] at hg
    have := gotoN_block hg
    subst this
    obtain ⟨c', l₀, l₁, r₀, hc', hrun, hkl, rfl⟩ := hG
    simp only at hc' hrun hkl
    rw [hpc] at hc'; cases hc'
    exact ⟨l₀, l₁, r₀, hrun, by simpa using hkl, rfl⟩
  · next hnone =>
    have hend : (segment pc)[m + 1]? = none := by
      rw [lookup_eq] at hnone
      simpa [hpc] using hnone
    rw [restAt_end hend]
    exact ⟨[], l, _, .nil, cont_good rp ls W s f st' l hok hg hG, rfl⟩

/-- `branchN` relative to the reversed path. -/
def branchR (body : Expr) (rp : List SeqStep) (ls : List LFrame) (k : Nat) (L : LFrame)
    (V : List Val) (s : Store H) (f : Frame) : Option (MState H) :=
  (arity f L.bt).bind fun a =>
    if L.loop then
      if a.1 ≤ V.length then
        gotoN ((labelsRev body rp).getD k .invalid) (rp.length - k) (L :: ls.drop (k + 1))
          (topVals a.1 V) s f
      else none
    else
      gotoN ((labelsRev body rp).getD k .invalid) (rp.length - (k + 1)) (ls.drop (k + 1))
        (L.outer ++ topVals a.2 V) s f

theorem branchN_eq (body : Expr) (b : BlockId) (ls : List LFrame) (k : Nat) (L : LFrame)
    (V : List Val) (s : Store H) (f : Frame) :
    branchN body b ls k L V s f = branchR body b.seq.reverse ls k L V s f := by
  simp [branchN, branchR, labels]

theorem branchR_succ (body : Expr) (x : SeqStep) (rp : List SeqStep) (L₀ : LFrame)
    (ls : List LFrame) (k : Nat) (L : LFrame) (V : List Val) (s : Store H) (f : Frame) :
    branchR body (x :: rp) (L₀ :: ls) (k + 1) L V s f = branchR body rp ls k L V s f := by
  obtain ⟨m, a⟩ := x
  simp [branchR, labelsRev]

theorem structKind_loop {t : Instr} {bt : BlockType} {tryT : Bool} {cs : List Catch}
    (h : StructKind t bt true tryT cs) : ∀ bt' tt ee, t ≠ .if_ bt' tt ee := by
  cases h; intros; exact nofun

/-- **A branch to the enclosing label `k`** (`branchR`), natively: `brk` passes the inner frames
(`blockBrk`, …), then the label's frame re-enters its loop (`loopBack`) or continues after it
(`blockOk`, …). -/
theorem br_kl {body : Expr} {Fin : Store H × Frame × POut → Prop} :
    ∀ (k : Nat) (rp : List SeqStep) (ls : List LFrame) (L : LFrame) (ws : List Val)
      (s : Store H) (f : Frame) (st' : MState H) (l : List (SCall H)), FramesOk body rp ls →
      ls[k]? = some L → branchR body rp ls k L ws.reverse s f = some st' →
      Good body Fin st' l → KL body Fin rp ls (s, f, .flow (.brk k ws)) l
  | _, [], [], _, _, _, _, _, _, _, hL, _, _ => by simp at hL
  | _, [], _ :: _, _, _, _, _, _, _, h, _, _, _ => by simp [FramesOk] at h
  | _, _ :: _, [], _, _, _, _, _, _, h, _, _, _ => by simp [FramesOk] at h
  | k + 1, x :: rp, L₀ :: ls, L, ws, s, f, st', l, hok, hL, hg, hG => by
    obtain ⟨m, a⟩ := x
    obtain ⟨⟨pc, sg, t, c, hpc, hsg, ht, harm, hkind⟩, hok'⟩ := hok
    rw [branchR_succ] at hg
    have hkl := br_kl k rp ls L ws s f st' l hok' (by simpa using hL) hg hG
    simpa using KL.frame hpc hsg ht harm hkind (WrapL.brk (s := s) (f := f) (k := k) (vs := ws)) hkl
  | 0, (m, a) :: rp, L₀ :: ls, L, ws, s, f, st', l, hok, hL, hg, hG => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hL
    subst hL
    have hlev := Proofs.Machine.levelLoop_of_framesOk 0 ((m, a) :: rp) (L₀ :: ls) hok rfl
    obtain ⟨⟨pc, sg, t, c, hpc, hsg, ht, harm, hkind⟩, hok'⟩ := hok
    simp only [branchR, Option.bind_eq_some_iff] at hg
    obtain ⟨⟨np, nr⟩, har, hg⟩ := hg
    have hd : ((m, a) :: rp).drop 0 = (m, a) :: rp := rfl
    rw [Proofs.Machine.labelsRev_getD 0 _ hd] at hg
    simp only [levelLoop, List.drop_zero] at hlev
    rw [hlev] at hg
    cases hloop : L₀.loop
    · simp only [hloop, Bool.false_eq_true, ↓reduceIte, List.length_cons,
        Nat.add_sub_cancel] at hg
      obtain ⟨l₁, l₂, r₁, hrun, hkl, rfl⟩ := after_frame hok' hpc hg hG
      rw [List.reverse_append, topVals_reverse, List.reverse_reverse] at hrun
      exact .frame hpc hsg ht harm hkind (.ok hloop har rfl hrun) hkl
    · simp only [hloop, ↓reduceIte] at hg
      split at hg
      · next hle =>
        have hcarm : seqAt body (rp.reverse ++ [(m, a)]) = some c := by
          rw [Proofs.Machine.seqAt_append]; simp [hpc, hsg, ht, harm]
        have hokA : FramesOk body (rp.reverse ++ [(m, a)]).reverse (L₀ :: ls) := by
          simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
            List.singleton_append, List.reverse_reverse, FramesOk]
          exact ⟨⟨pc, sg, t, c, hpc, hsg, ht, harm, hkind⟩, hok'⟩
        obtain ⟨l₀, l₁, r₀, hrun, hkl0, rfl⟩ :=
          entry_good hokA hcarm (by simpa using hg) hG
        rw [restAt_zero] at hrun
        simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
          List.singleton_append, List.reverse_reverse] at hkl0
        obtain ⟨pc', sg', t', c', r₁, l₁₁, l₁₂, hpc', hsg', ht', harm', hw, hrest, rfl⟩ :=
          kl_frame_inv hkl0
        rw [hpc] at hpc'; cases hpc'
        rw [hsg] at hsg'; cases hsg'
        rw [ht] at ht'; cases ht'
        have hnif := structKind_loop (hloop ▸ hkind)
        rw [topVals_reverse, List.reverse_reverse] at hrun
        have hlen : (ws.take np).length = np := by
          simp only [List.length_take, List.length_reverse] at hle ⊢; omega
        have hnat := wrap_sound hkind harm hnif har hlen hrun hw
        simpa [List.append_assoc] using
          KL.frame hpc hsg ht harm hkind (.loopBack hloop har hnat) (by simpa using hrest)
      · cases hg

/-- **A branch to the function label**: `brk` passes every frame, ending the body in `brk 0`. -/
theorem kl_brOut {body : Expr} {Fin : Store H × Frame × POut → Prop} {s : Store H} {f : Frame}
    {ws : List Val} (hF : Fin (s, f, .flow (.brk 0 ws))) :
    ∀ (rp : List SeqStep) (ls : List LFrame), FramesOk body rp ls →
      KL body Fin rp ls (s, f, .flow (.brk ls.length ws)) []
  | [], [], _ => .top hF
  | [], _ :: _, h => by simp [FramesOk] at h
  | _ :: _, [], h => by simp [FramesOk] at h
  | (m, a) :: rp, L :: ls, hok => by
    obtain ⟨⟨pc, sg, t, c, hpc, hsg, ht, harm, hkind⟩, hok'⟩ := hok
    simpa using KL.frame hpc hsg ht harm hkind WrapL.brk (kl_brOut hF rp ls hok')

end Silmaril.Wasm.Cfg.Proofs.MachineLFwd
