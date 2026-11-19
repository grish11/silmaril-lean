module

public import Silmaril.Proofs.Wasm.Cfg.MachineLFwd
public import Silmaril.Proofs.Wasm.Cfg.MachineLDivB

@[expose] public section

/-!
# The forward invariant relative to a frame (H2, proofs)

`MachineLFwd`'s invariant `Good`/`KL` carries a native outcome out of every label frame down to the
function body. Here the carrying stops at a **base**: a sequence `rp₀` (reversed path) with its
frames `ls₀`, the outcome of that sequence satisfying `Fin` (`KLR.base`). `GoodR` is `Good` over
`KLR`, with no sinks (a sink is never inside a frame).

The steps that keep the invariant are those **staying at depth `δ`** (`MStepS`): falling through,
branching or catching to a label strictly inside the innermost `δ` frames' bottom, and entering an
arm, each landing at depth at least `δ`. With `δ = rp₀.length`, staying runs keep `GoodR`
backwards (`run_goodR`), as `MachineLFwd.run_good` does for whole runs.

A step staying one level above the base but not at the base's depth **leaves** the base: it falls
out of the base's sequence, or branches to the base's own label (a loop's re-entry included).
`leave_good`: the state before it stands for the base's outcome leading to the step's target
(`ExitB`). `arm_fwd`: a staying run from an arm's entry, then a leaving step, is a native run of
the arm, with exactly the run's log, to such an outcome.
-/

namespace Silmaril.Wasm.Cfg.Proofs.MachineLRel

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Abstract (EvalLXPS SCall)
open Silmaril.Wasm.Abstract.CallXP (POut)
open Silmaril.Wasm.Cfg.Region (Catches)
open Silmaril.Wasm.Cfg.Proofs.Machine (restAt_cons restAt_end restAt_zero seg_of_lookup lookup_eq)
open Silmaril.Wasm.Cfg.Proofs.MachineLFwd

variable {H : Type}

/-! ## Steps staying at depth `δ` -/

/-- **A dispatch staying at depth `δ`**: falling through, a branch or a caught exception's branch
to a label inside the innermost frames above the bottom `δ`, landing at depth at least `δ`. -/
inductive DispS (body : Expr) (δ : Nat) (b : BlockId) (ls : List LFrame) :
    Store H × Frame × POut → MState H → Prop where
  | next {s : Store H} {f : Frame} {ws : List Val} {st' : MState H}
      (hg : gotoN (entry body b.seq (b.idx + 1)) b.seq.length ls ws.reverse s f = some st')
      (hδ : δ ≤ st'.lbls.length) :
      DispS body δ b ls (s, f, .flow (.normal ws)) st'
  | br {s : Store H} {f : Frame} {ws : List Val} {k : Nat} {L : LFrame} {st' : MState H}
      (hL : ls[k]? = some L) (hg : branchN body b ls k L ws s f = some st')
      (hk : k + δ < ls.length) (hδ : δ ≤ st'.lbls.length) :
      DispS body δ b ls (s, f, .flow (.brk k ws)) st'
  | catch_ {s : Store H} {f : Frame} {a j : Nat} {us : List Val} {L L' : LFrame} {l : LabelIdx}
      {st' : MState H}
      (hpass : ∀ (k : Nat) (L : LFrame), k < j → ls[k]? = some L → L.tryT = true →
        Catches s f a L.catches none)
      (hL : ls[j]? = some L) (hT : L.tryT = true) (hc : Catches s f a L.catches (some (us, l)))
      (hL' : ls[j + 1 + l.toNat]? = some L')
      (hg : branchN body b ls (j + 1 + l.toNat) L' (us.reverse ++ L.outer.reverse) s f = some st')
      (hk : j + 1 + l.toNat + δ < ls.length) (hδ : δ ≤ st'.lbls.length) :
      DispS body δ b ls (s, f, .flow (.throw a)) st'

/-- **A logged step staying at depth `δ`**. -/
inductive MStepS (body : Expr) (δ : Nat) : MState H → List (SCall H) → MState H → Prop where
  | run {b : BlockId} {sg : Segment} {stk : List Val} {ls : List LFrame} {s : Store H}
      {f : Frame} {l : List (SCall H)} {r : Store H × Frame × POut} {st' : MState H}
      (hb : lookup body b = some sg) (ht : ∀ i, sg.term = some i → ¬ Instr.IsStruct i)
      (hr : EvalLXPS s f stk.reverse (liftInstrs (codeOf sg)) l r) (hd : DispS body δ b ls r st') :
      MStepS body δ ⟨.block b, stk, ls, s, f⟩ l st'
  | abort {b : BlockId} {sg : Segment} {stk : List Val} {ls : List LFrame} {s : Store H}
      {f : Frame} {l : List (SCall H)} {r : Store H × Frame × POut} {st' : MState H}
      (hb : lookup body b = some sg) (hr : EvalLXPS s f stk.reverse (liftInstrs sg.body) l r)
      (hn : ¬ r.2.2.IsNormal) (hd : DispS body δ b ls r st') :
      MStepS body δ ⟨.block b, stk, ls, s, f⟩ l st'
  | enter {b : BlockId} {sg : Segment} {stk : List Val} {V V' : List Val} {ls : List LFrame}
      {s s₁ : Store H} {f f₁ : Frame} {i : Instr} {a : Nat} {c : List Instr} {bt : BlockType}
      {np nr : Nat} {loop tryT : Bool} {cs : List Catch} {l : List (SCall H)} {st' : MState H}
      (hb : lookup body b = some sg) (ht : sg.term = some i) (harm : armOf i a = some c)
      (hkind : StructKind i bt loop tryT cs)
      (hr : EvalLXPS s f stk.reverse (liftInstrs sg.body) l (s₁, f₁, .flow (.normal V)))
      (hsel : ArmSel i V a V') (har : Binaryen.arity f₁ bt = some (np, nr))
      (hg : gotoN (entry body (b.seq ++ [(b.idx, a)]) 0) (b.seq.length + 1)
          (⟨if loop then np else nr, (V'.drop np).reverse, loop, tryT, cs, bt⟩ :: ls)
          (V'.take np).reverse s₁ f₁ = some st')
      (hδ : δ ≤ st'.lbls.length) :
      MStepS body δ ⟨.block b, stk, ls, s, f⟩ l st'

theorem DispS.dispL {body : Expr} {δ : Nat} {b : BlockId} {ls : List LFrame}
    {r : Store H × Frame × POut} {st' : MState H} (h : DispS body δ b ls r st') :
    DispL body b ls r st' := by
  cases h with
  | next hg => exact .next hg
  | br hL hg => exact .br hL hg
  | catch_ hpass hL hT hc hL' hg => exact .catch_ hpass hL hT hc hL' hg

theorem DispS.depth {body : Expr} {δ : Nat} {b : BlockId} {ls : List LFrame}
    {r : Store H × Frame × POut} {st' : MState H} (h : DispS body δ b ls r st') :
    δ ≤ st'.lbls.length := by
  cases h with
  | next _ hδ => exact hδ
  | br _ _ _ hδ => exact hδ
  | catch_ _ _ _ _ _ _ _ hδ => exact hδ

theorem MStepS.stepL {body : Expr} {δ : Nat} {st st' : MState H} {l : List (SCall H)}
    (h : MStepS body δ st l st') : MStepL body st l st' := by
  cases h with
  | run hb ht hr hd => exact .run hb ht hr hd.dispL
  | abort hb hr hn hd => exact .abort hb hr hn hd.dispL
  | enter hb ht harm hkind hr hsel har hg => exact .enter hb ht harm hkind hr hsel har hg

theorem MStepS.depth {body : Expr} {δ : Nat} {st st' : MState H} {l : List (SCall H)}
    (h : MStepS body δ st l st') : δ ≤ st'.lbls.length := by
  cases h with
  | run _ _ _ hd => exact hd.depth
  | abort _ _ _ hd => exact hd.depth
  | enter _ _ _ _ _ _ _ _ hδ => exact hδ

/-- **Runs staying at depth `δ`**. -/
inductive MRunS (body : Expr) (δ : Nat) : MState H → List (SCall H) → MState H → Prop where
  | refl (st : MState H) : MRunS body δ st [] st
  | step {st st₁ st₂ : MState H} {l₁ l₂ : List (SCall H)} (h : MStepS body δ st l₁ st₁)
      (hr : MRunS body δ st₁ l₂ st₂) : MRunS body δ st (l₁ ++ l₂) st₂

/-! ## The invariant relative to a base -/

/-- **Carrying an outcome out of the label frames down to a base** `(rp₀, ls₀)`, where the
outcome of the base's sequence satisfies `Fin`. -/
inductive KLR (body : Expr) (Fin : Store H × Frame × POut → Prop) (rp₀ : List SeqStep)
    (ls₀ : List LFrame) :
    List SeqStep → List LFrame → Store H × Frame × POut → List (SCall H) → Prop where
  | base {r : Store H × Frame × POut} (h : Fin r) : KLR body Fin rp₀ ls₀ rp₀ ls₀ r []
  | frame {m a : Nat} {rp : List SeqStep} {L : LFrame} {ls : List LFrame} {pc : List Instr}
      {sg : Segment} {t : Instr} {c : List Instr} {r₀ r₁ : Store H × Frame × POut}
      {l₁ l₂ : List (SCall H)} (hpc : seqAt body rp.reverse = some pc)
      (hsg : (segment pc)[m]? = some sg) (ht : sg.term = some t) (harm : armOf t a = some c)
      (hk : StructKind t L.bt L.loop L.tryT L.catches)
      (hw : WrapL L t (restAt pc (m + 1)) r₀ l₁ r₁) (hrest : KLR body Fin rp₀ ls₀ rp ls r₁ l₂) :
      KLR body Fin rp₀ ls₀ ((m, a) :: rp) (L :: ls) r₀ (l₁ ++ l₂)

/-- **The relative invariant**: at a block, the rest of its sequence runs natively and `KLR`
carries the outcome down to the base. -/
def GoodR (body : Expr) (Fin : Store H × Frame × POut → Prop) (rp₀ : List SeqStep)
    (ls₀ : List LFrame) (st : MState H) (l : List (SCall H)) : Prop :=
  match st.node with
  | .block b => ∃ (c : List Instr) (l₀ l₁ : List (SCall H)) (r₀ : Store H × Frame × POut),
      seqAt body b.seq = some c ∧
      EvalLXPS st.store st.frame st.stk.reverse (liftInstrs (restAt c b.idx)) l₀ r₀ ∧
      KLR body Fin rp₀ ls₀ b.seq.reverse st.lbls r₀ l₁ ∧ l = l₀ ++ l₁
  | _ => False

/-! ## Keeping the invariant backwards -/

/-- **The continuation of a finished sequence** (`contRev`, reached natively by `gotoN`): the
sequence's normal end with the stack `W` is carried out by `KL`. -/
theorem cont_goodR {body : Expr} {Fin : Store H × Frame × POut → Prop} {rp₀ : List SeqStep} {ls₀ : List LFrame} :
    ∀ (rp : List SeqStep) (ls : List LFrame) (W : List Val) (s : Store H) (f : Frame)
      (st' : MState H) (l : List (SCall H)), FramesOk body rp ls →
      gotoN (contRev body rp) rp.length ls W s f = some st' → GoodR body Fin rp₀ ls₀ st' l →
      KLR body Fin rp₀ ls₀ rp ls (s, f, .flow (.normal W.reverse)) l
  | [], [], W, s, f, st', l, _, hg, hG => by
    simp only [contRev, gotoN, depthT, List.length_nil, Nat.sub_self, popN, Option.map_some,
      Option.some.injEq] at hg
    subst hg
    simp [GoodR] at hG
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
      have hkl := cont_goodR rp ls _ s f st' l hok' hg' hG
      have hw : WrapL L t (restAt pc (m + 1)) (s, f, .flow (.normal W.reverse)) []
          (s, f, .flow (.normal (L.outer ++ topVals nr W).reverse)) :=
        wrap_fall har (by rw [hnil]; exact .nil)
      simpa using KLR.frame hpc hsg ht harm hkind hw hkl


/-- **Reaching position `i` of the sequence at `p`** natively (`gotoN (entry …)`): the rest of
the sequence from `i` runs natively and its outcome is carried out by `KL`. -/
theorem entry_goodR {body : Expr} {Fin : Store H × Frame × POut → Prop} {rp₀ : List SeqStep} {ls₀ : List LFrame} {p : List SeqStep}
    {c : List Instr} {i : Nat} {ls : List LFrame} {W : List Val} {s : Store H} {f : Frame}
    {st' : MState H} {l : List (SCall H)} (hok : FramesOk body p.reverse ls)
    (hc : seqAt body p = some c) (hg : gotoN (entry body p i) p.length ls W s f = some st')
    (hG : GoodR body Fin rp₀ ls₀ st' l) :
    ∃ (l₀ l₁ : List (SCall H)) (r₀ : Store H × Frame × POut),
      EvalLXPS s f W.reverse (liftInstrs (restAt c i)) l₀ r₀ ∧
      KLR body Fin rp₀ ls₀ p.reverse ls r₀ l₁ ∧ l = l₀ ++ l₁ := by
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
    exact cont_goodR p.reverse ls W s f st' l hok (by simpa [cont] using hg) hG


/-- **Falling through** (`DispL.next`). -/
theorem next_goodR {body : Expr} {Fin : Store H × Frame × POut → Prop} {rp₀ : List SeqStep} {ls₀ : List LFrame} {b : BlockId}
    {sg : Segment} {stk : List Val} {ls : List LFrame} {s s₁ : Store H} {f f₁ : Frame}
    {ws : List Val} {l l' : List (SCall H)} {st' : MState H} (hok : FramesOk body b.seq.reverse ls)
    (hb : lookup body b = some sg)
    (hr : EvalLXPS s f stk.reverse (liftInstrs (codeOf sg)) l (s₁, f₁, .flow (.normal ws)))
    (hg : gotoN (entry body b.seq (b.idx + 1)) b.seq.length ls ws.reverse s₁ f₁ = some st')
    (hG : GoodR body Fin rp₀ ls₀ st' l') : GoodR body Fin rp₀ ls₀ ⟨.block b, stk, ls, s, f⟩ (l ++ l') := by
  obtain ⟨c, hc, hsg⟩ := seg_of_lookup hb
  obtain ⟨l₀, l₁, r₀, hrun, hkl, rfl⟩ := entry_goodR (by simpa using hok) hc hg hG
  refine ⟨c, l ++ l₀, l₁, r₀, hc, ?_, hkl, by simp⟩
  exact (restAt_run hsg hr).2 _ _ _ rfl _ _ (by simpa using hrun)


/-- **A block whose straight-line code ends abruptly**: the rest of the sequence is skipped. -/
theorem abrupt_goodR {body : Expr} {Fin : Store H × Frame × POut → Prop} {rp₀ : List SeqStep} {ls₀ : List LFrame} {b : BlockId}
    {sg : Segment} {stk : List Val} {ls : List LFrame} {s : Store H} {f : Frame}
    {l l₁ : List (SCall H)} {r : Store H × Frame × POut} {is : List Instr}
    (hb : lookup body b = some sg) (his : is = MachineL.codeOf sg ∨ (is = sg.body ∧ ∃ t, sg.term = some t))
    (hr : EvalLXPS s f stk.reverse (liftInstrs is) l r) (hn : ¬ r.2.2.IsNormal)
    (hkl : KLR body Fin rp₀ ls₀ b.seq.reverse ls r l₁) :
    GoodR body Fin rp₀ ls₀ ⟨.block b, stk, ls, s, f⟩ (l ++ l₁) := by
  obtain ⟨c, hc, hsg⟩ := seg_of_lookup hb
  refine ⟨c, l, l₁, r, hc, ?_, hkl, rfl⟩
  rcases his with rfl | ⟨rfl, t, ht⟩
  · exact (restAt_run hsg hr).1 hn
  · have hr' : EvalLXPS s f stk.reverse (liftInstrs (codeOf sg)) l r := by
      rw [MachineL.codeOf, ht, Option.toList_some, MachineLSeq.liftInstrs_append]
      exact (MachineLSeq.append hr _).1 hn
    exact (restAt_run hsg hr').1 hn


theorem kl_frame_invR {body : Expr} {Fin : Store H × Frame × POut → Prop} {rp₀ : List SeqStep} {ls₀ : List LFrame} {m a : Nat}
    {rp : List SeqStep} {L : LFrame} {ls : List LFrame} {r₀ : Store H × Frame × POut}
    {l : List (SCall H)} (h : KLR body Fin rp₀ ls₀ ((m, a) :: rp) (L :: ls) r₀ l)
    (hne : rp₀.length < rp.length + 1) :
    ∃ (pc : List Instr) (sg : Segment) (t : Instr) (c : List Instr)
      (r₁ : Store H × Frame × POut) (l₁ l₂ : List (SCall H)),
      seqAt body rp.reverse = some pc ∧ (segment pc)[m]? = some sg ∧ sg.term = some t ∧
      armOf t a = some c ∧ WrapL L t (restAt pc (m + 1)) r₀ l₁ r₁ ∧
      KLR body Fin rp₀ ls₀ rp ls r₁ l₂ ∧ l = l₁ ++ l₂ := by
  cases h with
  | base => simp at hne
  | frame hpc hsg ht harm _ hw hrest => exact ⟨_, _, _, _, _, _, _, hpc, hsg, ht, harm, hw, hrest, rfl⟩


/-- **Entering a structured terminator, given its arm's native run and the carrying of the arm's
outcome** (`MStepL.enter`). -/
theorem enter_core {body : Expr} {Fin : Store H × Frame × POut → Prop} {rp₀ : List SeqStep}
    {ls₀ : List LFrame} {b : BlockId}
    {sg : Segment} {stk V V' : List Val} {ls : List LFrame} {s s₁ : Store H}
    {f f₁ : Frame} {i : Instr} {a : Nat} {c : List Instr} {bt : BlockType} {np nr : Nat}
    {loop tryT : Bool} {cs : List Catch} {l l₀ l₁ : List (SCall H)} {r₀ : Store H × Frame × POut}
    (hlen : rp₀.length ≤ b.seq.length)
    (hb : lookup body b = some sg) (ht : sg.term = some i) (harm : armOf i a = some c)
    (hkind : StructKind i bt loop tryT cs)
    (hr : EvalLXPS s f stk.reverse (liftInstrs sg.body) l (s₁, f₁, .flow (.normal V)))
    (hsel : ArmSel i V a V') (har : arity f₁ bt = some (np, nr))
    (hrun : EvalLXPS s₁ f₁ (V'.take np) (liftInstrs c) l₀ r₀)
    (hkl : KLR body Fin rp₀ ls₀ ((b.idx, a) :: b.seq.reverse)
      (⟨if loop then np else nr, (V'.drop np).reverse, loop, tryT, cs, bt⟩ :: ls) r₀ l₁) :
    GoodR body Fin rp₀ ls₀ ⟨.block b, stk, ls, s, f⟩ (l ++ (l₀ ++ l₁)) := by
  obtain ⟨pc, hpc, hsg⟩ := seg_of_lookup hb
  set L : LFrame := ⟨if loop then np else nr, (V'.drop np).reverse, loop, tryT, cs, bt⟩ with hLdef
  obtain ⟨pc', sg', t', c', r₁, l₁₁, l₁₂, hpc', hsg', ht', harm', hw, hrest, rfl⟩ :=
    kl_frame_invR hkl (by simp; omega)
  rw [List.reverse_reverse, hpc] at hpc'; cases hpc'
  rw [hsg] at hsg'; cases hsg'
  rw [ht] at ht'; cases ht'
  have hdr : V'.drop np = L.outer.reverse := by simp [hLdef]
  have hnat : EvalLXPS s₁ f₁ V (liftInstr i :: liftInstrs (restAt pc (b.idx + 1)))
      (l₀ ++ l₁₁) r₁ := by
    cases hsel with
    | plain hi => exact wrap_sound hkind harm hi har hdr hrun hw
    | cond hb' => exact wrap_sound_if hkind harm hb' rfl har hdr hrun hw
  refine ⟨pc, l ++ (l₀ ++ l₁₁), l₁₂, r₁, hpc, ?_, hrest, by simp⟩
  have hsplit : liftInstrs (restAt pc b.idx) =
      liftInstrs sg.body ++ (liftInstr i :: liftInstrs (restAt pc (b.idx + 1))) := by
    rw [restAt_cons hsg, Segment.instrs, ht]
    simp [MachineLSeq.liftInstrs_append, liftInstrs]
  rw [hsplit]
  exact (MachineLSeq.append hr _).2 _ _ _ rfl _ _ hnat

/-- **Entering a structured terminator** (`MStepL.enter`), staying inside. -/
theorem enter_goodR {body : Expr} {Fin : Store H × Frame × POut → Prop} {rp₀ : List SeqStep}
    {ls₀ : List LFrame} {b : BlockId}
    {sg : Segment} {stk V V' : List Val} {ls : List LFrame} {s s₁ : Store H}
    {f f₁ : Frame} {i : Instr} {a : Nat} {c : List Instr} {bt : BlockType} {np nr : Nat}
    {loop tryT : Bool} {cs : List Catch} {l l' : List (SCall H)}
    {st' : MState H} (hok : FramesOk body b.seq.reverse ls) (hlen : rp₀.length ≤ b.seq.length)
    (hb : lookup body b = some sg) (ht : sg.term = some i) (harm : armOf i a = some c)
    (hkind : StructKind i bt loop tryT cs)
    (hr : EvalLXPS s f stk.reverse (liftInstrs sg.body) l (s₁, f₁, .flow (.normal V)))
    (hsel : ArmSel i V a V') (har : arity f₁ bt = some (np, nr))
    (hg : gotoN (entry body (b.seq ++ [(b.idx, a)]) 0) (b.seq.length + 1)
      (⟨if loop then np else nr, (V'.drop np).reverse, loop, tryT, cs, bt⟩ :: ls)
      (V'.take np).reverse s₁ f₁ = some st')
    (hG : GoodR body Fin rp₀ ls₀ st' l') :
    GoodR body Fin rp₀ ls₀ ⟨.block b, stk, ls, s, f⟩ (l ++ l') := by
  obtain ⟨pc, hpc, hsg⟩ := seg_of_lookup hb
  have hcarm : seqAt body (b.seq ++ [(b.idx, a)]) = some c := by
    rw [Proofs.Machine.seqAt_append]; simp [hpc, hsg, ht, harm]
  have hokA : FramesOk body (b.seq ++ [(b.idx, a)]).reverse
      (⟨if loop then np else nr, (V'.drop np).reverse, loop, tryT, cs, bt⟩ :: ls) := by
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, FramesOk]
    exact ⟨⟨pc, sg, i, c, by simpa using hpc, hsg, ht, harm, hkind⟩, hok⟩
  obtain ⟨l₀, l₁, r₀, hrun, hkl, rfl⟩ :=
    entry_goodR hokA hcarm (by simpa using hg) hG
  rw [restAt_zero, List.reverse_reverse] at hrun
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append] at hkl
  exact enter_core hlen hb ht harm hkind hr hsel har hrun hkl

/-- **After leaving the frame of `(m, a)`** (its block's continuation `contRev`, reached natively
at the parent's depth): the parent's rest from `m + 1` runs natively and its outcome is carried
out. -/
theorem after_frameR {body : Expr} {Fin : Store H × Frame × POut → Prop} {rp₀ : List SeqStep} {ls₀ : List LFrame} {m a : Nat}
    {rp : List SeqStep} {ls : List LFrame} {pc : List Instr} {W : List Val} {s : Store H}
    {f : Frame} {st' : MState H} {l : List (SCall H)} (hok : FramesOk body rp ls)
    (hpc : seqAt body rp.reverse = some pc)
    (hg : gotoN (contRev body ((m, a) :: rp)) rp.length ls W s f = some st')
    (hG : GoodR body Fin rp₀ ls₀ st' l) :
    ∃ (l₁ l₂ : List (SCall H)) (r₁ : Store H × Frame × POut),
      EvalLXPS s f W.reverse (liftInstrs (restAt pc (m + 1))) l₁ r₁ ∧
      KLR body Fin rp₀ ls₀ rp ls r₁ l₂ ∧ l = l₁ ++ l₂ := by
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
    exact ⟨[], l, _, .nil, cont_goodR rp ls W s f st' l hok hg hG, rfl⟩


/-- **A branch to the enclosing label `k`** (`branchR`), natively: `brk` passes the inner frames
(`blockBrk`, …), then the label's frame re-enters its loop (`loopBack`) or continues after it
(`blockOk`, …). -/
theorem br_klR {body : Expr} {Fin : Store H × Frame × POut → Prop} {rp₀ : List SeqStep} {ls₀ : List LFrame} :
    ∀ (k : Nat) (rp : List SeqStep) (ls : List LFrame) (L : LFrame) (ws : List Val)
      (s : Store H) (f : Frame) (st' : MState H) (l : List (SCall H)), FramesOk body rp ls →
      k + rp₀.length < ls.length →
      ls[k]? = some L → branchR body rp ls k L ws s f = some st' →
      GoodR body Fin rp₀ ls₀ st' l → KLR body Fin rp₀ ls₀ rp ls (s, f, .flow (.brk k ws)) l
  | _, [], [], _, _, _, _, _, _, _, _, hL, _, _ => by simp at hL
  | _, [], _ :: _, _, _, _, _, _, _, h, _, _, _, _ => by simp [FramesOk] at h
  | _, _ :: _, [], _, _, _, _, _, _, h, _, _, _, _ => by simp [FramesOk] at h
  | k + 1, x :: rp, L₀ :: ls, L, ws, s, f, st', l, hok, hk, hL, hg, hG => by
    obtain ⟨m, a⟩ := x
    obtain ⟨⟨pc, sg, t, c, hpc, hsg, ht, harm, hkind⟩, hok'⟩ := hok
    rw [branchR_succ] at hg
    have hkl := br_klR k rp ls L ws s f st' l hok' (by simp at hk; omega) (by simpa using hL) hg hG
    simpa using KLR.frame hpc hsg ht harm hkind (WrapL.brk (s := s) (f := f) (k := k) (vs := ws)) hkl
  | 0, (m, a) :: rp, L₀ :: ls, L, ws, s, f, st', l, hok, hk, hL, hg, hG => by
    have hlen0 := Proofs.Machine.framesOk_length _ _ hok
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
      obtain ⟨l₁, l₂, r₁, hrun, hkl, rfl⟩ := after_frameR hok' hpc hg hG
      rw [List.reverse_append, List.reverse_reverse] at hrun
      exact .frame hpc hsg ht harm hkind (.ok hloop har rfl hrun) hkl
    · simp only [hloop, ↓reduceIte, Nat.sub_zero, List.length_cons, zero_add, List.drop_one,
        List.tail_cons] at hg
      set R := ws.take np ++ L₀.outer.reverse with hR
      set L' : LFrame := ⟨np, (R.drop np).reverse, true, L₀.tryT, L₀.catches, L₀.bt⟩ with hL'
      have hcarm : seqAt body (rp.reverse ++ [(m, a)]) = some c := by
        rw [Proofs.Machine.seqAt_append]; simp [hpc, hsg, ht, harm]
      have hkind' : StructKind t L'.bt L'.loop L'.tryT L'.catches := by
        simpa [hL', ← hloop] using hkind
      have hokA : FramesOk body (rp.reverse ++ [(m, a)]).reverse (L' :: ls) := by
        simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
          List.singleton_append, List.reverse_reverse, FramesOk]
        exact ⟨⟨pc, sg, t, c, hpc, hsg, ht, harm, hkind'⟩, hok'⟩
      obtain ⟨l₀, l₁, r₀, hrun, hkl0, rfl⟩ :=
        entry_goodR hokA hcarm (by simpa using hg) hG
      rw [restAt_zero, List.reverse_reverse] at hrun
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append, List.reverse_reverse] at hkl0
      obtain ⟨pc', sg', t', c', r₁, l₁₁, l₁₂, hpc', hsg', ht', harm', hw, hrest, rfl⟩ :=
        kl_frame_invR hkl0 (by simp at hk hlen0; omega)
      rw [hpc] at hpc'; cases hpc'
      rw [hsg] at hsg'; cases hsg'
      rw [ht] at ht'; cases ht'
      have hnif := structKind_loop (hloop ▸ hkind)
      have hdr : R.drop np = L'.outer.reverse := by simp [hL']
      have hnat := wrap_sound hkind' harm hnif har hdr hrun hw
      simpa [List.append_assoc] using
        KLR.frame hpc hsg ht harm hkind (.loopBack hloop har hnat) (by simpa using hrest)


/-- **A caught exception**: the frames below `j` let it pass (`tryRethrow`, or the escape rule),
and the `try_table` frame `j` catches it (`tryCatch`): a branch from outside it. -/
theorem kl_catchR {body : Expr} {Fin : Store H × Frame × POut → Prop} {rp₀ : List SeqStep} {ls₀ : List LFrame} {s : Store H} {f : Frame}
    {a : Nat} {us : List Val} {L : LFrame} {l' : LabelIdx} {lg : List (SCall H)} :
    ∀ (j : Nat) (rp : List SeqStep) (ls : List LFrame), FramesOk body rp ls →
      (∀ (k : Nat) (L' : LFrame), k < j → ls[k]? = some L' → L'.tryT = true →
        Catches s f a L'.catches none) →
      ls[j]? = some L → L.tryT = true → Catches s f a L.catches (some (us, l')) →
      KLR body Fin rp₀ ls₀ (rp.drop (j + 1)) (ls.drop (j + 1))
        (s, f, .flow (.brk l'.toNat (us.reverse ++ L.outer.reverse))) lg →
      KLR body Fin rp₀ ls₀ rp ls (s, f, .flow (.throw a)) lg
  | _, [], [], _, _, hL, _, _, _ => by simp at hL
  | _, [], _ :: _, h, _, _, _, _, _ => by simp [FramesOk] at h
  | _, _ :: _, [], h, _, _, _, _, _ => by simp [FramesOk] at h
  | 0, (m, a') :: rp, L₀ :: ls, hok, _, hL, hT, hc, hk => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hL
    subst hL
    obtain ⟨⟨pc, sg, t, c, hpc, hsg, ht, harm, hkind⟩, -⟩ := hok
    simpa using KLR.frame hpc hsg ht harm hkind (.catch_ hT hc) (by simpa using hk)
  | j + 1, (m, a') :: rp, L₀ :: ls, hok, hpass, hL, hT, hc, hk => by
    obtain ⟨⟨pc, sg, t, c, hpc, hsg, ht, harm, hkind⟩, hok'⟩ := hok
    have hkl := kl_catchR j rp ls hok'
      (fun k L' hk' hL' hT' => hpass (k + 1) L' (by omega) (by simpa using hL') hT')
      (by simpa using hL) hT hc (by simpa using hk)
    have hw : WrapL L₀ t (restAt pc (m + 1)) (s, f, .flow (.throw a)) [] (s, f, .flow (.throw a)) := by
      cases htt : L₀.tryT
      · exact .esc trivial (fun h => by rw [htt] at h; cases h)
      · exact .rethrow htt (hpass 0 L₀ (by omega) rfl htt)
    simpa using KLR.frame hpc hsg ht harm hkind hw hkl


/-- **Where an abrupt native outcome staying inside leads**: its frames carry it out to the
result the target stands for. -/
theorem disp_klR {body : Expr} {Fin : Store H × Frame × POut → Prop} {rp₀ : List SeqStep}
    {ls₀ : List LFrame} {b : BlockId} {ls : List LFrame} {r : Store H × Frame × POut}
    {st' : MState H} {l : List (SCall H)} (hok : FramesOk body b.seq.reverse ls)
    (hd : DispS body rp₀.length b ls r st') (hn : ¬ r.2.2.IsNormal)
    (hG : GoodR body Fin rp₀ ls₀ st' l) : KLR body Fin rp₀ ls₀ b.seq.reverse ls r l := by
  have hlen := Proofs.Machine.framesOk_length _ _ hok
  cases hd with
  | next => exact absurd trivial hn
  | br hL hg hk _ =>
    rw [branchN_eq] at hg
    exact br_klR _ _ _ _ _ _ _ _ _ hok hk hL hg hG
  | @catch_ s f a j us L L' l' st' hpass hL hT hc hL' hg hk _ =>
    have hj : j + 1 ≤ b.seq.reverse.length := by
      have := (List.getElem?_eq_some_iff.mp hL).1; omega
    refine kl_catchR j _ _ hok hpass hL hT hc ?_
    rw [branchN_eq, branchR_drop body hj (by simpa using hlen)] at hg
    have hL'' : (ls.drop (j + 1))[l'.toNat]? = some L' := by simpa using hL'
    refine br_klR _ _ _ _ _ _ _ _ _ (Proofs.Machine.framesOk_drop _ _ _ hok)
      (by simp; omega) hL'' ?_ hG
    simpa using hg

/-- **A step staying inside keeps the invariant backwards**: a state stands for what its
successor stands for, with the step's log first. -/
theorem mstep_goodR {body : Expr} {Fin : Store H × Frame × POut → Prop} {rp₀ : List SeqStep}
    {ls₀ : List LFrame} {st st' : MState H} {l l' : List (SCall H)}
    (h : MStepS body rp₀.length st l st') (hok : MInv body st)
    (hlen : rp₀.length ≤ st.lbls.length)
    (hG : GoodR body Fin rp₀ ls₀ st' l') : GoodR body Fin rp₀ ls₀ st (l ++ l') := by
  cases h with
  | @run b sg stk ls s f l r st' hb ht hr hd =>
    by_cases hn : r.2.2.IsNormal
    · cases hd with
      | next hg => exact next_goodR hok hb hr hg hG
      | _ => simp_all [POut.IsNormal, Flow.IsNormal]
    · exact abrupt_goodR hb (.inl rfl) hr hn (disp_klR hok hd hn hG)
  | @abort b sg stk ls s f l r st' hb hr hn hd =>
    have hr' : EvalLXPS s f stk.reverse (liftInstrs (MachineL.codeOf sg)) l r := by
      rw [MachineL.codeOf, MachineLSeq.liftInstrs_append]
      exact (MachineLSeq.append hr _).1 hn
    exact abrupt_goodR hb (.inl rfl) hr' hn (disp_klR hok hd hn hG)
  | @enter b sg stk V V' ls s s₁ f f₁ i a c bt np nr loop tryT cs l st' hb ht harm hkind hr hsel
      har hg _ =>
    have := Proofs.Machine.framesOk_length _ _ (show FramesOk body b.seq.reverse ls from hok)
    exact enter_goodR hok (by simp at hlen this; omega) hb ht harm hkind hr hsel har hg hG

/-- **Runs staying inside keep the invariant backwards.** -/
theorem run_goodR {body : Expr} {Fin : Store H × Frame × POut → Prop} {rp₀ : List SeqStep}
    {ls₀ : List LFrame} {st st' : MState H} {l l' : List (SCall H)}
    (h : MRunS body rp₀.length st l st') (hok : MInv body st)
    (hlen : rp₀.length ≤ st.lbls.length)
    (hG : GoodR body Fin rp₀ ls₀ st' l') : GoodR body Fin rp₀ ls₀ st (l ++ l') := by
  induction h with
  | refl => simpa using hG
  | step hs _ ih =>
    simpa [List.append_assoc] using
      mstep_goodR hs hok hlen (ih (mstep_ok hs.stepL hok) hs.depth hG)

/-! ## Leaving the base -/

theorem KLR.len {body : Expr} {Fin : Store H × Frame × POut → Prop} {rp₀ : List SeqStep}
    {ls₀ : List LFrame} {rp : List SeqStep} {ls : List LFrame} {r : Store H × Frame × POut}
    {l : List (SCall H)} (h : KLR body Fin rp₀ ls₀ rp ls r l) : rp₀.length ≤ rp.length := by
  induction h with
  | base => exact le_rfl
  | frame _ _ _ _ _ _ _ ih => simp; omega

/-- **Where the base's sequence leads**: falling out of it (popping its frame), or a branch to its
own label, to the state `st'`. -/
def ExitB (body : Expr) (rp₀ : List SeqStep) (ls₀ : List LFrame) (st' : MState H)
    (r : Store H × Frame × POut) : Prop :=
  (∃ ws, r.2.2 = .flow (.normal ws) ∧
    gotoN (contRev body rp₀) rp₀.length ls₀ ws.reverse r.1 r.2.1 = some st') ∨
  (∃ ws L, r.2.2 = .flow (.brk 0 ws) ∧ ls₀[0]? = some L ∧
    branchR body rp₀ ls₀ 0 L ws r.1 r.2.1 = some st')

/-- **Falling out of every frame down to the base and out of it**, to a state above the base. -/
theorem cont_leave {body : Expr} {rp₀ : List SeqStep} {ls₀ : List LFrame} {st₀ : MState H} :
    ∀ (rq : List SeqStep) (ls₁ : List LFrame) (W : List Val) (s : Store H) (f : Frame),
      rq.length = ls₁.length → FramesOk body (rq ++ rp₀) (ls₁ ++ ls₀) →
      gotoN (contRev body (rq ++ rp₀)) (rq ++ rp₀).length (ls₁ ++ ls₀) W s f = some st₀ →
      st₀.lbls.length < rp₀.length →
      KLR body (ExitB body rp₀ ls₀ st₀) rp₀ ls₀ (rq ++ rp₀) (ls₁ ++ ls₀)
        (s, f, .flow (.normal W.reverse)) []
  | [], [], W, s, f, _, _, hg, _ => .base (.inl ⟨W.reverse, rfl, by simpa using hg⟩)
  | [], _ :: _, _, _, _, h, _, _, _ => by simp at h
  | _ :: _, [], _, _, _, h, _, _, _ => by simp at h
  | (m, a) :: rq, L :: ls₁, W, s, f, hlen, hok, hg, hd => by
    obtain ⟨⟨pc, sg, t, c, hpc, hsg, ht, harm, hkind⟩, hok'⟩ := hok
    change FramesOk body (rq ++ rp₀) (ls₁ ++ ls₀) at hok'
    change seqAt body (rq ++ rp₀).reverse = some pc at hpc
    have hl' := Proofs.Machine.framesOk_length _ _ hok'
    simp only [List.cons_append, List.length_cons] at hg
    obtain ⟨np, nr, har, hg'⟩ := gotoN_cons (Proofs.Machine.depth_contRev_cons body m a _) hg
    unfold contRev at hg'
    split at hg'
    · rw [show (rq ++ rp₀).length = (⟨(rq ++ rp₀).reverse, m + 1⟩ : BlockId).seq.length by
        simp [Nat.add_comm]]
        at hg'
      have := gotoN_block hg'
      subst this
      simp at hd hl'; omega
    · next hnone =>
      have hend : (segment pc)[m + 1]? = none := by
        rw [lookup_eq, hpc] at hnone
        simpa using hnone
      have hnil : restAt pc (m + 1) = [] := restAt_end hend
      have hkl := cont_leave rq ls₁ _ s f (by simpa using hlen) hok' hg' hd
      have hw : WrapL L t (restAt pc (m + 1)) (s, f, .flow (.normal W.reverse)) []
          (s, f, .flow (.normal (L.outer ++ topVals nr W).reverse)) :=
        wrap_fall har (by rw [hnil]; exact .nil)
      simpa using KLR.frame hpc hsg ht harm hkind hw hkl

/-- **After leaving the frame of `(m, a)` out of the base**: the parent's rest is empty and the
outcome falls out of the base. -/
theorem after_leave {body : Expr} {rp₀ : List SeqStep} {ls₀ : List LFrame} {st₀ : MState H}
    {m a : Nat} {rq : List SeqStep} {ls₁ : List LFrame} {pc : List Instr} {W : List Val}
    {s : Store H} {f : Frame} (hlen : rq.length = ls₁.length)
    (hok : FramesOk body (rq ++ rp₀) (ls₁ ++ ls₀)) (hpc : seqAt body (rq ++ rp₀).reverse = some pc)
    (hg : gotoN (contRev body ((m, a) :: (rq ++ rp₀))) (rq ++ rp₀).length (ls₁ ++ ls₀) W s f =
      some st₀)
    (hd : st₀.lbls.length < rp₀.length) :
    restAt pc (m + 1) = [] ∧
      KLR body (ExitB body rp₀ ls₀ st₀) rp₀ ls₀ (rq ++ rp₀) (ls₁ ++ ls₀)
        (s, f, .flow (.normal W.reverse)) [] := by
  have hl' := Proofs.Machine.framesOk_length _ _ hok
  unfold contRev at hg
  split at hg
  · rw [show (rq ++ rp₀).length = (⟨(rq ++ rp₀).reverse, m + 1⟩ : BlockId).seq.length by
        simp [Nat.add_comm]]
      at hg
    have := gotoN_block hg
    subst this
    simp at hd hl'; omega
  · next hnone =>
    have hend : (segment pc)[m + 1]? = none := by
      rw [lookup_eq, hpc] at hnone
      simpa using hnone
    exact ⟨restAt_end hend, cont_leave rq ls₁ W s f hlen hok hg hd⟩

/-- **A branch leaving the base**: to the base's own label, or to an inner label whose block
falls out of the base. -/
theorem br_leave {body : Expr} {rp₀ : List SeqStep} {ls₀ : List LFrame} {st₀ : MState H} :
    ∀ (k : Nat) (rq : List SeqStep) (ls₁ : List LFrame) (L : LFrame) (ws : List Val)
      (s : Store H) (f : Frame), rq.length = ls₁.length →
      FramesOk body (rq ++ rp₀) (ls₁ ++ ls₀) →
      (∃ c, seqAt body (rq ++ rp₀).reverse = some c ∧ 0 < (segment c).length) →
      k ≤ ls₁.length → (ls₁ ++ ls₀)[k]? = some L →
      branchR body (rq ++ rp₀) (ls₁ ++ ls₀) k L ws s f = some st₀ →
      (k < ls₁.length → st₀.lbls.length < rp₀.length) →
      KLR body (ExitB body rp₀ ls₀ st₀) rp₀ ls₀ (rq ++ rp₀) (ls₁ ++ ls₀)
        (s, f, .flow (.brk k ws)) []
  | 0, [], [], L, ws, s, f, _, _, _, _, hL, hg, _ =>
    .base (.inr ⟨ws, L, rfl, by simpa using hL, by simpa using hg⟩)
  | _ + 1, [], [], _, _, _, _, _, _, _, hk, _, _, _ => by simp at hk
  | _, [], _ :: _, _, _, _, _, h, _, _, _, _, _, _ => by simp at h
  | _, _ :: _, [], _, _, _, _, h, _, _, _, _, _, _ => by simp at h
  | k + 1, x :: rq, L₀ :: ls₁, L, ws, s, f, hlen, hok, _, hk, hL, hg, hd => by
    obtain ⟨m, a⟩ := x
    obtain ⟨⟨pc, sg, t, c, hpc, hsg, ht, harm, hkind⟩, hok'⟩ := hok
    change FramesOk body (rq ++ rp₀) (ls₁ ++ ls₀) at hok'
    change seqAt body (rq ++ rp₀).reverse = some pc at hpc
    simp only [List.cons_append] at hg
    rw [branchR_succ] at hg
    have hkl := br_leave k rq ls₁ L ws s f (by simpa using hlen) hok'
      ⟨pc, hpc, by have := (List.getElem?_eq_some_iff.mp hsg).1; omega⟩
      (by simp at hk; omega) (by simpa using hL) hg (fun h => hd (by simp; omega))
    simpa using KLR.frame hpc hsg ht harm hkind (WrapL.brk (s := s) (f := f) (k := k) (vs := ws))
      hkl
  | 0, (m, a) :: rq, L₀ :: ls₁, L, ws, s, f, hlen, hok, hseq, _, hL, hg, hd => by
    simp only [List.cons_append, List.getElem?_cons_zero, Option.some.injEq] at hL
    subst hL
    have hlev := Proofs.Machine.levelLoop_of_framesOk 0 ((m, a) :: (rq ++ rp₀))
      (L₀ :: (ls₁ ++ ls₀)) (by simpa using hok) rfl
    obtain ⟨⟨pc, sg, t, c, hpc, hsg, ht, harm, hkind⟩, hok'⟩ := hok
    change FramesOk body (rq ++ rp₀) (ls₁ ++ ls₀) at hok'
    change seqAt body (rq ++ rp₀).reverse = some pc at hpc
    have hl' := Proofs.Machine.framesOk_length _ _ hok'
    simp only [List.cons_append] at hg
    simp only [branchR, Option.bind_eq_some_iff] at hg
    obtain ⟨⟨np, nr⟩, har, hg⟩ := hg
    have hd0 : ((m, a) :: (rq ++ rp₀)).drop 0 = (m, a) :: (rq ++ rp₀) := rfl
    rw [Proofs.Machine.labelsRev_getD 0 _ hd0] at hg
    simp only [levelLoop, List.drop_zero] at hlev
    rw [hlev] at hg
    cases hloop : L₀.loop
    · simp only [hloop, Bool.false_eq_true, ↓reduceIte, List.length_cons,
        Nat.add_sub_cancel] at hg
      obtain ⟨hnil, hkl⟩ := after_leave (by simpa using hlen) hok' hpc hg (hd (by simp))
      have hw : WrapL L₀ t (restAt pc (m + 1)) (s, f, .flow (.brk 0 ws)) []
          (s, f, .flow (.normal (L₀.outer ++ (ws.take nr).reverse).reverse)) :=
        .ok hloop har rfl (by rw [hnil]; simpa [List.reverse_append, liftInstrs] using EvalLXPS.nil)
      simpa using KLR.frame hpc hsg ht harm hkind hw hkl
    · simp only [hloop, ↓reduceIte, Nat.sub_zero, List.length_cons, zero_add, List.drop_one,
        List.tail_cons] at hg
      obtain ⟨c₀, hc₀, hne⟩ := hseq
      obtain ⟨sg₀, hsg₀⟩ : ∃ sg₀, (segment c₀)[0]? = some sg₀ :=
        ⟨_, List.getElem?_eq_getElem hne⟩
      have h2 := MachineLDivB.gotoN_entry (H := H) (body := body)
        (p := ((m, a) :: (rq ++ rp₀)).reverse) hc₀ hsg₀
        (⟨np, ((ws.take np ++ L₀.outer.reverse).drop np).reverse, true, L₀.tryT, L₀.catches,
          L₀.bt⟩ :: (ls₁ ++ ls₀)) ((ws.take np ++ L₀.outer.reverse).take np).reverse s f
      simp only [List.reverse_cons, List.length_append, List.length_reverse, List.length_cons,
        List.length_nil, zero_add] at h2 hg
      rw [h2] at hg
      simp only [Option.some.injEq] at hg
      subst hg
      simp at hd hl'; omega

theorem seq_ne_of_framesOk {body : Expr} {m a : Nat} {rp : List SeqStep} {L : LFrame}
    {ls : List LFrame} (h : FramesOk body ((m, a) :: rp) (L :: ls)) :
    ∃ c, seqAt body rp.reverse = some c ∧ 0 < (segment c).length := by
  obtain ⟨⟨pc, sg, t, c, hpc, hsg, -⟩, -⟩ := h
  exact ⟨pc, hpc, by have := (List.getElem?_eq_some_iff.mp hsg).1; omega⟩

/-- **An abrupt dispatch leaving the base** (staying one level above it). -/
theorem abrupt_leave {body : Expr} {rp₀ : List SeqStep} {ls₀ : List LFrame} {rq : List SeqStep}
    {ls₁ : List LFrame} {b : BlockId} {r : Store H × Frame × POut} {st₀ : MState H}
    (hlen : rq.length = ls₁.length) (hseq : b.seq.reverse = rq ++ rp₀)
    (hok : FramesOk body (rq ++ rp₀) (ls₁ ++ ls₀)) (hpos : 0 < rp₀.length)
    (hne : ∃ c, seqAt body b.seq = some c ∧ 0 < (segment c).length)
    (hd : DispS body (rp₀.length - 1) b (ls₁ ++ ls₀) r st₀)
    (hnot : ¬ DispS body rp₀.length b (ls₁ ++ ls₀) r st₀) (hn : ¬ r.2.2.IsNormal) :
    KLR body (ExitB body rp₀ ls₀ st₀) rp₀ ls₀ (rq ++ rp₀) (ls₁ ++ ls₀) r [] := by
  have hl' := Proofs.Machine.framesOk_length _ _ hok
  have hl0 : ls₀.length = rp₀.length := by simp at hl'; omega
  have hne' : ∃ c, seqAt body (rq ++ rp₀).reverse = some c ∧ 0 < (segment c).length := by
    rw [← hseq, List.reverse_reverse]; exact hne
  cases hd with
  | next => exact absurd trivial hn
  | br hL hg hk hδ =>
    rw [branchN_eq, hseq] at hg
    refine br_leave _ rq ls₁ _ _ _ _ hlen hok hne' (by simp at hk; omega) hL hg ?_
    intro hk'
    by_contra hc
    exact hnot (.br hL (by rw [branchN_eq, hseq]; exact hg) (by simp; omega) (by omega))
  | @catch_ s f a j us L L' l' st₀ hpass hL hT hc hL' hg hk hδ =>
    have hJ : j + 1 + l'.toNat ≤ ls₁.length := by simp at hk; omega
    have hj : j + 1 ≤ rq.length := by omega
    have hjr : j + 1 ≤ (rq ++ rp₀).length := by simp; omega
    rw [branchN_eq, hseq, branchR_drop body hjr (by simpa using hl')] at hg
    rw [← hseq]
    refine kl_catchR j _ _ (by rw [hseq]; exact hok) hpass hL hT hc ?_
    rw [hseq, List.drop_append_of_le_length hj, List.drop_append_of_le_length (by omega)]
    rw [List.drop_append_of_le_length hj, List.drop_append_of_le_length (by omega)] at hg
    have hokd := Proofs.Machine.framesOk_drop j _ _ hok
    obtain ⟨x, rest, hx⟩ : ∃ x rest, (rq ++ rp₀).drop j = x :: rest := by
      cases h : (rq ++ rp₀).drop j with
      | nil => simp at h; omega
      | cons x rest => exact ⟨x, rest, rfl⟩
    obtain ⟨Y, rest', hY⟩ : ∃ Y rest', (ls₁ ++ ls₀).drop j = Y :: rest' := by
      cases h : (ls₁ ++ ls₀).drop j with
      | nil => simp at h; omega
      | cons Y rest' => exact ⟨Y, rest', rfl⟩
    rw [hx, hY] at hokd
    obtain ⟨m, a'⟩ := x
    have hne'' := seq_ne_of_framesOk hokd
    have hrest : rest = rq.drop (j + 1) ++ rp₀ := by
      have := congrArg List.tail hx
      simp only [List.tail_cons, List.tail_drop] at this
      rw [← this, List.drop_append_of_le_length hj]
    rw [hrest] at hne''
    refine br_leave _ (rq.drop (j + 1)) (ls₁.drop (j + 1)) L' _ s f (by simp; omega)
      (by
        have := Proofs.Machine.framesOk_drop (j + 1) _ _ hok
        rwa [List.drop_append_of_le_length hj, List.drop_append_of_le_length (by omega)] at this)
      hne'' (by simp; omega)
      (by rw [← List.drop_append_of_le_length (by omega)]; simpa using hL') hg ?_
    intro hk'
    simp only [List.length_drop] at hk'
    by_contra hcon
    refine hnot (.catch_ hpass hL hT hc hL' ?_ (by simp; omega) (by omega))
    rw [branchN_eq, hseq, branchR_drop body hjr (by simpa using hl'),
      List.drop_append_of_le_length hj, List.drop_append_of_le_length (by omega)]
    exact hg

/-- **A step leaving the base, staying one level above it**: the state stands for the base's
outcome leading to the step's target. -/
theorem leave_good {body : Expr} {rp₀ : List SeqStep} {ls₀ : List LFrame} {rq : List SeqStep}
    {ls₁ : List LFrame} {b : BlockId} {stk : List Val} {s : Store H} {f : Frame}
    {l : List (SCall H)} {st₀ : MState H} (hlen : rq.length = ls₁.length)
    (hseq : b.seq.reverse = rq ++ rp₀) (hok : FramesOk body (rq ++ rp₀) (ls₁ ++ ls₀))
    (hpos : 0 < rp₀.length)
    (hD : MStepS body (rp₀.length - 1) ⟨.block b, stk, ls₁ ++ ls₀, s, f⟩ l st₀)
    (hnot : ¬ MStepS body rp₀.length ⟨.block b, stk, ls₁ ++ ls₀, s, f⟩ l st₀) :
    GoodR body (ExitB body rp₀ ls₀ st₀) rp₀ ls₀ ⟨.block b, stk, ls₁ ++ ls₀, s, f⟩ l := by
  have hl' := Proofs.Machine.framesOk_length _ _ hok
  have hbl : b.seq.length = (rq ++ rp₀).length := by rw [← hseq, List.length_reverse]
  cases hD with
  | @run _ sg _ _ _ _ _ r _ hb ht hr hd =>
    obtain ⟨c, hc, hsg⟩ := seg_of_lookup hb
    have hne : ∃ c, seqAt body b.seq = some c ∧ 0 < (segment c).length :=
      ⟨c, hc, by have := (List.getElem?_eq_some_iff.mp hsg).1; omega⟩
    by_cases hn : r.2.2.IsNormal
    · cases hd with
      | @next s₁ f₁ ws _ hg hδ =>
        have hd' : st₀.lbls.length < rp₀.length := by
          by_contra hcon
          exact hnot (.run hb ht hr (.next hg (by omega)))
        unfold entry at hg
        split at hg
        · rw [show b.seq.length = (⟨b.seq, b.idx + 1⟩ : BlockId).seq.length from rfl] at hg
          have := gotoN_block hg
          subst this
          simp at hd' hl'; omega
        · next hnone =>
          have hend : (segment c)[b.idx + 1]? = none := by
            rw [lookup_eq, hc] at hnone
            simpa using hnone
          rw [cont, hseq, hbl] at hg
          have hkl := cont_leave rq ls₁ ws.reverse s₁ f₁ hlen hok hg hd'
          refine ⟨c, l, [], _, hc, ?_, by rw [hseq]; simpa using hkl, by simp⟩
          exact (restAt_run hsg hr).2 _ _ _ rfl [] _ (by rw [restAt_end hend]; exact .nil)
          |> fun h => by simpa using h
      | _ => simp_all [POut.IsNormal, Flow.IsNormal]
    · have hkl := abrupt_leave hlen hseq hok hpos hne hd
        (fun h => hnot (.run hb ht hr h)) hn
      have := abrupt_goodR (Fin := ExitB body rp₀ ls₀ st₀) (stk := stk) (s := s) (f := f) hb
        (.inl rfl) hr hn (by rw [hseq]; exact hkl)
      simpa using this
  | @abort _ sg _ _ _ _ _ r _ hb hr hn hd =>
    obtain ⟨c, hc, hsg⟩ := seg_of_lookup hb
    have hne : ∃ c, seqAt body b.seq = some c ∧ 0 < (segment c).length :=
      ⟨c, hc, by have := (List.getElem?_eq_some_iff.mp hsg).1; omega⟩
    have hkl := abrupt_leave hlen hseq hok hpos hne hd (fun h => hnot (.abort hb hr hn h)) hn
    have hr' : EvalLXPS s f stk.reverse (liftInstrs (MachineL.codeOf sg)) l r := by
      rw [MachineL.codeOf, MachineLSeq.liftInstrs_append]
      exact (MachineLSeq.append hr _).1 hn
    have := abrupt_goodR (Fin := ExitB body rp₀ ls₀ st₀) (stk := stk) (s := s) (f := f) hb
      (.inl rfl) hr' hn (by rw [hseq]; exact hkl)
    simpa using this
  | @enter _ sg _ V V' _ _ s₁ _ f₁ i a c bt np nr loop tryT cs _ _ hb ht harm hkind hr hsel har hg
      hδ =>
    have hd' : st₀.lbls.length < rp₀.length := by
      by_contra hcon
      exact hnot (.enter hb ht harm hkind hr hsel har hg (by omega))
    obtain ⟨pc, hpc, hsg⟩ := seg_of_lookup hb
    have hcarm : seqAt body (b.seq ++ [(b.idx, a)]) = some c := by
      rw [Proofs.Machine.seqAt_append]; simp [hpc, hsg, ht, harm]
    set L : LFrame := ⟨if loop then np else nr, (V'.drop np).reverse, loop, tryT, cs, bt⟩ with hLdef
    have hokA : FramesOk body ((b.idx, a) :: (rq ++ rp₀)) (L :: (ls₁ ++ ls₀)) :=
      ⟨⟨pc, sg, i, c, by rw [← hseq, List.reverse_reverse]; exact hpc, hsg, ht, harm, hkind⟩, hok⟩
    unfold entry at hg
    split at hg
    · rw [show b.seq.length + 1 = (⟨b.seq ++ [(b.idx, a)], 0⟩ : BlockId).seq.length by simp] at hg
      have := gotoN_block hg
      subst this
      simp at hd' hl'; omega
    · next hnone =>
      have hend : (segment c)[0]? = none := by
        rw [lookup_eq, hcarm] at hnone
        simpa using hnone
      have hc0 : c = [] := by rw [← restAt_zero c, restAt_end hend]
      subst hc0
      rw [cont, List.reverse_append, List.reverse_singleton, List.singleton_append, hseq,
        show b.seq.length + 1 = ((b.idx, a) :: (rq ++ rp₀)).length by simp [hbl]] at hg
      have hkl := cont_leave ((b.idx, a) :: rq) (L :: ls₁) (V'.take np).reverse s₁ f₁
        (by simp [hlen]) hokA hg hd'
      rw [List.reverse_reverse] at hkl
      have := enter_core (rp₀ := rp₀) (by rw [hbl]; simp) hb ht harm hkind hr hsel har
        (EvalLXPS.nil (s := s₁) (f := f₁) (stk := V'.take np)) (by rw [hseq]; exact hkl)
      simpa using this

/-! ## Runs inside an arm -/

theorem MStepS.block {body : Expr} {δ : Nat} {st st' : MState H} {l : List (SCall H)}
    (h : MStepS body δ st l st') :
    ∃ b stk ls s f, st = (⟨.block b, stk, ls, s, f⟩ : MState H) := by
  cases h <;> exact ⟨_, _, _, _, _, rfl⟩

theorem run_props {body : Expr} {δ : Nat} {st st' : MState H} {l : List (SCall H)}
    (h : MRunS body δ st l st') (hok : MInv body st) (hd : δ ≤ st.lbls.length) :
    MInv body st' ∧ δ ≤ st'.lbls.length := by
  induction h with
  | refl => exact ⟨hok, hd⟩
  | step hs _ ih => exact ih (mstep_ok hs.stepL hok) hs.depth

/-- **A run inside an arm, until a step leaves the arm one level up**: natively, the arm runs from
its entry with exactly the run's log to an outcome leading, out of its frame, to the step's
target (`ExitB`: falling out of the arm, or a branch to its own label). -/
theorem arm_fwd {body : Expr} {p : List SeqStep} {i a : Nat} {L : LFrame} {ls : List LFrame}
    {W : List Val} {s : Store H} {f : Frame} {c : List Instr}
    (hc : seqAt body (p ++ [(i, a)]) = some c)
    (hok : FramesOk body ((i, a) :: p.reverse) (L :: ls))
    {st_m st₀ : MState H} {l₁ l₂ : List (SCall H)}
    (hrun : MRunS body (p.length + 1) ⟨.block ⟨p ++ [(i, a)], 0⟩, W, L :: ls, s, f⟩ l₁ st_m)
    (hD : MStepS body p.length st_m l₂ st₀) (hnot : ¬ MStepS body (p.length + 1) st_m l₂ st₀) :
    ∃ r₀, EvalLXPS s f W.reverse (liftInstrs c) (l₁ ++ l₂) r₀ ∧
      ExitB body ((i, a) :: p.reverse) (L :: ls) st₀ r₀ := by
  have hl := Proofs.Machine.framesOk_length _ _ hok
  have hok₀ : MInv body (⟨.block ⟨p ++ [(i, a)], 0⟩, W, L :: ls, s, f⟩ : MState H) := by
    show FramesOk body (p ++ [(i, a)]).reverse (L :: ls)
    simpa using hok
  obtain ⟨hokm, hdm⟩ := run_props hrun hok₀ (by simp at hl ⊢; omega)
  obtain ⟨b, stk, lsm, sm, fm, rfl⟩ := hD.block
  have hokm' : FramesOk body b.seq.reverse lsm := hokm
  have hlm := Proofs.Machine.framesOk_length _ _ hokm'
  obtain ⟨rq, R, hseq, hR, hrq⟩ : ∃ rq R, b.seq.reverse = rq ++ R ∧ R.length = p.length + 1 ∧
      rq.length = lsm.length - (p.length + 1) :=
    ⟨b.seq.reverse.take (lsm.length - (p.length + 1)),
      b.seq.reverse.drop (lsm.length - (p.length + 1)), (List.take_append_drop _ _).symm,
      by simp at hlm hdm ⊢; omega, by simp at hlm hdm ⊢; omega⟩
  obtain ⟨ls₁, LS, hls, hLS⟩ : ∃ ls₁ LS, lsm = ls₁ ++ LS ∧ ls₁.length = rq.length :=
    ⟨lsm.take rq.length, lsm.drop rq.length, (List.take_append_drop _ _).symm,
      by simp at hlm hdm ⊢; omega⟩
  subst hls
  rw [hseq] at hokm'
  have hG := leave_good (rp₀ := R) (ls₀ := LS) hLS.symm hseq hokm' (by omega)
    (by rw [hR]; simpa using hD) (by rw [hR]; exact hnot)
  have hG₀ := run_goodR (rp₀ := R) (by rw [hR]; exact hrun) hok₀ (by simp at hl ⊢; omega) hG
  obtain ⟨c', l₀, l₁', r₀, hc', hrun₀, hkl, hlog⟩ := hG₀
  simp only at hc' hrun₀ hkl hlog
  rw [hc] at hc'; cases hc'
  rw [restAt_zero] at hrun₀
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append] at hkl
  cases hkl with
  | base hF => exact ⟨r₀, by simpa [hlog] using hrun₀, hF⟩
  | frame _ _ _ _ _ _ hrest =>
    have := hrest.len
    simp at this; omega

end Silmaril.Wasm.Cfg.Proofs.MachineLRel
