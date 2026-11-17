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

end Silmaril.Wasm.Cfg.Proofs.MachineLFwd
