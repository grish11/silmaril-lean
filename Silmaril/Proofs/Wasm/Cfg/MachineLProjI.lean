module

public import Silmaril.Wasm.Cfg.MachineLProj.Defs
public import Silmaril.Wasm.Interp.EHExt.Thms
public import Silmaril.Wasm.Abstract.ExposePTyped.Thms
import Silmaril.Proofs.Wasm.Cfg.MachineLProjC
import Silmaril.Proofs.Wasm.Cfg.MachineLFwd
import Silmaril.Proofs.Wasm.Cfg.MachineLBwd
import Silmaril.Proofs.Wasm.Cfg.MachineLClosed

@[expose] public section

/-!
# The checker invariant of logged machine states (proofs)

`ChkF`, `CInv`: at a block, the rest of its sequence passes the arity check `chkE` at the stack's
height, under the frames' label arities; each frame records its structured instruction, block-type
arities, the check of its arm from its parameters, and the check of the parent's rest after it.
`leave`: a sequence finished at the height its frame expects moves to its continuation with fitting
stacks (`PopFit`) and the invariant.
-/

namespace Silmaril.Wasm.Cfg.Proofs.MachineLProjI

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen Silmaril.Wasm.Interp
open Silmaril.Wasm.Cfg.Proofs.Machine (restAt_cons restAt_end restAt_zero lookup_eq)
open Silmaril.Wasm.Cfg.Proofs.MachineLProjC (topVals_brVals branchN_loop branchN_block gotoN_eq_goto)

variable {H : Type}

theorem arity_eq_blockArity {f : Frame} {mi : ModuleInst} (hf : f.module = mi) (bt : BlockType) :
    Binaryen.arity f bt = blockArity mi bt := by
  subst hf; cases bt <;> rfl

theorem endsAt_some {k n : Nat} (h : endsAt (some (some k)) n = true) : k = n := by
  simpa [endsAt] using h

/-- **Leaving a finished sequence** at the height its frame expects: fitting stacks, and the
invariant at the continuation. -/
theorem leave {ext : ExtArity H} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {body : Expr} {s : Store H} {f : Frame} (hf : f.module = mi) :
    ∀ (rp : List SeqStep) (ls : List LFrame) (W : List Val),
      ChkF ext F mi nl ret body rp ls (some W.length) →
      PopFit f (rp.length - depthT (contRev body rp)) ls W ∧
        CInv ext F mi nl ret body (goto (contRev body rp) rp.length ls W s f)
  | [], [], W, _ => ⟨by simp [contRev, depthT, PopFit], by simp [CInv, goto, contRev]⟩
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim
  | (m, a) :: rp, L :: ls, W, h => by
    obtain ⟨pc, sg, t, c, np, nr, hpc, hsg, ht, harm, hk, har, hLa, -, hend, -, out', hrest, hF⟩ := h
    have hW := endsAt_some hend
    have har' : Binaryen.arity f L.bt = some (np, nr) := by rw [arity_eq_blockArity hf]; exact har
    unfold contRev
    split
    · next hs =>
      refine ⟨?_, ?_⟩
      · simp only [List.length_cons, depthT, List.length_reverse,
          show rp.length + 1 - rp.length = 0 + 1 by omega, PopFit]
        exact ⟨np, nr, har', by omega, trivial⟩
      · simp only [CInv, goto, depthT, List.length_reverse, List.length_cons,
          show rp.length + 1 - rp.length = 0 + 1 by omega, popL]
        refine ⟨hf, pc, out', hpc, ?_, by simpa using hF⟩
        simpa [hW] using hrest
    · next hs =>
      have hnone : (segment pc)[m + 1]? = none := by
        rw [lookup_eq] at hs; simpa [hpc] using hs
      rw [restAt_end hnone] at hrest
      simp only [liftInstrs, chkE, Option.some.injEq] at hrest
      subst hrest
      have hd := Proofs.Machine.depth_contRev body rp
      obtain ⟨h1, h2⟩ := leave hf rp ls (L.outer ++ W) (by simpa [hW] using hF)
      refine ⟨?_, ?_⟩
      · rw [List.length_cons, show rp.length + 1 - depthT (contRev body rp) =
          (rp.length - depthT (contRev body rp)) + 1 by omega]
        exact ⟨np, nr, har', by omega, h1⟩
      · simpa [goto, popL, show rp.length + 1 - depthT (contRev body rp) =
          (rp.length - depthT (contRev body rp)) + 1 by omega] using h2

theorem liftInstrs_append : ∀ (a b : List Instr), liftInstrs (a ++ b) = liftInstrs a ++ liftInstrs b
  | [], _ => rfl
  | _ :: a, b => by simp [liftInstrs, liftInstrs_append a b]

theorem chkE_append {ext : ExtArity H} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {labels : List Nat} :
    ∀ (es₁ es₂ : List BExpr) (h : Nat), chkE ext F mi nl ret labels (some h) (es₁ ++ es₂) =
      (chkE ext F mi nl ret labels (some h) es₁).bind fun o => chkE ext F mi nl ret labels o es₂
  | [], es₂, h => by simp [chkE]
  | e :: es₁, es₂, h => by
    simp only [List.cons_append, chkE]
    cases h1 : chk1E ext F mi nl ret labels h e with
    | none => rfl
    | some o =>
      simp only [Option.bind_some]
      cases o with
      | none => simp
      | some h' => exact chkE_append es₁ es₂ h'

/-- **The invariant at an entry**: reaching position `j` of a checked sequence at the check's
height moves to the block there, or leaves the finished sequence. -/
theorem entry_inv {ext : ExtArity H} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {body : Expr} {s : Store H} {f : Frame} (hf : f.module = mi) {p : List SeqStep}
    {c : List Instr} {j : Nat} {ls : List LFrame} {W : List Val} {out : Option Nat}
    (hc : seqAt body p = some c)
    (hchk : chkE ext F mi nl ret (labs ret ls) (some W.length) (liftInstrs (restAt c j)) =
      some out)
    (hF : ChkF ext F mi nl ret body p.reverse ls out) :
    PopFit f (p.length - depthT (entry body p j)) ls W ∧
      CInv ext F mi nl ret body (goto (entry body p j) p.length ls W s f) := by
  unfold entry
  split
  · refine ⟨by simp [depthT, PopFit], ?_⟩
    simp only [CInv, goto, depthT, Nat.sub_self, popL]
    exact ⟨hf, c, out, hc, hchk, hF⟩
  · next hs =>
    have hnone : (segment c)[j]? = none := by rw [lookup_eq] at hs; simpa [hc] using hs
    rw [restAt_end hnone] at hchk
    simp only [liftInstrs, chkE, Option.some.injEq] at hchk
    subst hchk
    have := leave (s := s) hf p.reverse ls W hF
    simpa [cont] using this

/-- The checked frames below the first `k`. -/
theorem chkF_drop {ext : ExtArity H} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {body : Expr} :
    ∀ (k : Nat) (rp : List SeqStep) (ls : List LFrame) (out : Option Nat), k ≤ ls.length →
      ChkF ext F mi nl ret body rp ls out → ∃ out', ChkF ext F mi nl ret body (rp.drop k) (ls.drop k) out'
  | 0, _, _, out, _, h => ⟨out, by simpa using h⟩
  | _ + 1, _, [], _, hk, _ => by simp at hk
  | _ + 1, [], _ :: _, _, _, h => h.elim
  | k + 1, (m, a) :: rp, L :: ls, out, hk, h => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, out', -, hF⟩ := h
    simpa using chkF_drop k rp ls out' (by simp at hk; omega) hF

/-- A frame's clause depends on the current sequence's end only through `endsAt` at the frame's
result arity. -/
theorem chkF_retarget {ext : ExtArity H} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {body : Expr} {m a : Nat} {rp : List SeqStep} {L : LFrame} {ls : List LFrame}
    {out out' : Option Nat}
    (h : ChkF ext F mi nl ret body ((m, a) :: rp) (L :: ls) out)
    (he : ∀ np nr, blockArity mi L.bt = some (np, nr) → endsAt (some out') nr = true) :
    ChkF ext F mi nl ret body ((m, a) :: rp) (L :: ls) out' := by
  obtain ⟨pc, sg, t, c, np, nr, h1, h2, h3, h4, h5, h6, h7, h8, -, h10⟩ := h
  exact ⟨pc, sg, t, c, np, nr, h1, h2, h3, h4, h5, h6, h7, h8, he _ _ h6, h10⟩

/-- **A branch to label `k`**, the branch site holding the label's arity: the native target is
`MStepC`'s (re-entering a loop's arm, or continuing after the labelled instruction), with the
invariant. -/
theorem branch_inv {ext : ExtArity H} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {body : Expr} {s : Store H} {f : Frame} (hf : f.module = mi) {b : BlockId}
    {ls : List LFrame} {out : Option Nat} {k : Nat} {L : LFrame} {N : List Val}
    (hok : FramesOk body b.seq.reverse ls) (hF : ChkF ext F mi nl ret body b.seq.reverse ls out)
    (hL : ls[k]? = some L) (hN : L.arity ≤ N.length) :
    let tgt := (labels body b.seq).getD k .invalid
    let st' := if L.loop then
        goto tgt (b.seq.length - k) (L :: ls.drop (k + 1)) (topVals L.arity (brVals k ls N.reverse)) s f
      else
        goto tgt (b.seq.length - (k + 1)) (ls.drop (k + 1))
          (L.outer ++ topVals L.arity (brVals k ls N.reverse)) s f
    branchN body b ls k L N s f = some st' ∧ CInv ext F mi nl ret body st' := by
  intro tgt st'
  have hlen : ls.length = b.seq.length := by
    simpa using Proofs.Machine.framesOk_length _ _ hok
  have hk : k < ls.length := (List.getElem?_eq_some_iff.mp hL).1
  have hdl : ls.drop k = L :: ls.drop (k + 1) := by
    rw [List.drop_eq_getElem_cons hk]; congr 1; exact (List.getElem?_eq_some_iff.mp hL).2
  obtain ⟨⟨m, a⟩, rp', hdr⟩ : ∃ x rp', b.seq.reverse.drop k = x :: rp' := by
    cases h : b.seq.reverse.drop k with
    | nil => simp [List.drop_eq_nil_iff] at h; omega
    | cons x rp' => exact ⟨x, rp', rfl⟩
  have hrp' : rp'.length + k + 1 = b.seq.length := by
    have := congrArg List.length hdr; simp at this; omega
  obtain ⟨outk, hFk⟩ := chkF_drop k _ _ out (by omega) hF
  rw [hdr, hdl] at hFk
  have hFk' := hFk
  obtain ⟨pc, sg, t, c, np, nr, hpc, hsg, ht, harm, hkind, har, hLa, -, -, ⟨oa, hoa, hoaE⟩, out', hrest,
    hFr⟩ := hFk'
  have har' : Binaryen.arity f L.bt = some (np, nr) := by rw [arity_eq_blockArity hf]; exact har
  have hlev := Proofs.Machine.levelLoop_of_framesOk k _ _ hok hL
  simp only [levelLoop, hdr] at hlev
  have htgt : (labels body b.seq).getD k .invalid = if L.loop then
      entry body (rp'.reverse ++ [(m, a)]) 0 else contRev body ((m, a) :: rp') := by
    show (labelsRev body b.seq.reverse).getD k .invalid = _
    rw [Proofs.Machine.labelsRev_getD k _ hdr, hlev]
  cases hloop : L.loop with
  | true =>
    simp only [hloop, ↓reduceIte] at hLa htgt
    have hW : (topVals L.arity (brVals k ls N.reverse)).length = np := by
      rw [topVals_brVals (by omega)]; simp; omega
    have hcA : seqAt body (rp'.reverse ++ [(m, a)]) = some c := by
      rw [Proofs.Machine.seqAt_append]; simp [hpc, hsg, ht, harm]
    have hFa : ChkF ext F mi nl ret body (rp'.reverse ++ [(m, a)]).reverse
        (L :: ls.drop (k + 1)) oa := by
      simpa using chkF_retarget hFk (fun np' nr' h => by
        rw [har] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h; exact hoaE)
    obtain ⟨hfit, hinv⟩ := entry_inv (s := s) hf (j := 0) hcA (by rw [restAt_zero, hW]; exact hoa) hFa
    have hd : (rp'.reverse ++ [(m, a)]).length = b.seq.length - k := by simp; omega
    rw [hd] at hfit hinv
    refine ⟨?_, ?_⟩
    · rw [branchN_loop hloop har' hLa (by omega), htgt]
      simp only [st', tgt, hloop, ↓reduceIte, htgt]
      exact gotoN_eq_goto hfit
    · simp only [st', tgt, hloop, ↓reduceIte]
      rw [htgt]; exact hinv
  | false =>
    simp only [hloop, Bool.false_eq_true, ↓reduceIte] at hLa htgt
    set W := topVals L.arity (brVals k ls N.reverse) with hWdef
    have hW : W.length = nr := by rw [hWdef, topVals_brVals (by omega)]; simp; omega
    have hFl : ChkF ext F mi nl ret body ((m, a) :: rp') (L :: ls.drop (k + 1)) (some W.length) :=
      chkF_retarget hFk (fun np' nr' h => by
        rw [har] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h; simp [endsAt, hW])
    obtain ⟨hfit, hinv⟩ := leave (s := s) hf ((m, a) :: rp') (L :: ls.drop (k + 1)) W hFl
    have hdc := Proofs.Machine.depth_contRev_cons body m a rp'
    have hg : goto (contRev body ((m, a) :: rp')) (rp'.length + 1) (L :: ls.drop (k + 1)) W s f =
        goto (contRev body ((m, a) :: rp')) rp'.length (ls.drop (k + 1)) (L.outer ++ W) s f := by
      simp only [goto]
      rw [show rp'.length + 1 - depthT (contRev body ((m, a) :: rp')) =
        (rp'.length - depthT (contRev body ((m, a) :: rp'))) + 1 by omega]
      rfl
    rw [List.length_cons] at hfit hinv
    rw [hg] at hinv
    rw [show rp'.length + 1 - depthT (contRev body ((m, a) :: rp')) =
      (rp'.length - depthT (contRev body ((m, a) :: rp'))) + 1 by omega] at hfit
    obtain ⟨np', nr', har'', -, hfit'⟩ := hfit
    have hd : b.seq.length - (k + 1) = rp'.length := by omega
    refine ⟨?_, ?_⟩
    · rw [branchN_block hloop har' hLa (by omega)]
      simp only [st', tgt, hloop, Bool.false_eq_true, ↓reduceIte, htgt, hd]
      exact gotoN_eq_goto hfit'
    · simp only [st', tgt, hloop, Bool.false_eq_true, ↓reduceIte, hd]
      rw [htgt]; exact hinv

open Silmaril.Wasm.Abstract.ExposePTyped (GoodO) in
/-- **Dispatching a checked outcome**: the straight-line code at block `b` ended as its check says
(`GoodO`); a fallthrough continues with the checked rest. Every `DispL` target satisfies the
invariant, when no frame is a `try_table` (catching is the exception bridge's). -/
theorem disp_inv {ext : ExtArity H} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {body : Expr} {b : BlockId} {ls : List LFrame} {r : Store H × Frame × Abstract.CallXP.POut}
    {st' : MState H} {c : List Instr} {out oc : Option Nat}
    (hd : DispL body b ls r st') (hf : r.2.1.module = mi) (hok : FramesOk body b.seq.reverse ls)
    (hc : seqAt body b.seq = some c) (hF : ChkF ext F mi nl ret body b.seq.reverse ls out)
    (hgo : GoodO (labs ret ls) ret oc r.2.2)
    (hnext : ∀ ws, r.2.2 = .flow (.normal ws) → oc = some ws.length →
      chkE ext F mi nl ret (labs ret ls) (some ws.length) (liftInstrs (restAt c (b.idx + 1))) =
        some out)
    (hnt : ∀ L ∈ ls, L.tryT = false) :
    CInv ext F mi nl ret body st' := by
  cases hd with
  | @next s f ws st' hg =>
    simp only [GoodO] at hgo
    have hchk := hnext ws rfl hgo
    obtain ⟨hfit, hinv⟩ := entry_inv (s := s) (W := ws.reverse) hf hc (by simpa using hchk) hF
    rw [gotoN_eq_goto hfit] at hg
    cases hg; exact hinv
  | @br s f ws k L st' hL hg =>
    simp only [GoodO] at hgo
    obtain ⟨n, hn, hle⟩ := hgo
    have hk : k < ls.length := (List.getElem?_eq_some_iff.mp hL).1
    have hlk : (labs ret ls)[k]? = some L.arity := by
      rw [labs, List.getElem?_append_left (by simpa using hk), List.getElem?_map, hL]; rfl
    have hn' : n = L.arity := by
      rw [hlk] at hn; exact (Option.some.inj hn).symm
    subst hn'
    obtain ⟨hg', hinv⟩ := branch_inv (s := s) hf hok hF hL hle
    rw [hg'] at hg; cases hg; exact hinv
  | brOut => simp [CInv]
  | ret => simp [CInv]
  | trap => simp [CInv]
  | raise => simp [CInv]
  | catch_ _ hL hT =>
    exact absurd hT (by rw [hnt _ (List.mem_of_getElem? hL)]; simp)
  | catchOut _ hL hT =>
    exact absurd hT (by rw [hnt _ (List.mem_of_getElem? hL)]; simp)

theorem endsAt_some_iff {o : Option (Option Nat)} {n : Nat} (h : endsAt o n = true) :
    ∃ oa, o = some oa ∧ endsAt (some oa) n = true := by
  cases o with
  | none => simp [endsAt] at h
  | some oa => exact ⟨oa, rfl, h⟩

/-- **The check of a structured terminator** (not a `try_table`) at the height of the stack `V`
left by its segment: its block type has arities, the arm's parameters are on the stack, the arm
passes the check under the pushed label, and the parent continues at the height the frame's outer
values and results make. -/
theorem chk_struct {ext : ExtArity H} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {labels : List Nat} {t : Instr} {bt : BlockType} {loop tryT : Bool} {cs : List Catch}
    {V V' : List Val} {a : Nat} {c' : List Instr} {o : Option Nat}
    (hk : StructKind t bt loop tryT cs) (hnt : tryT = false) (hsel : ArmSel t V a V')
    (harm : armOf t a = some c')
    (h : chk1E ext F mi nl ret labels V.length (liftInstr t) = some o) :
    ∃ np nr, blockArity mi bt = some (np, nr) ∧ np ≤ V'.length ∧
      o = some (V'.length - np + nr) ∧ ∃ oa,
        chkE ext F mi nl ret ((if loop then np else nr) :: labels) (some np) (liftInstrs c') =
          some oa ∧ endsAt (some oa) nr = true := by
  cases hk with
  | block =>
    cases hsel
    simp only [armOf, Option.some.injEq] at harm; subst harm
    simp only [liftInstr, chk1E] at h
    split at h
    · next np nr hba =>
      split at h
      · next hc =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨oa, hoa, hoaE⟩ := endsAt_some_iff hc.2
        exact ⟨np, nr, hba, hc.1, (Option.some.inj h).symm, oa, by simpa using hoa, hoaE⟩
      · simp at h
    · simp at h
  | loop =>
    cases hsel
    simp only [armOf, Option.some.injEq] at harm; subst harm
    simp only [liftInstr, chk1E] at h
    split at h
    · next np nr hba =>
      split at h
      · next hc =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨oa, hoa, hoaE⟩ := endsAt_some_iff hc.2
        exact ⟨np, nr, hba, hc.1, (Option.some.inj h).symm, oa, by simpa using hoa, hoaE⟩
      · simp at h
    · simp at h
  | if_ =>
    cases hsel with
    | plain hi => exact absurd rfl (hi _ _ _)
    | @cond _ tt ee cv V₀ bv hb =>
    simp only [liftInstr, chk1E, chkE, Option.bind_some] at h
    split at h
    · next np nr hba =>
      split at h
      · next hc =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨⟨hle, h1⟩, h2⟩ := hc
        refine ⟨np, nr, hba, by simp at hle; omega, ?_, ?_⟩
        · rw [← Option.some.inj h]; simp
        · have hc' := MachineLBwd.armOf_if harm
          subst hc'
          cases bv
          · obtain ⟨oa, hoa, hoaE⟩ := endsAt_some_iff h2
            exact ⟨oa, by simpa using hoa, hoaE⟩
          · obtain ⟨oa, hoa, hoaE⟩ := endsAt_some_iff h1
            exact ⟨oa, by simpa using hoa, hoaE⟩
      · simp at h
    · simp at h
  | tryTable => exact absurd hnt (by simp)

theorem chk_structE {ext : ExtArity H} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {labels : List Nat} {t : Instr} {bt : BlockType} {loop tryT : Bool} {cs : List Catch}
    {V V' : List Val} {a : Nat} {c' : List Instr} {o : Option Nat}
    (hk : StructKind t bt loop tryT cs) (hsel : ArmSel t V a V')
    (harm : armOf t a = some c')
    (h : chk1E ext F mi nl ret labels V.length (liftInstr t) = some o) :
    ∃ np nr, blockArity mi bt = some (np, nr) ∧ np ≤ V'.length ∧
      o = some (V'.length - np + nr) ∧ (∃ oa,
        chkE ext F mi nl ret ((if loop then np else nr) :: labels) (some np) (liftInstrs c') =
          some oa ∧ endsAt (some oa) nr = true) ∧
      (tryT = true → ∃ ns, ext F mi (.tryTable bt cs []) = some (.catches ns) ∧
        catchOk labels cs ns = true) := by
  cases hk with
  | block =>
    cases hsel
    simp only [armOf, Option.some.injEq] at harm; subst harm
    simp only [liftInstr, chk1E] at h
    split at h
    · next np nr hba =>
      split at h
      · next hc =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨oa, hoa, hoaE⟩ := endsAt_some_iff hc.2
        exact ⟨np, nr, hba, hc.1, (Option.some.inj h).symm, ⟨oa, by simpa using hoa, hoaE⟩, nofun⟩
      · simp at h
    · simp at h
  | loop =>
    cases hsel
    simp only [armOf, Option.some.injEq] at harm; subst harm
    simp only [liftInstr, chk1E] at h
    split at h
    · next np nr hba =>
      split at h
      · next hc =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨oa, hoa, hoaE⟩ := endsAt_some_iff hc.2
        exact ⟨np, nr, hba, hc.1, (Option.some.inj h).symm, ⟨oa, by simpa using hoa, hoaE⟩, nofun⟩
      · simp at h
    · simp at h
  | if_ =>
    cases hsel with
    | plain hi => exact absurd rfl (hi _ _ _)
    | @cond _ tt ee cv V₀ bv hb =>
    simp only [liftInstr, chk1E, chkE, Option.bind_some] at h
    split at h
    · next np nr hba =>
      split at h
      · next hc =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨⟨hle, h1⟩, h2⟩ := hc
        refine ⟨np, nr, hba, by simp at hle; omega, ?_, ?_, nofun⟩
        · rw [← Option.some.inj h]; simp
        · have hc' := MachineLBwd.armOf_if harm
          subst hc'
          cases bv
          · obtain ⟨oa, hoa, hoaE⟩ := endsAt_some_iff h2
            exact ⟨oa, by simpa using hoa, hoaE⟩
          · obtain ⟨oa, hoa, hoaE⟩ := endsAt_some_iff h1
            exact ⟨oa, by simpa using hoa, hoaE⟩
      · simp at h
    · simp at h
  | tryTable =>
    cases hsel
    simp only [armOf, Option.some.injEq] at harm; subst harm
    simp only [liftInstr, chk1E] at h
    split at h
    · next ns np nr hext hba =>
      split at h
      · next hc =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨⟨hle, hcok⟩, hend⟩ := hc
        obtain ⟨oa, hoa, hoaE⟩ := endsAt_some_iff hend
        exact ⟨np, nr, hba, hle, (Option.some.inj h).symm, ⟨oa, by simpa using hoa, hoaE⟩,
          fun _ => ⟨ns, hext, hcok⟩⟩
      · simp at h
    · simp at h

theorem gotoN_sf {t : Target} {d : Nat} {ls : List LFrame} {W : List Val} {s : Store H}
    {f : Frame} {st' : MState H} (h : gotoN t d ls W s f = some st') :
    st'.store = s ∧ st'.frame = f := by
  simp only [gotoN, Option.map_eq_some_iff] at h
  obtain ⟨_, -, rfl⟩ := h; exact ⟨rfl, rfl⟩

theorem branchN_sf {body : Expr} {b : BlockId} {ls : List LFrame} {k : Nat} {L : LFrame}
    {N : List Val} {s : Store H} {f : Frame} {st' : MState H}
    (h : branchN body b ls k L N s f = some st') : st'.store = s ∧ st'.frame = f := by
  simp only [branchN, Option.bind_eq_some_iff] at h
  obtain ⟨_, -, h⟩ := h
  split at h <;> exact gotoN_sf h

/-- A dispatch keeps the outcome's store and frame. -/
theorem disp_sf {body : Expr} {b : BlockId} {ls : List LFrame}
    {r : Store H × Frame × Abstract.CallXP.POut} {st' : MState H} (hd : DispL body b ls r st') :
    st'.store = r.1 ∧ st'.frame = r.2.1 := by
  cases hd with
  | next hg => exact gotoN_sf hg
  | br _ hg => exact branchN_sf hg
  | catch_ _ _ _ _ _ hg => exact branchN_sf hg
  | _ => exact ⟨rfl, rfl⟩

theorem tryT_of_noTry {body : Expr} (hNT : NoTry body) {p : List SeqStep} {c : List Instr}
    {i : Nat} {sg : Segment} {t : Instr} {bt : BlockType} {loop tryT : Bool} {cs : List Catch}
    (hc : seqAt body p = some c) (hsg : (segment c)[i]? = some sg) (ht : sg.term = some t)
    (hk : StructKind t bt loop tryT cs) : tryT = false := by
  cases hk with
  | tryTable => exact absurd ht (hNT _ _ _ _ _ _ _ hc hsg)
  | _ => rfl

theorem chkF_noTry {ext : ExtArity H} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {body : Expr} (hNT : NoTry body) :
    ∀ (rp : List SeqStep) (ls : List LFrame) (out : Option Nat),
      ChkF ext F mi nl ret body rp ls out → ∀ L ∈ ls, L.tryT = false
  | _, [], _, _ => by simp
  | [], _ :: _, _, h => h.elim
  | (m, a) :: rp, L :: ls, out, h => by
    obtain ⟨pc, sg, t, c, np, nr, hpc, hsg, ht, -, hk, -, -, -, -, -, out', -, hF⟩ := h
    intro L' hL'
    rcases List.mem_cons.mp hL' with rfl | hL'
    · exact tryT_of_noTry hNT hpc hsg ht hk
    · exact chkF_noTry hNT rp ls out' hF L' hL'

open Silmaril.Wasm.Abstract.ExposePTyped (GoodO ArityResp evalOXP_goodO) in
open Silmaril.Wasm.Abstract.ExposePStruct (Ctx) in
/-- **The checker invariant is preserved by logged steps** whose calls are answers of an
arity-respecting oracle `C`, on bodies without `try_table`. -/
theorem cinv_step {Γ : Ctx H} {C : Abstract.CallRel H} (hC : ArityResp Γ C) {mi : ModuleInst}
    {nl ret : Nat} {body : Expr} (hNT : NoTry body) {st st' : MState H}
    {l : List (Abstract.SCall H)} (hs : MStepL body st l st') (hl : ∀ e ∈ l, CloseOk C e)
    (hok : MInv body st) (hg : Γ.Good st.store) (hn : st.frame.locals.length = nl)
    (hI : CInv (ehExt Γ.tags) Γ.funcs mi nl ret body st) :
    Γ.Good st'.store ∧ st'.frame.locals.length = nl ∧
      CInv (ehExt Γ.tags) Γ.funcs mi nl ret body st' := by
  cases hs with
  | @run b sg stk ls s f l r st' hb ht hr hd =>
    obtain ⟨hf, c, out, hc, hchk, hF⟩ := hI
    obtain ⟨c', hc', hsg⟩ := Proofs.Machine.seg_of_lookup hb
    rw [hc] at hc'; cases hc'
    simp only at hchk
    rw [restAt_cons hsg, liftInstrs_append, chkE_append] at hchk
    obtain ⟨oc, hoc, hrest⟩ := Option.bind_eq_some_iff.mp hchk
    have d := Proofs.MachineLClosed.logged_closed hr hl
    obtain ⟨s', f', o⟩ := r
    simp only at hg hn hf
    have hoc' : chkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret (labs ret ls)
        (some stk.reverse.length) (liftInstrs (codeOf sg)) = some oc := by
      rw [hg.1, hf, hn, List.length_reverse]; exact hoc
    obtain ⟨hg', hf', hn', hgo⟩ := evalOXP_goodO hC d hg hoc'
    obtain ⟨hs1, hs2⟩ := disp_sf hd
    simp only at hs1 hs2
    refine ⟨by rw [hs1]; exact hg', by rw [hs2, hn', hn], ?_⟩
    exact disp_inv hd (by simp only; rw [hf', hf]) (by simpa [MInv] using hok) hc hF hgo
      (fun ws hw hoc2 => by simp only at hw; subst hw; subst hoc2; exact hrest)
      (chkF_noTry hNT _ _ _ hF)
  | @abort b sg stk ls s f l r st' hb hr hnn hd =>
    obtain ⟨hf, c, out, hc, hchk, hF⟩ := hI
    obtain ⟨c', hc', hsg⟩ := Proofs.Machine.seg_of_lookup hb
    rw [hc] at hc'; cases hc'
    simp only at hchk
    rw [restAt_cons hsg, Segment.instrs, List.append_assoc, liftInstrs_append, chkE_append]
      at hchk
    obtain ⟨oc, hoc, -⟩ := Option.bind_eq_some_iff.mp hchk
    have d := Proofs.MachineLClosed.logged_closed hr hl
    obtain ⟨s', f', o⟩ := r
    simp only at hg hn hf
    have hoc' : chkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret (labs ret ls)
        (some stk.reverse.length) (liftInstrs sg.body) = some oc := by
      rw [hg.1, hf, hn, List.length_reverse]; exact hoc
    obtain ⟨hg', hf', hn', hgo⟩ := evalOXP_goodO hC d hg hoc'
    obtain ⟨hs1, hs2⟩ := disp_sf hd
    simp only at hs1 hs2
    refine ⟨by rw [hs1]; exact hg', by rw [hs2, hn', hn], ?_⟩
    exact disp_inv hd (by simp only; rw [hf', hf]) (by simpa [MInv] using hok) hc hF hgo
      (fun ws hw _ => by simp only at hw; subst hw; exact absurd trivial hnn)
      (chkF_noTry hNT _ _ _ hF)
  | @enter b sg stk V V' ls s s₁ f f₁ i a c' bt np nr loop tryT cs l st' hb ht harm hkind hr hsel
      har hg' =>
    obtain ⟨hf, c, out, hc, hchk, hF⟩ := hI
    obtain ⟨c₀, hc₀, hsg⟩ := Proofs.Machine.seg_of_lookup hb
    rw [hc] at hc₀; cases hc₀
    simp only at hchk
    rw [restAt_cons hsg, Segment.instrs, ht, Option.toList_some, List.append_assoc,
      liftInstrs_append, chkE_append] at hchk
    obtain ⟨oc, hoc, hrest⟩ := Option.bind_eq_some_iff.mp hchk
    have d := Proofs.MachineLClosed.logged_closed hr hl
    simp only at hg hn hf
    have hoc' : chkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret (labs ret ls)
        (some stk.reverse.length) (liftInstrs sg.body) = some oc := by
      rw [hg.1, hf, hn, List.length_reverse]; exact hoc
    obtain ⟨hg', hf', hn', hgo⟩ := evalOXP_goodO hC d hg hoc'
    simp only [GoodO] at hgo
    subst hgo
    have hf₁ : f₁.module = mi := by rw [hf', hf]
    have hnt : tryT = false := tryT_of_noTry hNT hc hsg ht hkind
    simp only [liftInstrs, List.singleton_append, chkE, Option.bind_eq_some_iff] at hrest
    obtain ⟨o₂, h₂, hrest⟩ := hrest
    obtain ⟨np', nr', hba, hle, ho₂, oa, hoa, hoaE⟩ := chk_struct hkind hnt hsel harm h₂
    rw [arity_eq_blockArity hf₁, hba] at har
    simp only [Option.some.injEq, Prod.mk.injEq] at har
    obtain ⟨rfl, rfl⟩ := har
    subst ho₂
    set L : LFrame := ⟨if loop then np' else nr', (V'.drop np').reverse, loop, tryT, cs, bt⟩
      with hLdef
    have hcA : seqAt body (b.seq ++ [(b.idx, a)]) = some c' := by
      rw [Proofs.Machine.seqAt_append]; simp [hc, hsg, ht, harm]
    have hFa : ChkF (ehExt Γ.tags) Γ.funcs mi nl ret body (b.seq ++ [(b.idx, a)]).reverse
        (L :: ls) oa := by
      simp only [List.reverse_append, List.reverse_singleton, List.singleton_append]
      refine ⟨c, sg, i, c', np', nr', by simpa using hc, hsg, ht, harm, hkind, hba, rfl,
      fun h => absurd h (by simp [hLdef, hnt]), hoaE,
        ⟨oa, hoa, hoaE⟩, out, ?_, hF⟩
      have : (L.outer.length + nr') = V'.length - np' + nr' := by simp [hLdef]
      rw [this]; exact hrest
    have hW : ((V'.take np').reverse).length = np' := by simp; omega
    obtain ⟨hfit, hinv⟩ := entry_inv (s := s₁) (W := (V'.take np').reverse) hf₁ (j := 0) hcA
      (by rw [restAt_zero, hW]; exact hoa) hFa
    have hlen : (b.seq ++ [(b.idx, a)]).length = b.seq.length + 1 := by simp
    rw [hlen] at hfit hinv
    rw [gotoN_eq_goto hfit] at hg'
    cases hg'
    exact ⟨hg', by simp [goto]; rw [hn', hn], hinv⟩

/-- **The checker invariant at the CFG entry**, from the function's own check (as `StoreChkE`
checks a body: the function label of arity `ret`, from the empty stack, ending at `ret`). -/
theorem cinv_initial {ext : ExtArity H} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {body : Expr} {s : Store H} {f : Frame} (hf : f.module = mi)
    (hchk : endsAt (chkE ext F mi nl ret [ret] (some 0) (liftInstrs body)) ret = true) :
    CInv ext F mi nl ret body (initial body s f) := by
  obtain ⟨out, hout, hend⟩ := endsAt_some_iff hchk
  have := (entry_inv (s := s) (W := []) (ls := []) hf (p := []) (c := body) (j := 0) rfl
    (by rw [restAt_zero]; simpa [labs] using hout) hend).2
  simpa [goto, popL, initial, cfgEntry] using this

open Silmaril.Wasm.Abstract.ExposePTyped (ArityResp) in
open Silmaril.Wasm.Abstract.ExposePStruct (Ctx) in
/-- **The checker invariant along logged runs** whose calls are answers of an arity-respecting
oracle, on bodies without `try_table`. -/
theorem cinv_run {Γ : Ctx H} {C : Abstract.CallRel H} (hC : ArityResp Γ C) {mi : ModuleInst}
    {nl ret : Nat} {body : Expr} (hNT : NoTry body) {st st' : MState H}
    {l : List (Abstract.SCall H)} (h : MRunL body st l st') (hl : ∀ e ∈ l, CloseOk C e)
    (hok : MInv body st) (hg : Γ.Good st.store) (hn : st.frame.locals.length = nl)
    (hI : CInv (ehExt Γ.tags) Γ.funcs mi nl ret body st) :
    Γ.Good st'.store ∧ st'.frame.locals.length = nl ∧
      CInv (ehExt Γ.tags) Γ.funcs mi nl ret body st' := by
  induction h with
  | refl => exact ⟨hg, hn, hI⟩
  | step hs _ ih =>
    obtain ⟨hg₁, hn₁, hI₁⟩ := cinv_step hC hNT hs (fun e he => hl e (List.mem_append_left _ he))
      hok hg hn hI
    exact ih (fun e he => hl e (List.mem_append_right _ he)) (MachineLFwd.mstep_ok hs hok) hg₁
      hn₁ hI₁

end Silmaril.Wasm.Cfg.Proofs.MachineLProjI
