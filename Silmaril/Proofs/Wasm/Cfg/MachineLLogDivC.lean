module

public import Silmaril.Proofs.Wasm.Cfg.MachineLLogDivP

@[expose] public section

/-!
# Machine divergence after a log, natively (H2, proofs)

`machine_logDiv`: the machine's divergence after a log `l` (`MLogDivL`) is native divergence after a
log (`LogDivXP`) whose session reading is `l` followed by oracle-answered calls only.

* A diverging callee reached after the boundary: the run to it is a native pending call
  (`MachineLPend.pending_iff`), hence `LogDivXP` with the log up to the call
  (`MachineLLogDivB.reach_logDiv`).
* Infinite local steps after the boundary: the run eventually never leaves a sequence
  (`MachineLLogDivB.stays_point`); that point diverges natively (`MachineLDivI.qx_div`), and the
  logged run from the CFG entry to it is divergence after its log
  (`MachineLLogDivP.prefix_logDiv`). The calls between the boundary and the point are
  oracle-answered.
-/

namespace Silmaril.Wasm.Cfg.Proofs.MachineLLogDivC

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Abstract (EvalLXPS SCall OCall LogDivXP)
open Silmaril.Wasm.Abstract.XRecursionP (closedCallXP)
open Silmaril.Wasm.Abstract.XDivergeP (EvalDivXP FunDivXP)
open Silmaril.Wasm.Cfg.Proofs.MachineLClosed (AllOk allOk_append allOk_nil)
open Silmaril.Wasm.Cfg.Proofs.MachineLLogDivP (segLog segLog_add segLog_one PointT prefix_logDiv)

variable {H : Type}

theorem segLog_congr {lg lg' : ℕ → List (SCall H)} :
    ∀ (n a a' : ℕ), (∀ m, m < n → lg (a + m) = lg' (a' + m)) → segLog lg a n = segLog lg' a' n
  | 0, _, _, _ => rfl
  | n + 1, a, a', h => by
    simp only [segLog]
    rw [show lg a = lg' a' by simpa using h 0 (by omega),
      segLog_congr n (a + 1) (a' + 1) (fun m hm => by
        simpa [Nat.add_assoc, Nat.add_comm 1 m] using h (m + 1) (by omega))]

theorem segLog_allOk {lg : ℕ → List (SCall H)} (h : ∀ m, AllOk closedCallXP (lg m)) :
    ∀ (n a : ℕ), AllOk closedCallXP (segLog lg a n)
  | 0, _ => allOk_nil _
  | n + 1, a => allOk_append.2 ⟨h a, segLog_allOk h n (a + 1)⟩

/-- **A logged run as an indexed run.** -/
theorem mrun_index {body : Expr} {st st' : MState H} {l : List (SCall H)}
    (h : MRunL body st l st') :
    ∃ (K : ℕ) (G : ℕ → MState H) (lg : ℕ → List (SCall H)), G 0 = st ∧ G K = st' ∧
      (∀ k, k < K → MStepL body (G k) (lg k) (G (k + 1))) ∧ segLog lg 0 K = l := by
  induction h with
  | refl st => exact ⟨0, fun _ => st, fun _ => [], rfl, rfl, fun k hk => absurd hk (by omega), rfl⟩
  | @step st st₁ st₂ l₁ l₂ hs _ ih =>
    obtain ⟨K, G, lg, h0, hK, hG, hl⟩ := ih
    refine ⟨K + 1, fun k => if k = 0 then st else G (k - 1),
      fun k => if k = 0 then l₁ else lg (k - 1), by simp, by simp [hK], fun k hk => ?_, ?_⟩
    · rcases k with _ | k
      · simpa [h0] using hs
      · simpa using hG k (by omega)
    · have hc : segLog (fun k => if k = 0 then l₁ else lg (k - 1)) 1 K = segLog lg 0 K :=
        segLog_congr K 1 0 (fun m _ => by simp [Nat.add_comm 1 m])
      simp only [segLog, ↓reduceIte, zero_add, hc, hl]

open Silmaril.Wasm.Cfg.Proofs.Machine (lookup_eq)
open Silmaril.Wasm.Cfg.Proofs.MachineLFwd (mstep_ok run_ok initial_ok)
open Silmaril.Wasm.Cfg.Proofs.MachineLBwd (pos_term)
open Silmaril.Wasm.Cfg.Proofs.MachineLDivI (resB_of_stays qx_div pos_start lift_rest)
open Silmaril.Wasm.Cfg.Proofs.MachineLLogDivB (stays_point reach_logDiv lifted_lift)
open Silmaril.Wasm.Cfg.Proofs.MachineLDivB (gotoN_entry)

theorem mrun_trans {body : Expr} {a b c : MState H} {l l' : List (SCall H)}
    (h : MRunL body a l b) (h' : MRunL body b l' c) : MRunL body a (l ++ l') c := by
  induction h with
  | refl => simpa using h'
  | step hs _ ih => simpa [List.append_assoc] using MRunL.step hs (ih h')

/-- **The point of an infinite oracle-answered run**, natively. -/
theorem point_of {body : Expr} {g : ℕ → MState H} (hg : ∀ n, StepK body (g n) (g (n + 1)))
    (hok : MInv body (g 0)) : ∃ n₀, PointT body g n₀ := by
  obtain ⟨n₀, ⟨p, c, i, sg, stk, ls, s, f, hgn, hc, hsg, hok', hst⟩ |
    ⟨⟨p, c, i, sg, bt, b₀, sg₀, ls, np, nr, N, s, f, hp, hsg₀, hokp, har, hgn⟩, hst⟩⟩ :=
    stays_point hg hok
  · refine ⟨n₀, .inl ⟨p, c, i, stk, ls, s, f, hgn, hc, ?_⟩⟩
    have hls : ls.length = p.length := by simpa using Proofs.Machine.framesOk_length _ _ hok'
    have hlk : lookup body ⟨p, i⟩ = some sg := by rw [lookup_eq]; simp [hc, hsg]
    have hres := resB_of_stays hgn hls hlk (hst n₀ le_rfl)
    rw [lift_rest hsg]
    exact qx_div (g := g) (.inl ⟨n₀, p, c, i, sg, [], sg.instrs, ls, pos_start hc hsg, hok', rfl,
      fun m hm => hst m (by omega), hres⟩)
  · refine ⟨n₀, .inr ⟨p, c, i, sg, bt, b₀, ls, np, nr, N, s, f, hp, har, hgn, ?_⟩⟩
    have hls : ls.length = p.length := by simpa using Proofs.Machine.framesOk_length _ _ hokp
    obtain ⟨ht, -, -⟩ := pos_term hp rfl
    have hcA : seqAt body (p ++ [(i, 0)]) = some b₀ := by
      rw [Proofs.Machine.seqAt_append]; simp [hp.hc, hp.hsg, ht, armOf]
    have hg0 := gotoN_entry hcA hsg₀
      (⟨if (true = true) then np else nr, (N.drop np).reverse, true, false, [], bt⟩ :: ls)
      (N.take np).reverse s f
    rw [List.length_append, List.length_singleton] at hg0
    have hdep : (g n₀).lbls.length - 1 = p.length := by rw [hgn]; simp [hls]
    exact qx_div (g := g) (.inr (.inl ⟨n₀, p, c, i, sg, sg.body, .loop bt b₀, bt, true, false, [], 0, b₀, N,
      np, nr, ls, hp, .loop, hokp, rfl, .plain (fun _ _ _ => nofun), rfl, har,
      by rw [hg0, hgn]; simp, fun m hm => by simpa [hdep] using hst m hm⟩))

/-- **The machine's divergence after a log is native divergence after a log** extending it by
oracle-answered calls only. -/
theorem machine_logDiv {body : Expr} {s : Store H} {f : Frame} {l : List (SCall H)}
    (h : MLogDivL body (initial body s f) l) :
    ∃ (c : List (SCall H)) (L : List (OCall H)), (∀ e ∈ c, CloseOk closedCallXP e) ∧
      L.map OCall.toS = l ++ c ∧ LogDivXP s f [] (liftInstrs body) L := by
  obtain ⟨st₁, l₁, l₂, l₃, hrun, rfl, hl₃, hend⟩ := h
  have hreach : ∀ st L₁ L₂ z, MRunL body (initial body s f) L₁ st → ReachL body st L₂ z →
      FunDivXP z.2.2 z.1 z.2.1 →
      ∃ L, L₁ ++ L₂ = L.map OCall.toS ∧ LogDivXP s f [] (liftInstrs body) L :=
    fun st L₁ L₂ z hr hR hY =>
      reach_logDiv (MachineLPend.pending_iff.2 ⟨st, L₁, L₂, hr, hR, rfl⟩) hY (lifted_lift body)
  rcases hend with ⟨st₂, hs, hd⟩ | ⟨z, hR, hY⟩
  · rcases hd with ⟨g, hg0, hg⟩ | ⟨st₃, l₅, z, hr₃, hR, hl₅, hY⟩
    · have hok₂ : MInv body st₂ := mstep_ok hs (run_ok hrun (initial_ok body s f))
      obtain ⟨n₀, hpt⟩ := point_of hg (by rw [hg0]; exact hok₂)
      obtain ⟨K, G₁, lg₁, h0, hK, hG₁, hl₁⟩ := mrun_index hrun
      choose glog hglog using hg
      let G : ℕ → MState H := fun k => if k ≤ K then G₁ k else g (k - (K + 1))
      let lg : ℕ → List (SCall H) := fun k =>
        if k < K then lg₁ k else if k = K then l₂ ++ l₃ else glog (k - (K + 1))
      have hGs : ∀ k, k < K + 1 + n₀ → MStepL body (G k) (lg k) (G (k + 1)) := by
        intro k hk
        rcases Nat.lt_trichotomy k K with hlt | rfl | hgt
        · simp only [G, lg, show k ≤ K by omega, show k + 1 ≤ K by omega, hlt, ↓reduceIte]
          exact hG₁ k hlt
        · simp only [G, lg, le_refl, ↓reduceIte, lt_irrefl, show ¬ (k + 1 ≤ k) by omega,
            Nat.sub_self]
          rw [hK, hg0]; exact hs
        · simp only [G, lg, show ¬ k ≤ K by omega, show ¬ k + 1 ≤ K by omega,
            show ¬ k < K by omega, show k ≠ K by omega, ↓reduceIte]
          rw [show k + 1 - (K + 1) = (k - (K + 1)) + 1 by omega]
          exact (hglog _).1
      have hGN : G (K + 1 + n₀) = g n₀ := by
        simp only [G, show ¬ (K + 1 + n₀ ≤ K) by omega, ↓reduceIte]
        congr 1; omega
      have hptG : PointT body G (K + 1 + n₀) := by
        unfold PointT; rw [hGN]; exact hpt
      have hG0 : G 0 = initial body s f := by simp [G, h0]
      obtain ⟨L, hL, hd⟩ := prefix_logDiv hGs hptG hG0
      refine ⟨l₃ ++ segLog glog 0 n₀, L,
        allOk_append.2 ⟨hl₃, segLog_allOk (fun m => (hglog m).2) n₀ 0⟩, ?_, hd⟩
      rw [← hL, show K + 1 + n₀ = K + (1 + n₀) by omega, segLog_add, segLog_add, segLog_one]
      have h1 : segLog lg 0 K = l₁ := by
        rw [← hl₁]
        exact segLog_congr K 0 0 (fun m hm => by simp [lg, show m < K from by omega])
      have h2 : segLog lg (0 + K + 1) n₀ = segLog glog 0 n₀ :=
        segLog_congr n₀ _ 0 (fun m _ => by
          simp only [lg, show ¬ (0 + K + 1 + m < K) by omega, show 0 + K + 1 + m ≠ K by omega,
            ↓reduceIte]
          congr 1; omega)
      have h3 : lg (0 + K) = l₂ ++ l₃ := by simp [lg]
      rw [h1, h3, h2]; simp
    · obtain ⟨l₄, hr₄, hl₄⟩ := MachineLDivF.stepK_run hr₃
      have hrun' := mrun_trans (MRunL.step hs hr₄) (.refl st₃)
      obtain ⟨L, hL, hd⟩ := hreach st₃ (l₁ ++ ((l₂ ++ l₃) ++ l₄)) l₅ z
        (mrun_trans hrun (by simpa using hrun')) hR hY
      exact ⟨l₃ ++ l₄ ++ l₅, L, allOk_append.2 ⟨allOk_append.2 ⟨hl₃, hl₄⟩, hl₅⟩,
        by rw [← hL]; simp, hd⟩
  · obtain ⟨L, hL, hd⟩ := hreach st₁ l₁ (l₂ ++ l₃) z hrun hR hY
    exact ⟨l₃, L, hl₃, by rw [← hL]; simp, hd⟩

end Silmaril.Wasm.Cfg.Proofs.MachineLLogDivC
