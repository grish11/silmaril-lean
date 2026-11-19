module

public import Silmaril.Proofs.Wasm.Cfg.MachineLLogDivC
public import Silmaril.Games.Abstract.ModuleInf.Thms

@[expose] public section

/-!
# Productive runs of the machine (H2, proofs)

`prod_prepend`: a finite logged run in front of a productive run. `prod_of_chain`: a chain of
nonempty finite runs whose logs concatenate to a stream is a productive run (the global step index
of a run inside segment `n` is the sum `S n` of the lengths before it).
-/

namespace Silmaril.Wasm.Cfg.Proofs.MachineLProd

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.Shape
open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Abstract (SCall)
open Silmaril.Wasm.Cfg.Proofs.MachineLLogDivP (segLog segLog_add segLog_one)
open Silmaril.Wasm.Cfg.Proofs.MachineLLogDivC (segLog_congr mrun_index)

variable {H : Type}

theorem segLog_eq (lg : ℕ → List (SCall H)) :
    ∀ (K a : ℕ), segLog lg a K = ((List.range K).map fun k => lg (a + k)).flatten
  | 0, _ => rfl
  | K + 1, a => by
    rw [segLog_add lg a K 1, segLog_one, segLog_eq lg K a, List.range_succ]
    simp

theorem flatMap_range (lg : ℕ → List (SCall H)) (K : ℕ) :
    (List.range K).flatMap lg = segLog lg 0 K := by
  rw [segLog_eq]; simp [List.flatMap]

theorem streamPrefix_of_prefix {l l' : List (SCall H)} {ω : ℕ → SCall H} (hp : l <+: l')
    (h : StreamPrefix l' ω) : StreamPrefix l ω := by
  obtain ⟨t, rfl⟩ := hp
  intro i hi
  rw [h i (by simp; omega)]
  simp [List.getElem_append_left hi]

theorem segLog_prefix (lg : ℕ → List (SCall H)) {m n : ℕ} (h : m ≤ n) :
    segLog lg 0 m <+: segLog lg 0 n := by
  rw [show n = m + (n - m) by omega, segLog_add]
  exact List.prefix_append _ _

/-- **A finite run in front of a productive run.** -/
theorem prod_prepend {body : Expr} {st st' : MState H} {l : List (SCall H)} {ω : ℕ → SCall H}
    (hr : MRunL body st l st') (hp : ProdL body st' ω) : ProdL body st (l ++ω ω) := by
  obtain ⟨K, G', lg', h0, hK, hG', hl⟩ := mrun_index hr
  obtain ⟨g, lg, hg0, hg, hc⟩ := hp
  refine ⟨fun k => if k ≤ K then G' k else g (k - K),
    fun k => if k < K then lg' k else lg (k - K), by simp [h0], fun k => ?_, ?_⟩
  · rcases Nat.lt_or_ge k K with hk | hk
    · simp only [show k ≤ K by omega, show k + 1 ≤ K by omega, hk, ↓reduceIte]
      exact hG' k hk
    · simp only [show ¬ k < K by omega, show ¬ k + 1 ≤ K by omega, ↓reduceIte]
      rw [show k + 1 - K = (k - K) + 1 by omega]
      by_cases hkK : k ≤ K
      · have : k = K := by omega
        subst this
        simp only [le_refl, ↓reduceIte, Nat.sub_self, hK, ← hg0]
        exact hg 0
      · simp only [hkK, ↓reduceIte]
        exact hg (k - K)
  · have hfun : (fun k => if k < K then lg' k else lg (k - K)) =
        ((List.range K).map lg') ++ω lg := by
      funext k
      simp only [streamAppend, List.length_map, List.length_range]
      split <;> simp_all
    rw [hfun]
    have := streamConcat_append (ls := (List.range K).map lg') hc
    rwa [show ((List.range K).map lg').flatten = l by
      rw [← hl, segLog_eq]; simp] at this

/-- A nonempty run, indexed. -/
theorem mrun_index1 {body : Expr} {st st₁ st' : MState H} {l₁ l₂ : List (SCall H)}
    (hs : MStepL body st l₁ st₁) (hr : MRunL body st₁ l₂ st') :
    ∃ (K : ℕ) (G : ℕ → MState H) (lg : ℕ → List (SCall H)), 1 ≤ K ∧ G 0 = st ∧ G K = st' ∧
      (∀ k, k < K → MStepL body (G k) (lg k) (G (k + 1))) ∧ segLog lg 0 K = l₁ ++ l₂ := by
  obtain ⟨K, G, lg, h0, hK, hG, hl⟩ := mrun_index hr
  refine ⟨K + 1, fun k => if k = 0 then st else G (k - 1),
    fun k => if k = 0 then l₁ else lg (k - 1), by omega, by simp, by simp [hK], fun k hk => ?_, ?_⟩
  · rcases k with _ | k
    · simpa [h0] using hs
    · simpa using hG k (by omega)
  · have hc : segLog (fun k => if k = 0 then l₁ else lg (k - 1)) 1 K = segLog lg 0 K :=
      segLog_congr K 1 0 (fun m _ => by simp [Nat.add_comm 1 m])
    simp only [segLog, ↓reduceIte, zero_add, hc, hl]

/-- Cumulative lengths. -/
def cum (K : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => cum K n + K n

theorem cum_ge {K : ℕ → ℕ} (hK : ∀ n, 1 ≤ K n) : ∀ n, n ≤ cum K n
  | 0 => le_rfl
  | n + 1 => by simp only [cum]; have := cum_ge hK n; have := hK n; omega

theorem cum_mono {K : ℕ → ℕ} {n m : ℕ} (h : n ≤ m) : cum K n ≤ cum K m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => simp only [cum]; omega

/-- **A chain of nonempty finite runs is a productive run** of the concatenated stream. -/
theorem prod_of_chain {body : Expr} {X : ℕ → MState H} {L : ℕ → List (SCall H)}
    {ω : ℕ → SCall H}
    (hX : ∀ n, ∃ l₁ st₁ l₂, MStepL body (X n) l₁ st₁ ∧ MRunL body st₁ l₂ (X (n + 1)) ∧
      L n = l₁ ++ l₂)
    (hc : StreamConcat L ω) : ProdL body (X 0) ω := by
  have hseg : ∀ n, ∃ (K : ℕ) (G : ℕ → MState H) (lg : ℕ → List (SCall H)), 1 ≤ K ∧
      G 0 = X n ∧ G K = X (n + 1) ∧ (∀ k, k < K → MStepL body (G k) (lg k) (G (k + 1))) ∧
      segLog lg 0 K = L n := fun n => by
    obtain ⟨l₁, st₁, l₂, hs, hr, hL⟩ := hX n
    obtain ⟨K, G, lg, hK, h0, hKe, hG, hl⟩ := mrun_index1 hs hr
    exact ⟨K, G, lg, hK, h0, hKe, hG, by rw [hl, hL]⟩
  choose K G lgs hK1 h0 hKe hsteps hlog using hseg
  classical
  have hex : ∀ t, ∃ n, t < cum K (n + 1) := fun t =>
    ⟨t, by have := cum_ge hK1 (t + 1); omega⟩
  let seg : ℕ → ℕ := fun t => Nat.find (hex t)
  have hA : ∀ t, t < cum K (seg t + 1) := fun t => Nat.find_spec (hex t)
  have hB : ∀ t, cum K (seg t) ≤ t := fun t => by
    rcases h : seg t with _ | m
    · simp [cum]
    · have := Nat.find_min (hex t) (show m < seg t by omega)
      omega
  have hC : ∀ t n, cum K n ≤ t → t < cum K (n + 1) → seg t = n := fun t n h1 h2 => by
    have hle : seg t ≤ n := Nat.find_min' (hex t) h2
    by_contra hne
    have := cum_mono (K := K) (show seg t + 1 ≤ n by omega)
    have := hA t
    omega
  refine ⟨fun t => G (seg t) (t - cum K (seg t)), fun t => lgs (seg t) (t - cum K (seg t)),
    ?_, fun t => ?_, ?_⟩
  · have : seg 0 = 0 := hC 0 0 (by simp [cum]) (by simp [cum]; exact hK1 0)
    simp only [this, cum, Nat.sub_zero, h0]
  · show MStepL body (G (seg t) (t - cum K (seg t))) (lgs (seg t) (t - cum K (seg t)))
      (G (seg (t + 1)) (t + 1 - cum K (seg (t + 1))))
    have h1 := hA t
    have h2 := hB t
    generalize hn : seg t = n at h1 h2 ⊢
    simp only [cum] at h1
    by_cases hlast : t + 1 < cum K (n + 1)
    · have hs1 : seg (t + 1) = n := hC (t + 1) n (by omega) hlast
      simp only [hs1]
      rw [show t + 1 - cum K n = (t - cum K n) + 1 by omega]
      exact hsteps n (t - cum K n) (by simp only [cum] at hlast; omega)
    · have hs1 : seg (t + 1) = n + 1 :=
        hC (t + 1) (n + 1) (by simp only [cum] at hlast ⊢; omega)
          (by simp only [cum]; have := hK1 (n + 1); simp only [cum] at hlast; omega)
      simp only [hs1]
      have hoff : t + 1 - cum K (n + 1) = 0 := by simp only [cum] at hlast ⊢; omega
      rw [hoff, h0 (n + 1), ← hKe n]
      have hk : t - cum K n + 1 = K n := by simp only [cum] at hlast; omega
      rw [← hk]
      exact hsteps n (t - cum K n) (by omega)
  · have hsegs : ∀ n, segLog (fun t => lgs (seg t) (t - cum K (seg t))) 0 (cum K n) =
        (List.range n).flatMap L := by
      intro n
      induction n with
      | zero => simp [cum, segLog]
      | succ n ih =>
        simp only [cum]
        rw [segLog_add, ih, zero_add, List.range_succ, List.flatMap_append]
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
        rw [← hlog n]
        congr 1
        refine segLog_congr (K n) (cum K n) 0 (fun m hm => ?_)
        have : seg (cum K n + m) = n := hC _ n (by omega) (by simp only [cum]; omega)
        simp [this]
    refine ⟨fun m => ?_, fun N => ?_⟩
    · rw [flatMap_range]
      refine streamPrefix_of_prefix (segLog_prefix _ (cum_ge hK1 m)) ?_
      rw [hsegs]; exact hc.1 m
    · obtain ⟨n, hn⟩ := hc.2 N
      exact ⟨cum K n, by rw [flatMap_range, hsegs]; exact hn⟩

/-! ## Native productive runs on the machine -/

open Silmaril.Wasm.Abstract (EvalLXPS EvalLXPh OCall InfLXP evalLXPh_session)
open Silmaril.Wasm.Abstract.CallXP (POut)
open Silmaril.Wasm.Cfg.Proofs.Machine (restAt_cons restAt_end restAt_zero lookup_eq)
open Silmaril.Wasm.Cfg.Proofs.MachineLFwd
open Silmaril.Wasm.Cfg.Proofs.MachineLBwd (Pos pos_head pos_next pos_term pos_last_nonstruct
  isStruct_terminator lift_op lift_block lift_loop lift_if lift_try nil_inv armOf_if'
  liftInstrs_ite)
open Silmaril.Wasm.Cfg.Proofs.MachineLDivB (gotoN_entry)
open Silmaril.Wasm.Cfg.Proofs.MachineLDivI (pos_start lift_rest)
open Silmaril.Wasm.Cfg.Proofs.MachineLLogDiv (enter_at struct_target struct_target_arm
  loopBack_target loopBack_target_arm lxph_nil ne_trap_of_blockVals seg0_of_run)

/-- A stream of canonical calls as session calls. -/
def toSS (ω : ℕ → OCall H) : ℕ → SCall H := fun n => (ω n).toS

theorem toSS_append (l : List (OCall H)) (ω : ℕ → OCall H) :
    toSS (l ++ω ω) = l.map OCall.toS ++ω toSS ω := by
  funext n
  simp only [toSS, streamAppend, List.length_map]
  split <;> simp

theorem infL_nil {s : Store H} {f : Frame} {N : List Val} {ω : ℕ → OCall H}
    (h : InfLXP s f N [] ω) : False := by cases h

theorem infL_ne {s : Store H} {f : Frame} {N : List Val} {c : List Instr} {j : Nat}
    {ω : ℕ → OCall H} (h : InfLXP s f N (liftInstrs (restAt c j)) ω) :
    ∃ sg, (segment c)[j]? = some sg := by
  cases hs : (segment c)[j]? with
  | none => rw [restAt_end hs] at h; exact (infL_nil (by simpa [liftInstrs] using h)).elim
  | some sg => exact ⟨sg, rfl⟩

theorem prod_step {body : Expr} {st st' : MState H} {l : List (SCall H)} {ω : ℕ → SCall H}
    (hs : MStepL body st l st') (hp : ProdL body st' ω) : ProdL body st (l ++ω ω) := by
  simpa using prod_prepend (MRunL.step hs (.refl _)) hp

/-- **The block clause**: from block `i`, its instructions `pre` run natively with the log `l₀`,
the machine runs productively with `l₀` then the stream. -/
def BlkP (body : Expr) (s : Store H) (f : Frame) (N : List Val) (es : List BExpr)
    (ω : ℕ → OCall H) : Prop :=
  ∀ (p : List SeqStep) (c : List Instr) (i : Nat) (sg : Segment) (pre post : List Instr)
    (ls : List LFrame) (s₀ : Store H) (f₀ : Frame) (N₀ : List Val) (l₀ : List (SCall H)),
    Pos body p c i sg pre post → es = liftInstrs post ++ liftInstrs (restAt c (i + 1)) →
    FramesOk body p.reverse ls →
    EvalLXPS s₀ f₀ N₀ (liftInstrs pre) l₀ (s, f, .flow (.normal N)) →
    ProdL body ⟨.block ⟨p, i⟩, N₀.reverse, ls, s₀, f₀⟩ (l₀ ++ω toSS ω)

/-- **The arm clause**: at the entry of a loop's arm, entered from `(s, f, N)`. -/
def ArmP (body : Expr) (s : Store H) (f : Frame) (N : List Val) (es : List BExpr)
    (ω : ℕ → OCall H) : Prop :=
  ∀ (p : List SeqStep) (c : List Instr) (i : Nat) (sg : Segment) (pre : List Instr)
    (bt : BlockType) (b₀ : List Instr) (sg₀ : Segment) (ls : List LFrame) (np nr : Nat),
    Pos body p c i sg pre [.loop bt b₀] → (segment b₀)[0]? = some sg₀ →
    FramesOk body p.reverse ls → arity f bt = some (np, nr) →
    es = liftInstr (.loop bt b₀) :: liftInstrs (restAt c (i + 1)) →
    ProdL body ⟨.block ⟨p ++ [(i, 0)], 0⟩, (N.take np).reverse,
      ⟨np, (N.drop np).reverse, true, false, [], bt⟩ :: ls, s, f⟩ (toSS ω)

/-- **A finished flat instruction, then a productive rest.** -/
theorem flat_cont_prod {body : Expr} {p : List SeqStep} {c : List Instr} {i : Nat} {sg : Segment}
    {pre post' : List Instr} {e : Instr} {ls : List LFrame} {s s₀ s₂ : Store H} {f f₀ f₂ : Frame}
    {N N₀ N₂ : List Val} {l₀ l_e : List (SCall H)} {es' : List BExpr} {ω₂ : ℕ → OCall H}
    (hp : Pos body p c i sg pre (e :: post')) (hse : ¬ Instr.IsStruct e)
    (hok : FramesOk body p.reverse ls)
    (hpre : EvalLXPS s₀ f₀ N₀ (liftInstrs pre) l₀ (s, f, .flow (.normal N)))
    (hhead : EvalLXPS s f N [liftInstr e] l_e (s₂, f₂, .flow (.normal N₂)))
    (htl : es' = liftInstrs post' ++ liftInstrs (restAt c (i + 1)))
    (hk : InfLXP s₂ f₂ N₂ es' ω₂) (ih : BlkP body s₂ f₂ N₂ es' ω₂) :
    ProdL body ⟨.block ⟨p, i⟩, N₀.reverse, ls, s₀, f₀⟩ ((l₀ ++ l_e) ++ω toSS ω₂) := by
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
    obtain ⟨sg', hsg'⟩ := infL_ne hk
    have hr : EvalLXPS s₀ f₀ (N₀.reverse).reverse (liftInstrs (MachineL.codeOf sg)) (l₀ ++ l_e)
        (s₂, f₂, .flow (.normal N₂)) := by
      rw [List.reverse_reverse, codeOf_eq, hp.hinstrs]; exact hpre'
    have hstep := MStepL.run hb ht hr
      (.next (by simpa using gotoN_entry hp.hc hsg' ls N₂.reverse s₂ f₂))
    have := ih p c (i + 1) sg' [] sg'.instrs ls s₂ f₂ N₂ [] (pos_start hp.hc hsg')
      (lift_rest hsg') hok .nil
    simpa [streamAppend_nil] using prod_step hstep this

/-- **A loop iterating forever**, from the entry of its arm, is a productive run of the
concatenated iterations. -/
theorem loopInf_prod {body : Expr} {p : List SeqStep} {c : List Instr} {i : Nat} {sg sg₀ : Segment}
    {pre : List Instr} {bt : BlockType} {b₀ : List Instr} {ls : List LFrame} {np nr : Nat}
    {ω : ℕ → OCall H} (st : ℕ → Store H × Frame × List Val) (l : ℕ → List (OCall H))
    (hp : Pos body p c i sg pre [.loop bt b₀]) (hsg₀ : (segment b₀)[0]? = some sg₀)
    (hok : FramesOk body p.reverse ls) (har : ∀ n, arity (st n).2.1 bt = some (np, nr))
    (hit : ∀ n, ∃ vs, EvalLXPh (st n).1 (st n).2.1 ((st n).2.2.take np) (liftInstrs b₀) (l n)
        ((st (n + 1)).1, (st (n + 1)).2.1, .flow (.brk 0 vs)) ∧
      (st (n + 1)).2.2 = vs.take np ++ (st n).2.2.drop np)
    (hω : StreamConcat l ω) :
    ProdL body ⟨.block ⟨p ++ [(i, 0)], 0⟩, ((st 0).2.2.take np).reverse,
      ⟨np, ((st 0).2.2.drop np).reverse, true, false, [], bt⟩ :: ls, (st 0).1, (st 0).2.1⟩
      (toSS ω) := by
  let X : ℕ → MState H := fun n => ⟨.block ⟨p ++ [(i, 0)], 0⟩, ((st n).2.2.take np).reverse,
    ⟨np, ((st n).2.2.drop np).reverse, true, false, [], bt⟩ :: ls, (st n).1, (st n).2.1⟩
  refine prod_of_chain (X := X) (L := fun n => (l n).map OCall.toS) (fun n => ?_) ?_
  · obtain ⟨vs, hrun, hst⟩ := hit n
    have hlb := evalLXPh_session hrun (by simp)
    obtain ⟨l₁, st₁, l₂, hs, hr, hl⟩ := loopBack_target_arm hp hok (har n) hsg₀ hlb
    refine ⟨l₁, st₁, l₂, hs, ?_, hl⟩
    simpa [X, hst] using hr
  · exact streamConcat_map OCall.toS hω

theorem toSS_eq (l₀ : List (SCall H)) (l : List (OCall H)) (ω : ℕ → OCall H) :
    l₀ ++ω toSS (l ++ω ω) = (l₀ ++ l.map OCall.toS) ++ω toSS ω := by
  rw [toSS_append, streamAppend_append]

/-- **The main induction**: a productive run satisfies both clauses. -/
theorem infL_mot {body : Expr} {s : Store H} {f : Frame} {N : List Val} {es : List BExpr}
    {ω : ℕ → OCall H} (h : InfLXP s f N es ω) : BlkP body s f N es ω ∧ ArmP body s f N es ω := by
  induction h with
  | args h _ =>
    refine ⟨fun p c i sg pre post ls s₀ f₀ N₀ l₀ hp hes hok hpre => ?_,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hes => by simp [liftInstr] at hes⟩
    obtain ⟨e, post', rfl, hhd, -⟩ := pos_head hp hes
    obtain ⟨-, rfl, -⟩ := lift_op hhd.symm
    exact (infL_nil h).elim
  | @callK s s₁ s₂ f f₁ stk stk₁ ws x args es a fi ps rs l₁ ω hargs hfi hty hk ih =>
    refine ⟨fun p c i sg pre post ls s₀ f₀ N₀ l₀ hp hes hok hpre => ?_,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hes => by simp [liftInstr] at hes⟩
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    obtain ⟨rfl, rfl, hse⟩ := lift_op hhd.symm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := lxph_nil hargs
    have hhead : EvalLXPS s f stk [liftInstr (.call x)]
        [SCall.mk a (stk.take ps.length).reverse s (.inl (.inl ws)) s₂]
        (s₂, f, .flow (.normal (ws.reverse ++ stk.drop ps.length))) := by
      simpa [liftInstr] using EvalLXPS.callRet (es := []) (l₂ := []) .nil hfi hty .nil
    rw [toSS_eq]
    simpa using flat_cont_prod hp hse hok hpre hhead htl hk ih.1
  | @indK s s₁ s₂ f f₁ stk stk₁ ws x y args es ad iv fa fi ps rs l₁ ω hargs hres hfi hty hy hk ih =>
    refine ⟨fun p c i sg pre post ls s₀ f₀ N₀ l₀ hp hes hok hpre => ?_,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hes => by simp [liftInstr] at hes⟩
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    obtain ⟨rfl, rfl, hse⟩ := lift_op hhd.symm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := lxph_nil hargs
    have hhead := EvalLXPS.indRet (es := []) (l₂ := []) (ws := ws) (s₂ := s₂) (stk₁ := stk₁) .nil
      hres hfi hty hy .nil
    rw [toSS_eq]
    simpa using flat_cont_prod hp hse hok hpre (by simpa [liftInstr] using hhead) htl hk ih.1
  | @refK s s₁ s₂ f f₁ stk stk₁ ws y args es fa fi ps rs l₁ ω hargs hfi hty hy hk ih =>
    refine ⟨fun p c i sg pre post ls s₀ f₀ N₀ l₀ hp hes hok hpre => ?_,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hes => by simp [liftInstr] at hes⟩
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    obtain ⟨rfl, rfl, hse⟩ := lift_op hhd.symm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := lxph_nil hargs
    have hhead := EvalLXPS.refRet (es := []) (l₂ := []) (ws := ws) (s₂ := s₂) (stk₁ := stk₁) .nil
      hfi hty hy .nil
    rw [toSS_eq]
    simpa using flat_cont_prod hp hse hok hpre (by simpa [liftInstr] using hhead) htl hk ih.1
  | @opK s s₁ s₂ f f₁ f₂ stk stk₁ stk₂ i' args es l₁ ω hi hargs hflat hk ih =>
    refine ⟨fun p c i sg pre post ls s₀ f₀ N₀ l₀ hp hes hok hpre => ?_,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hes => by simp [liftInstr] at hes⟩
    obtain ⟨e, post', rfl, hhd, htl⟩ := pos_head hp hes
    obtain ⟨he, rfl, hse⟩ := lift_op hhd.symm
    subst he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := lxph_nil hargs
    have hhead := EvalLXPS.opOk (es := []) (l₂ := []) hi .nil hflat .nil
    rw [hhd] at hhead
    rw [toSS_eq]
    simpa using flat_cont_prod hp hse hok hpre hhead htl hk ih.1
  | @block s f stk bt bd es np nr ω har hk ih =>
    refine ⟨fun p c i sg pre post ls s₀ f₀ N₀ l₀ hp hes hok hpre => ?_,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hes => by simp [liftInstr] at hes⟩
    obtain ⟨e, post', rfl, hhd, -⟩ := pos_head hp hes
    obtain ⟨b₀, rfl, rfl⟩ := lift_block hhd.symm
    obtain ⟨-, rfl, rfl⟩ := pos_term hp rfl
    rw [← restAt_zero b₀] at hk
    obtain ⟨sg₀, hsg₀⟩ := infL_ne hk
    obtain ⟨hcA, hokA, hstep⟩ := enter_at hp hok hpre .block (.plain (fun _ _ _ => nofun)) rfl har
      hsg₀
    have := ih.1 (p ++ [(i, 0)]) b₀ 0 sg₀ [] sg₀.instrs _ s f (stk.take np) []
      (pos_start hcA hsg₀) (by simpa [restAt_zero] using lift_rest hsg₀) hokA .nil
    simpa [streamAppend_nil] using prod_step hstep this
  | @blockK s s₁ f f₁ stk vs bt bd es np nr fl l₁ ω har hbody hvs hk ih =>
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
    obtain ⟨sg', hsg'⟩ := infL_ne hk
    have hrunM := struct_target hp ⟨_, _, _, _, .block⟩ hok hpre hrun hsg'
    have := ih.1 p c (i + 1) sg' [] sg'.instrs ls s₁ f₁ _ [] (pos_start hp.hc hsg') (lift_rest hsg')
      hok .nil
    rw [toSS_eq]
    simpa [streamAppend_nil] using prod_prepend hrunM this
  | @loop s f stk bt bd es np nr ω har hk ih =>
    refine ⟨fun p c i sg pre post ls s₀ f₀ N₀ l₀ hp hes hok hpre => ?_,
      fun p c i sg pre bt' b₀ sg₀ ls np' nr' hp hsg₀ hok har' hes => ?_⟩
    · obtain ⟨e, post', rfl, hhd, -⟩ := pos_head hp hes
      obtain ⟨b₀, rfl, rfl⟩ := lift_loop hhd.symm
      obtain ⟨-, rfl, rfl⟩ := pos_term hp rfl
      rw [← restAt_zero b₀] at hk
      obtain ⟨sg₀, hsg₀⟩ := infL_ne hk
      obtain ⟨hcA, hokA, hstep⟩ := enter_at hp hok hpre .loop (.plain (fun _ _ _ => nofun)) rfl har
        hsg₀
      have := ih.1 (p ++ [(i, 0)]) b₀ 0 sg₀ [] sg₀.instrs _ s f (stk.take np) []
        (pos_start hcA hsg₀) (by simpa [restAt_zero] using lift_rest hsg₀) hokA .nil
      simpa [streamAppend_nil] using prod_step hstep this
    · simp only [liftInstr, List.cons.injEq, BExpr.loop.injEq] at hes
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hes
      rw [har] at har'; simp only [Option.some.injEq, Prod.mk.injEq] at har'
      obtain ⟨rfl, rfl⟩ := har'
      obtain ⟨ht, -, -⟩ := pos_term hp rfl
      have hcA : seqAt body (p ++ [(i, 0)]) = some b₀ := by
        rw [Proofs.Machine.seqAt_append]; simp [hp.hc, hp.hsg, ht, armOf]
      have hokA := MachineLBwd.arm_ok (a := 0) hp .loop rfl hok np (stk.drop np).reverse
      have := ih.1 (p ++ [(i, 0)]) b₀ 0 sg₀ [] sg₀.instrs _ s f (stk.take np) []
        (pos_start hcA hsg₀) (by simpa [restAt_zero] using lift_rest hsg₀) (by simpa using hokA) .nil
      simpa [streamAppend_nil] using this
  | @loopK s s₁ f f₁ stk vs bt bd es np nr l₁ ω har hbody hk ih =>
    have hrun : ∀ b₀, bd = liftInstrs b₀ → EvalLXPS s f stk [liftInstr (.loop bt b₀)]
        (l₁.map OCall.toS) (s₁, f₁, .flow (.normal (vs.take nr ++ stk.drop np))) := by
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
      obtain ⟨sg', hsg'⟩ := infL_ne hk
      have hrunM := struct_target hp ⟨_, _, _, _, .loop⟩ hok hpre (hrun b₀ rfl) hsg'
      have := ih.1 p c (i + 1) sg' [] sg'.instrs ls s₁ f₁ _ [] (pos_start hp.hc hsg')
        (lift_rest hsg') hok .nil
      rw [toSS_eq]
      simpa [streamAppend_nil] using prod_prepend hrunM this
    · simp only [liftInstr, List.cons.injEq, BExpr.loop.injEq] at hes
      obtain ⟨⟨rfl, rfl⟩, htl⟩ := hes
      subst htl
      rw [har] at har'; simp only [Option.some.injEq, Prod.mk.injEq] at har'
      obtain ⟨rfl, rfl⟩ := har'
      obtain ⟨sg', hsg'⟩ := infL_ne hk
      have hrunM := struct_target_arm hp hok har hsg₀ (hrun b₀ rfl) hsg'
      have := ih.1 p c (i + 1) sg' [] sg'.instrs ls s₁ f₁ _ [] (pos_start hp.hc hsg')
        (lift_rest hsg') hok .nil
      rw [toSS_append]
      simpa [streamAppend_nil] using prod_prepend hrunM this
  | @loopBack s s₁ f f₁ stk vs bt bd es np nr l₁ ω har hbody hk ih =>
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
      rw [toSS_eq]
      simpa using prod_prepend hrunM this
    · simp only [liftInstr, List.cons.injEq, BExpr.loop.injEq] at hes
      obtain ⟨⟨rfl, rfl⟩, htl⟩ := hes
      rw [har] at har'; simp only [Option.some.injEq, Prod.mk.injEq] at har'
      obtain ⟨rfl, rfl⟩ := har'
      obtain ⟨lb₁, stb, lb₂, hsb, hrb, hlbe⟩ := loopBack_target_arm hp hok har hsg₀ hlb
      have hrunM := MRunL.step hsb hrb
      rw [← hlbe] at hrunM
      have := ih.2 p c i sg pre bt b₀ sg₀ ls np nr hp hsg₀ hok har₁ (by simp [liftInstr, htl])
      rw [toSS_append]
      exact prod_prepend hrunM this
  | @loopInf s f stk bt bd es np nr ω st l h0 har hit hω =>
    refine ⟨fun p c i sg pre post ls s₀ f₀ N₀ l₀ hp hes hok hpre => ?_,
      fun p c i sg pre bt' b₀ sg₀ ls np' nr' hp hsg₀ hok har' hes => ?_⟩
    · obtain ⟨e, post', rfl, hhd, -⟩ := pos_head hp hes
      obtain ⟨b₀, rfl, rfl⟩ := lift_loop hhd.symm
      obtain ⟨-, rfl, rfl⟩ := pos_term hp rfl
      obtain ⟨vs₀, hrun₀, -⟩ := hit 0
      have har0 : arity f bt = some (np, nr) := by simpa [h0] using har 0
      obtain ⟨sg₀, hsg₀⟩ := seg0_of_run (evalLXPh_session hrun₀ (by simp))
      obtain ⟨hcA, hokA, hstep⟩ := enter_at hp hok hpre .loop (.plain (fun _ _ _ => nofun)) rfl
        har0 hsg₀
      have hP := loopInf_prod st l hp hsg₀ hok har hit hω
      rw [h0] at hP
      simpa using prod_step hstep hP
    · simp only [liftInstr, List.cons.injEq, BExpr.loop.injEq] at hes
      obtain ⟨⟨rfl, rfl⟩, -⟩ := hes
      have har0 : arity f bt = some (np, nr) := by simpa [h0] using har 0
      rw [har0] at har'; simp only [Option.some.injEq, Prod.mk.injEq] at har'
      obtain ⟨rfl, rfl⟩ := har'
      have hP := loopInf_prod st l hp hsg₀ hok har hit hω
      rw [h0] at hP
      simpa using hP
  | cond hk _ =>
    refine ⟨fun p c i sg pre post ls s₀ f₀ N₀ l₀ hp hes hok hpre => ?_,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hes => by simp [liftInstr] at hes⟩
    obtain ⟨e, post', rfl, hhd, -⟩ := pos_head hp hes
    obtain ⟨t₀, e₀, rfl, rfl, -, -⟩ := lift_if hhd.symm
    exact (infL_nil hk).elim
  | @arm s s₁ f f₁ stk stk₁ cv b bt cc tt el es np nr l₁ ω hc hb har hk ih =>
    refine ⟨fun p c i sg pre post ls s₀ f₀ N₀ l₀ hp hes hok hpre => ?_,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hes => by simp [liftInstr] at hes⟩
    obtain ⟨e, post', rfl, hhd, -⟩ := pos_head hp hes
    obtain ⟨t₀, e₀, rfl, rfl, rfl, rfl⟩ := lift_if hhd.symm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := lxph_nil hc
    obtain ⟨-, rfl, rfl⟩ := pos_term hp rfl
    rw [liftInstrs_ite, ← restAt_zero (if b then t₀ else e₀)] at hk
    obtain ⟨sg₀, hsg₀⟩ := infL_ne hk
    obtain ⟨hcA, hokA, hstep⟩ := enter_at hp hok hpre .if_ (.cond hb) (armOf_if' _ _ _ _) har hsg₀
    have := ih.1 _ _ 0 sg₀ [] sg₀.instrs _ _ _ (stk₁.take np) [] (pos_start hcA hsg₀)
      (by rw [liftInstrs_ite]; simpa [restAt_zero] using lift_rest hsg₀) hokA .nil
    simpa [streamAppend_nil] using prod_step hstep this
  | @ifK s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt cc tt el es np nr fl l₁ l₂ ω hc hb har harm hvs hk
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
    obtain ⟨sg', hsg'⟩ := infL_ne hk
    have hrunM := struct_target hp ⟨_, _, _, _, .if_⟩ hok hpre hrun hsg'
    have := ih.1 p c (i + 1) sg' [] sg'.instrs ls s₂ f₂ _ [] (pos_start hp.hc hsg') (lift_rest hsg')
      hok .nil
    rw [toSS_eq]
    simpa [streamAppend_nil] using prod_prepend hrunM this
  | @handler s f stk bt cs bd es np nr ω har hk ih =>
    refine ⟨fun p c i sg pre post ls s₀ f₀ N₀ l₀ hp hes hok hpre => ?_,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hes => by simp [liftInstr] at hes⟩
    obtain ⟨e, post', rfl, hhd, -⟩ := pos_head hp hes
    obtain ⟨b₀, rfl, rfl⟩ := lift_try hhd.symm
    obtain ⟨-, rfl, rfl⟩ := pos_term hp rfl
    rw [← restAt_zero b₀] at hk
    obtain ⟨sg₀, hsg₀⟩ := infL_ne hk
    obtain ⟨hcA, hokA, hstep⟩ := enter_at hp hok hpre .tryTable (.plain (fun _ _ _ => nofun)) rfl
      har hsg₀
    have := ih.1 (p ++ [(i, 0)]) b₀ 0 sg₀ [] sg₀.instrs _ s f (stk.take np) []
      (pos_start hcA hsg₀) (by simpa [restAt_zero] using lift_rest hsg₀) hokA .nil
    simpa [streamAppend_nil] using prod_step hstep this
  | @tryK s s₁ f f₁ stk vs bt cs bd es np nr fl l₁ ω har hbody hvs hk ih =>
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
    obtain ⟨sg', hsg'⟩ := infL_ne hk
    have hrunM := struct_target hp ⟨_, _, _, _, .tryTable⟩ hok hpre hrun hsg'
    have := ih.1 p c (i + 1) sg' [] sg'.instrs ls s₁ f₁ _ [] (pos_start hp.hc hsg') (lift_rest hsg')
      hok .nil
    rw [toSS_eq]
    simpa [streamAppend_nil] using prod_prepend hrunM this

/-- **A productive run of the body is a productive run of the machine** with the same stream,
the calls as session calls. -/
theorem infL_machine {body : Expr} {s : Store H} {f : Frame} {ω : ℕ → OCall H}
    (h : InfLXP s f [] (liftInstrs body) ω) : ProdL body (initial body s f) (toSS ω) := by
  have hm := (infL_mot (body := body) h).1
  rw [← restAt_zero body] at h
  obtain ⟨sg₀, hsg₀⟩ := infL_ne h
  have hg := gotoN_entry (body := body) (p := []) rfl hsg₀ [] [] s f
  rw [initial_eq] at hg
  simp only [Option.some.injEq] at hg
  rw [hg]
  simpa [streamAppend_nil] using hm [] body 0 sg₀ [] sg₀.instrs [] s f [] [] (pos_start rfl hsg₀)
    (by rw [← lift_rest hsg₀, restAt_zero]) trivial .nil

end Silmaril.Wasm.Cfg.Proofs.MachineLProd
