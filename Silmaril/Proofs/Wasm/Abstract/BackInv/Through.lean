module

public import Silmaril.Wasm.Abstract.BackInv.Defs
public import Silmaril.Proofs.Wasm.Abstract.HostCall.Div
import Silmaril.Wasm.Interp.Thms

/-!
# Divergence passes through host-free steps, for every invariant with closed-valid principal
types (proofs)

`HostCall.diverges_through` proves, for `Sim.ContextTyped` configurations in the deterministic
profile, that a divergent run passes through every host-free step: host-free steps join within
one step, and every other successor than the interpreter's shrinks the code
(`Silmaril.Wasm.Interp.step?_lag_at`). The proof reads only two things of typing: the interpreter's exactness
at the configuration's store (`interpHead_exact`, which uses `StoreOk` only through the principal
types of references, `Ref.type?_tyOk`) and the cast side conditions of the code
(`DeepAll IHeadInv`). Here it is proved for every invariant `I` kept by host-free steps whose
configurations have a store with closed-valid principal types (`StoreTy`) and the cast side
conditions (`diverges_through_of`).

* `refOk?_complete'`, `referenceStep?_complete'`, `interpHead_exact'`: the interpreter's
  exactness under `StoreTy` (the proofs of `refOk?_complete`, `referenceStep?_complete`,
  `interpHead_exact`, which used `StoreOk` only through `Ref.type?_tyOk`);
* `diverges_through_of`;
* `storeTy_of_storeOk`, `storeTy_deepAll_of_ctx`: `Sim.ContextTyped` configurations satisfy the
  hypotheses.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.BackInv

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Exec
open Silmaril.Wasm.SingleThreaded.Det Silmaril.Wasm.SingleThreaded.Exec.Interp
open Silmaril.Wasm.Abstract (StoreTy)

variable {H : Type}

theorem storeTy_of_storeOk {s : Store H} (hs : StoreOk s) : StoreTy s :=
  fun _ _ e => Ref.type?_tyOk hs e

theorem storeTy_deepAll_of_ctx {c : Config H} (h : Sim.ContextTyped c) :
    StoreTy c.store ∧ DeepAll IHeadInv c.frame c.code :=
  ⟨storeTy_of_storeOk (HostCall.contextTyped_storeOk h), HostCall.contextTyped_deepAll h⟩

/-! ## The interpreter's exactness under `StoreTy` -/

theorem refOk?_complete' {s : Store H} {r : Ref} {rt : CRefType} (hs : StoreTy s)
    (hrt : TyOk {} rt) : RefOk s r rt → refOk? s r rt = true := by
  intro h
  induction r generalizing rt with
  | extern r' ih =>
    obtain ⟨rt₀, e, hsub, hx⟩ := (RefOk.iff_principal s _ rt hrt).mp h
    obtain ⟨hr', hn⟩ := hx r' rfl
    unfold refOk?
    simp only [e, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨(Sub.check_iff TypeCtx.ok_empty rfl (hs _ _ e) hrt).mpr hsub,
      ih Ref.tyOk_any hr', hn⟩
  | _ =>
    obtain ⟨rt₀, e, hsub, -⟩ := (RefOk.iff_principal s _ rt hrt).mp h
    unfold refOk?
    simp only [e, Bool.and_true]
    exact (Sub.check_iff TypeCtx.ok_empty rfl (hs _ _ e) hrt).mpr hsub

theorem refOk?_iff' {s : Store H} (hs : StoreTy s) :
    ∀ r rt, TyOk {} rt → (refOk? s r rt = true ↔ RefOk s r rt) :=
  fun _ _ hrt => ⟨refOk?_sound hrt, refOk?_complete' hs hrt⟩

theorem referenceStep?_complete' {o : GrowOracle} {s : Store H} {f : Frame} {vs args : List Val}
    {e : Admin} {c : Config H} (hs : StoreTy s)
    (hcast : ∀ rt, (e = .plain (.refTest rt) ∨ e = .plain (.refCast rt)) →
      TyOk {} (f.module.instRef rt)) :
    Head (profile o) s f args e c → famOf e = .reference → (∃ q, vs = q ++ args) →
      referenceStep? o s f vs e = some (args.length, c) := by
  intro h hf ⟨q, hq⟩
  have h' := h.fam_inv (by rw [hf]; decide)
  rw [hf] at h'
  simp only [FamRel] at h'
  subst hq
  unfold referenceStep?
  rw [List.reverse_append]
  generalize hl : vals args ++ [e] = l at h'
  cases h' <;> first
    | obtain ⟨rfl, rfl⟩ := Ref.snoc_eq (l := []) hl
    | obtain ⟨rfl, rfl⟩ := Ref.snoc_eq (l := [.ref _]) hl
    | obtain ⟨rfl, rfl⟩ := Ref.snoc_eq (l := [.num ⟨.int .i32, _⟩]) hl
    | obtain ⟨rfl, rfl⟩ := Ref.snoc_eq (l := [.ref _, .ref _]) hl
  all_goals first
    | (simp [refStepRev?, *]; done)
    | simp [refStepRev?, refOk?_complete' hs (hcast _ (.inl rfl)) ‹_›]
    | simp [refStepRev?, refOk?_complete' hs (hcast _ (.inr rfl)) ‹_›]
    | simp [refStepRev?, Bool.eq_false_iff.mpr (fun h => ‹¬_› (refOk?_sound (hcast _ (.inl rfl)) h))]
    | simp [refStepRev?, Bool.eq_false_iff.mpr (fun h => ‹¬_› (refOk?_sound (hcast _ (.inr rfl)) h))]
    | rfl

theorem interpHead_exact' {o : GrowOracle} {s : Store H} (hs : StoreTy s) :
    ∀ f vs args e c, IHeadInv f e → Head (profile o) s f args e c → (∃ q, vs = q ++ args) →
      interpHead o s f vs e = some (args.length, c) ∨
        (interpHead o s f vs e = none ∧ IsCtxtHead (profile o) s f e c) := by
  intro f vs args e c hinv h hq
  unfold interpHead
  split
  all_goals rename_i hf
  · exact .inl (parametricStep?_complete h hf hq)
  · exact .inl (numericStep?_complete h hf hq)
  · exact .inl (vectorStep?_complete h hf hq)
  · exact .inl (variableStep?_complete h hf hq)
  · exact .inl (tableStep?_complete h hf hq)
  · exact .inl (memoryStep?_complete h hf hq)
  · exact .inl (referenceStep?_complete' hs hinv.1 h hf hq)
  · left
    by_cases hi : AggNewInstr e
    · exact orElse_of_some (aggNewStep?_complete h hi hq)
    · rw [orElse_of_none (aggNewStep?_none hi)]
      exact aggAccessStep?_complete h (aggAccessInstr_of hf hi) hq
  · by_cases hn : Adm.IsNest e
    · rw [orElse_of_none (controlStep?_nest hn)]
      cases ha : adminStep? o s f vs e with
      | none =>
        refine .inr ⟨rfl, ?_⟩
        rcases adminStep?_none ha h with h' | h' | h' | h'
        · exact .inl h'
        · exact .inr (.inl h')
        · exact .inr (.inr h')
        · exact absurd hn h'
      | some p =>
        obtain ⟨k, c'⟩ := p
        obtain ⟨rfl, rfl⟩ := Adm.adminStep?_exact ha h
        exact .inl rfl
    · left
      exact orElse_of_some (controlStep?_complete (refOk?_iff' hs) hinv.2 h hf
        (by rintro n cont is rfl; exact hn trivial)
        (by rintro n cs is rfl; exact hn trivial)
        (by rintro n fi is rfl; exact hn trivial) hq)

theorem interpHead_complete' {o : GrowOracle} {s : Store H} (hs : StoreTy s) :
    ∀ f vs args e c, IHeadInv f e → Head (profile o) s f args e c → (∃ q, vs = q ++ args) →
      interpHead o s f vs e = none → IsCtxtHead (profile o) s f e c := by
  intro f vs args e c hi hH hq hn
  rcases interpHead_exact' hs f vs args e c hi hH hq with h | ⟨-, h⟩
  · rw [h] at hn; cases hn
  · exact h

/-! ## Divergence passes through host-free steps -/

section Through

variable {o : GrowOracle} {host : HostSemantics H} {I : Config H → Prop}

theorem through_aux_of (hI : ∀ c, I c → StoreTy c.store ∧ DeepAll IHeadInv c.frame c.code)
    (hstep : ∀ c c', I c → Det.DStep o c c' → I c') :
    ∀ (n : Nat) (K : Config H), sizeOf K.code = n → I K →
      Diverges (profile o) host K → ∀ d, Det.DStep o K d →
        ∃ d', Step (profile o) host d d' ∧ (Diverges (profile o) host d' ∨
          ∃ K', I K' ∧ Diverges (profile o) host K' ∧ Det.DStep o K' d') := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K hn ht hK d hd
  obtain ⟨b, hb, hdb⟩ := hK.unfold
  have hb' := HostCall.dstep_of_step hd hb
  obtain ⟨hs, hi⟩ := hI K ht
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp
    (step?_complete (interpHead_complete' hs) rfl hi hd : (stepI o K).isSome)
  have hlb := Silmaril.Wasm.Interp.step?_lag_at (interpHead_exact' hs) _ K b x rfl rfl hi hb' hx
  have htb : I b := hstep K b ht hb'
  rcases step?_maximal_at (interpHead_exact' hs) _ K d x rfl rfl hi hd hx with _ | hdx
  · rcases step?_maximal_at (interpHead_exact' hs) _ K b _ rfl rfl hi hb' hx with _ | hbx
    · obtain ⟨d', h', hd'⟩ := hdb.unfold
      exact ⟨d', h', .inl hd'⟩
    · rcases hlb with rfl | ⟨hlt, -⟩
      · obtain ⟨d', h', hd'⟩ := hdb.unfold
        exact ⟨d', h', .inl hd'⟩
      · exact ih _ (hn ▸ hlt) b rfl htb hdb _ hbx
  · refine ⟨x, Step.of_noHost host hdx, ?_⟩
    rcases step?_maximal_at (interpHead_exact' hs) _ K b x rfl rfl hi hb' hx with _ | hbx
    · exact .inl hdb
    · exact .inr ⟨b, htb, hdb, hbx⟩

/-- **A divergent run passes through every host-free step** of a configuration in an invariant
kept by host-free steps, whose stores have closed-valid principal types and whose code meets the
cast side conditions (deterministic profile). -/
theorem diverges_through_of (hI : ∀ c, I c → StoreTy c.store ∧ DeepAll IHeadInv c.frame c.code)
    (hstep : ∀ c c', I c → Det.DStep o c c' → I c') {K d : Config H} (ht : I K)
    (hK : Diverges (profile o) host K) (hd : Det.DStep o K d) : Diverges (profile o) host d := by
  refine Silmaril.InfiniteTrace.coinduct (fun d => Diverges (profile o) host d ∨
    ∃ K', I K' ∧ Diverges (profile o) host K' ∧ Det.DStep o K' d) ?_ (.inr ⟨K, ht, hK, hd⟩)
  rintro c (hc | ⟨K, ht, hK, hd⟩)
  · obtain ⟨d', h', hd'⟩ := hc.unfold
    exact ⟨d', h', .inl hd'⟩
  · exact through_aux_of hI hstep _ K rfl ht hK c hd

end Through

end Silmaril.Proofs.Wasm.Abstract.BackInv
