module

public import Silmaril.Proofs.Games.Abstract.FullFun.Tensor
import Silmaril.Games.Abstract.FunctionIter.Thms

/-!
# Uniformity of iteration fails along effectful maps (proofs)

Uniformity holds along pure maps (`iter_uniform`). Along a map `h` with an effect it fails, even
when `h` is total and deterministic. Take `G = pure.map inr`, the body that continues silently
forever, so that `iter G` is silent divergence `([], div)`:

* `not_iter_uniform_call`: `h` makes one import call and returns. With `F = G`, both
  `h ; F` and `G ; [inl, inr ∘ h]` make the call and continue, but `h ; iter F` makes the call
  before diverging, `([true], div)`. The two differ in their call logs, so they differ also with
  trap and divergence merged;
* `not_iter_uniform_trap`: `h` always traps (it is strict: it diverges after a divergence). Both
  sides of the hypothesis trap, but `h ; iter F` traps while `iter G` diverges.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.FullFun

open Silmaril.Games Silmaril.Games.Abstract

/-- The body that continues silently with its argument. -/
abbrev contBody : FullFun boolSig PUnit PUnit (PUnit ⊕ PUnit) := FullFun.pure.map Sum.inr

theorem iter_contBody_fin : (FullFun.iter contBody).1 ⟨⟩ ⟨⟩ = {([], End.div)} :=
  AFun.iter_continue (fun s a => pure_map_fst Sum.inr s a) _ _

/-- **Uniformity fails along a map that makes an import call.** -/
theorem not_iter_uniform_call :
    FullFun.seq (callOnce true) contBody =
        FullFun.seq contBody (FullFun.case (FullFun.pure.map Sum.inl) ((callOnce true).map Sum.inr)) ∧
      FullFun.seq (callOnce true) (FullFun.iter contBody) ≠ FullFun.iter contBody := by
  refine ⟨by rw [seq_pure_map, pure_map_seq]; rfl, fun heq => ?_⟩
  have hd : ([], End.div) ∈ (FullFun.iter contBody).1 ⟨⟩ ⟨⟩ := by
    rw [iter_contBody_fin]; rfl
  have hm : ([⟨true, ⟨⟩⟩], End.div) ∈
      (FullFun.seq (callOnce true) (FullFun.iter contBody)).1 ⟨⟩ ⟨⟩ :=
    .inr (.inr ⟨[⟨true, ⟨⟩⟩], ⟨⟩, ⟨⟩, [], .div, rfl, hd, rfl⟩)
  rw [heq, iter_contBody_fin] at hm
  cases (Prod.mk.inj hm).1

/-- Always trap. -/
def trapFun : FullFun boolSig PUnit PUnit PUnit := (fun _ _ => {([], End.trap)}, fun _ _ => ∅)

/-- **Uniformity fails along a map that traps.** -/
theorem not_iter_uniform_trap :
    FullFun.seq trapFun contBody =
        FullFun.seq contBody (FullFun.case (FullFun.pure.map Sum.inl) (trapFun.map Sum.inr)) ∧
      FullFun.seq trapFun (FullFun.iter contBody) ≠ FullFun.iter contBody := by
  refine ⟨?_, fun heq => ?_⟩
  · rw [pure_map_seq]
    refine Prod.ext (funext fun _ => funext fun _ => Set.ext fun x => ?_)
      (funext fun _ => funext fun _ => Set.ext fun ω => ?_)
    · constructor
      · rintro (⟨c, hc, rfl⟩ | ⟨c, hc, -⟩ | ⟨c₁, b, s₁, c₂, e, hc, -, -⟩)
        · obtain ⟨rfl, -⟩ := Prod.mk.inj hc
          exact ⟨([], .trap), rfl, rfl⟩
        · cases (Prod.mk.inj hc).2
        · cases (Prod.mk.inj hc).2
      · rintro ⟨y, rfl, rfl⟩
        exact .inl ⟨[], rfl, rfl⟩
    · constructor
      · rintro (h | ⟨c, b, s₁, ω', hc, -, -⟩)
        · exact h.elim
        · cases (Prod.mk.inj hc).2
      · intro h
        exact h.elim
  · have hm : ([], End.trap) ∈ (FullFun.seq trapFun (FullFun.iter contBody)).1 ⟨⟩ ⟨⟩ :=
      .inl ⟨[], rfl, rfl⟩
    rw [heq, iter_contBody_fin] at hm
    cases (Prod.mk.inj hm).2

end Silmaril.Proofs.Games.Abstract.FullFun
