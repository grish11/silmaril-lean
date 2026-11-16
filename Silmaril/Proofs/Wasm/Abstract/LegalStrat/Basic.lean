module

public import Silmaril.Wasm.Abstract.LegalStrat.Defs
public import Silmaril.Wasm.Abstract.FunctorP.Thms
public import Silmaril.Wasm.Abstract.LegalFunctor.Thms
public import Silmaril.Proofs.Wasm.Abstract.LegalStrat.Restrict

/-!
# Wasm legality and the legal operational equivalence (proofs)

* `legal_iff`: #623's `Legal Γ C` is "every answer of `C` is a `LegalAns`";
* `lObs_denL_iff`: for `denL`, agreement at `wasmL`-legal logs (`Restrict.LObs`) is `OpEquivPL`,
  read through `FunctorP.evalLXP_iff`, `evalLXP_trap_iff` and `reachXP_iff_pend` at the universal
  oracle; a finished path never ends in a non-trap result carrying a trap flow
  (`not_path_ok_trap`, from `ExposeP.path_evalOXP`);
* `opEquivL_of_opEquivPL`: answered runs under a legal oracle are logged runs with legal logs;
* `evalLXP_lands_legal`: a legally answered logged fallthrough of typed code lands in the world.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.LegalStrat

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (CallRel)
open Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
open Silmaril.Wasm.Abstract.ExposeP Silmaril.Wasm.Abstract.ExposePStruct
open Silmaril.Wasm.Abstract.ExposePTyped Silmaril.Wasm.Abstract.TypedCat
open Silmaril.Wasm.Abstract.WorldFunctor Silmaril.Wasm.Abstract.LegalFunctor
open Silmaril.Wasm.Abstract.CallXP (POut EvalOXP)
open Silmaril.Wasm.Abstract.FunctorP
open Silmaril.Wasm.Abstract.LegalStrat
open Silmaril.Wasm.Abstract.BodyTrace (Path Pend liftSig)
open Silmaril.Wasm.Abstract.BodyStrat (toTriple)

variable {H : Type}

/-! ## Legal oracles and legal logs -/

theorem legal_iff {Γ : Ctx H} {C : CallRel H} :
    Legal Γ C ↔ ∀ s a args ans, C s a args ans → LegalAns Γ s a args ans :=
  ⟨fun h s a args ans hC hfit hg => h s ans.1 a args ans.2 ⟨hC, hfit⟩ hg,
    fun h s s₂ a args fl hC hg => h s a args (s₂, fl) hC.1 hC.2 hg⟩

theorem legal_legalC (Γ : Ctx H) : Legal Γ (legalC Γ) := legal_iff.2 fun _ _ _ _ h => h

theorem legalLog_of {Γ : Ctx H} {C : CallRel H} (hC : Legal Γ C) {cs : List (ACall H)}
    (hA : Answered C cs) : LegalLog Γ cs :=
  fun c hc => legal_iff.1 hC c.1.2.2 c.1.1 c.1.2.1 c.2 (hA c hc)

/-! ## Logged observations at legal logs -/

/-- The universal oracle. -/
def topRel : CallRel H := fun _ _ _ _ => True

theorem answered_top (cs : List (ACall H)) : Answered (topRel (H := H)) cs := fun _ _ => trivial

/-- A finished path of the exposed body never ends in a non-trap result with a trap flow: a trap
is the trap effect. -/
theorem not_path_ok_trap {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {cs : List (ACall H)} {f' : Frame} {s' : Store H} :
    ¬ Path (((denListXP es f stk : M (CallSig H) H ResP).run ⟨s⟩).run) cs
      (.val (.ok (⟨(f', .flow .trap)⟩, ⟨s'⟩))) := by
  intro hp
  obtain ⟨⟨s₁, f₁, o₁⟩, -, hr⟩ :=
    path_evalOXP (C := topRel) (answered_top cs) hp (fun h => by cases h)
  cases o₁ with
  | flow fl => cases fl <;> simp_all [endRP]
  | tail => simp_all [endRP]

/-- **For code, agreement at legal logs is the legal operational equivalence.** -/
theorem lObs_denL_iff (Γ : Ctx H) (es es' : List BExpr) :
    LObs (wasmL Γ) (denL (H := H) es) (denL es') ↔ OpEquivPL Γ es es' := by
  constructor
  · intro h C s f stk cs hcs
    obtain ⟨h₁, h₂, h₃⟩ := h ⟨s⟩ ⟨(f, stk)⟩ cs hcs
    refine ⟨fun s' f' o ho => ?_, ?_, fun y => ?_⟩
    · rw [evalLXP_iff ho, evalLXP_iff ho]
      exact and_congr_right fun _ => h₁ ⟨(f', o)⟩ ⟨s'⟩
    · rw [evalLXP_trap_iff, evalLXP_trap_iff]
      refine and_congr_right fun _ => ⟨fun hp => ?_, fun hp => ?_⟩
      · obtain ⟨⟨⟩, hp'⟩ := h₂.1 ⟨_, hp⟩
        exact hp'
      · obtain ⟨⟨⟩, hp'⟩ := h₂.2 ⟨_, hp⟩
        exact hp'
    · rw [reachXP_iff_pend, reachXP_iff_pend]
      exact and_congr_right fun _ => h₃ y
  · intro h
    rintro ⟨s⟩ ⟨⟨f, stk⟩⟩ cs hcs
    obtain ⟨h₁, h₂, h₃⟩ := h topRel s f stk cs hcs
    refine ⟨?_, ?_, fun y => ?_⟩
    · rintro ⟨⟨f', o⟩⟩ ⟨s'⟩
      by_cases ho : o = .flow .trap
      · subst ho
        exact ⟨fun hp => absurd hp (not_path_ok_trap (es := es) (f := f) (stk := stk)),
          fun hp => absurd hp (not_path_ok_trap (es := es') (f := f) (stk := stk))⟩
      · exact ⟨fun hp => ((evalLXP_iff ho).1
            ((h₁ s' f' o ho).1 ((evalLXP_iff ho).2 ⟨answered_top cs, hp⟩))).2,
          fun hp => ((evalLXP_iff ho).1
            ((h₁ s' f' o ho).2 ((evalLXP_iff ho).2 ⟨answered_top cs, hp⟩))).2⟩
    · refine ⟨fun ⟨⟨⟩, hp⟩ => ⟨⟨⟩, ?_⟩, fun ⟨⟨⟩, hp⟩ => ⟨⟨⟩, ?_⟩⟩
      · exact (evalLXP_trap_iff.1 (h₂.1 (evalLXP_trap_iff.2 ⟨answered_top cs, hp⟩))).2
      · exact (evalLXP_trap_iff.1 (h₂.2 (evalLXP_trap_iff.2 ⟨answered_top cs, hp⟩))).2
    · exact ⟨fun hp => (reachXP_iff_pend.1 ((h₃ y).1 (reachXP_iff_pend.2 ⟨answered_top cs, hp⟩))).2,
        fun hp => (reachXP_iff_pend.1 ((h₃ y).2 (reachXP_iff_pend.2 ⟨answered_top cs, hp⟩))).2⟩

/-- **For code, equal restricted triples is the legal operational equivalence.** -/
theorem restrict_denL_iff (Γ : Ctx H) (es es' : List BExpr) :
    StratLegal.restrict (wasmL Γ) (toTriple (denL (H := H) es)) =
        StratLegal.restrict (wasmL Γ) (toTriple (denL es')) ↔ OpEquivPL Γ es es' :=
  (restrict_eq_iff _ _ _).trans (lObs_denL_iff Γ es es')

/-! ## Links -/

/-- **Legal-play equality determines the answered runs under legal oracles.** -/
theorem opEquivL_of_opEquivPL {Γ : Ctx H} (I : TIface) {es es' : List BExpr}
    (h : OpEquivPL Γ es es') : OpEquivL Γ I es es' := by
  intro C hC s f stk _
  refine ⟨fun s' f' o ho => ?_, ?_⟩
  · rw [evalOXP_iff_log ho, evalOXP_iff_log ho]
    refine ⟨fun ⟨cs, hd⟩ => ⟨cs, ?_⟩, fun ⟨cs, hd⟩ => ⟨cs, ?_⟩⟩
    · exact ((h C s f stk cs (legalLog_of hC ((evalLXP_iff ho).1 hd).1)).1 s' f' o ho).1 hd
    · exact ((h C s f stk cs (legalLog_of hC ((evalLXP_iff ho).1 hd).1)).1 s' f' o ho).2 hd
  · rw [evalOXP_trap_iff_log, evalOXP_trap_iff_log]
    refine ⟨fun ⟨cs, s', f', hd⟩ => ?_, fun ⟨cs, s', f', hd⟩ => ?_⟩
    · obtain ⟨s'', f'', hd'⟩ := (h C s f stk cs
        (legalLog_of hC (evalLXP_trap_iff.1 ⟨s', f', hd⟩).1)).2.1.1 ⟨s', f', hd⟩
      exact ⟨cs, s'', f'', hd'⟩
    · obtain ⟨s'', f'', hd'⟩ := (h C s f stk cs
        (legalLog_of hC (evalLXP_trap_iff.1 ⟨s', f', hd⟩).1)).2.1.2 ⟨s', f', hd⟩
      exact ⟨cs, s'', f'', hd'⟩

/-- **Legally answered logged fallthroughs of typed code land in the world.** -/
theorem evalLXP_lands_legal {Γ : Ctx H} {I J : TIface} {es : List BExpr} (hm : THom Γ I J es)
    {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val} (hw : WSt Γ I s f stk)
    {cs : List (ACall H)} (hcs : LegalLog Γ cs) {s' : Store H} {f' : Frame} {vs : List Val}
    (d : EvalLXP C s f stk es cs (s', f', .flow (.normal vs))) : WSt Γ J s' f' vs := by
  have ho : (POut.flow (.normal vs)) ≠ .flow .trap := fun h => by cases h
  have d' : EvalLXP (legalC Γ) s f stk es cs (s', f', .flow (.normal vs)) :=
    (evalLXP_iff ho).2 ⟨fun c hc => hcs c hc, ((evalLXP_iff ho).1 d).2⟩
  exact thom_lands_legal (legal_legalC Γ) hm hw ((evalOXP_iff_log ho).2 ⟨cs, d'⟩)

end Silmaril.Proofs.Wasm.Abstract.LegalStrat
