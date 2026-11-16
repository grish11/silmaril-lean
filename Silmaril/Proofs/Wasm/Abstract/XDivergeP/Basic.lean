module

public import Silmaril.Wasm.Abstract.XDivergeP.Defs

/-!
Proofs for `Silmaril.Wasm.Abstract.XDivergeP.Thms`: unfolding of the two divergences, their joint
coinduction principle, and the frame-level reading of `FunDivXP`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.XDivergeP

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Interp (Problem)
open Silmaril.Wasm.Abstract.CallXP Silmaril.Wasm.Abstract.XRecursionP
open Silmaril.Wasm.Abstract.XDivergeP

variable {H : Type}

theorem gfp_unfold : divOpXP ((divOpXP (H := H)).gfp) = (divOpXP (H := H)).gfp :=
  (divOpXP (H := H)).map_gfp

theorem evalDivXP_unfold {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr} :
    EvalDivXP s f stk es ↔ DivStepXP EvalDivXP FunDivXP s f stk es := by
  have h := congrArg Prod.fst (gfp_unfold (H := H))
  exact (Eq.to_iff (congrFun (congrFun (congrFun (congrFun h s) f) stk) es)).symm

theorem funDivXP_unfold {s : Store H} {a : Nat} {vs : List Val} :
    FunDivXP s a vs ↔ CallStepXP EvalDivXP FunDivXP s a vs := by
  have h := congrArg Prod.snd (gfp_unfold (H := H))
  exact (Eq.to_iff (congrFun (congrFun (congrFun h s) a) vs)).symm

theorem coind {X : Problem H} {Y : CallProblem H}
    (hX : ∀ s f stk es, X s f stk es → DivStepXP X Y s f stk es)
    (hY : ∀ s a vs, Y s a vs → CallStepXP X Y s a vs) : X ≤ EvalDivXP ∧ Y ≤ FunDivXP := by
  have h : (X, Y) ≤ (divOpXP (H := H)).gfp :=
    (divOpXP (H := H)).le_gfp ⟨fun s f stk es hx => hX s f stk es hx, fun s a vs hy => hY s a vs hy⟩
  exact ⟨h.1, h.2⟩

theorem funDivXP_iff {s : Store H} {a : Nat} {vs : List Val} :
    FunDivXP s a vs ↔ ∃ (fi : FuncInst H) (fn : Func), s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧
      (EvalDivXP s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body) ∨
        ∃ (s₁ : Store H) (f₂ : Frame) (a' : Nat) (args' : List Val) (n : Nat),
          EvalOXP closedCallXP s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body)
            (s₁, f₂, .tail a' args' n) ∧ FunDivXP s₁ a' args') := by
  rw [funDivXP_unfold]
  constructor
  · rintro (⟨hfi, hcode, h⟩ | ⟨hfi, hcode, hbody, h⟩)
    · exact ⟨_, _, hfi, hcode, .inl h⟩
    · exact ⟨_, _, hfi, hcode, .inr ⟨_, _, _, _, _, hbody, h⟩⟩
  · rintro ⟨fi, fn, hfi, hcode, h | ⟨s₁, f₂, a', args', n, hbody, h⟩⟩
    · exact .body hfi hcode h
    · exact .frameTail hfi hcode hbody h

end Silmaril.Proofs.Wasm.Abstract.XDivergeP
