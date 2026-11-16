module

public import Silmaril.Proofs.Wasm.Abstract.StoreBody.Complete

/-! Proofs for `Silmaril.Wasm.Abstract.StoreBody.Thms`: invocations. -/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.StoreBody

open Silmaril.Wasm Silmaril.Games Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Binaryen
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract.StoreBody Silmaril.Elgot.ITree

variable {E : Sig.{0}} {H : Type}

theorem run_denInvoke (a : Nat) (vs : List Val) (s : Store H) :
    run' (denInvoke a vs : M E H _) ⟨s⟩ =
      run' (match s.funcs[a]? with
        | some fi =>
          match fi.code, Validation.DefType.funcType? fi.type with
          | .wasm fn, some (_, rs) =>
            denList (liftInstrs fn.body) (Frame.forCall fi.module vs fn.locals) [] >>=
              invokeK rs.length
          | _, _ => stuck
        | none => stuck : M E H _) ⟨s⟩ := by
  simp only [denInvoke, getState, run', StateT.run_bind, StateT.run_get, ExceptT.run_bind,
    ExceptT.run_pure]
  exact pure_bind _ _

/-- The call outcome after a body outcome, as `invokeRun` computes it. -/
def invokeOut (nr : Nat) : Store H × Frame × Flow → Option (Store H × Flow)
  | (s', _, .normal ws) | (s', _, .ret ws) | (s', _, .brk 0 ws) =>
      some (s', .normal (ws.take nr).reverse)
  | (s', _, .trap) => some (s', .trap)
  | (s', _, .throw x) => some (s', .throw x)
  | _ => none

theorem invokeK_eval {nr : Nat} {y : M E H Res} {s : St H} {r : Store H × Frame × Flow}
    (hy : run' y s = evalTree (some r)) :
    run' (y >>= invokeK nr) s = invTree (invokeOut nr r) := by
  rw [run_bind_eval hy]
  obtain ⟨s', f', fl⟩ := r
  cases fl with
  | brk k ws => cases k <;> rfl
  | _ => rfl

theorem invokeRun_of {fuel : Nat} {s : Store H} {a : Nat} {vs : List Val} {fi : FuncInst H}
    {fn : Func} {ps rs : List Validation.CValType} (hf : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm fn) (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
    invokeRun fuel s a vs =
      (run fuel s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body)).bind
        (invokeOut rs.length) := by
  simp only [invokeRun, hf, hcode, hty]
  rcases run fuel s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body) with
    _ | ⟨s', f', fl⟩
  · rfl
  · cases fl with
    | brk k ws => cases k <;> rfl
    | _ => rfl

theorem invokeRun_none {fuel : Nat} {s : Store H} {a : Nat} {vs : List Val}
    (h : ∀ fi fn ps rs, s.funcs[a]? = some fi → fi.code = .wasm fn →
      Validation.DefType.funcType? fi.type = some (ps, rs) → False) :
    invokeRun fuel s a vs = none := by
  unfold invokeRun
  split
  · rename_i fi hf
    split
    · rename_i fn ps rs hcode hty
      exact (h fi fn ps rs hf hcode hty).elim
    · rfl
  · rfl

/-- **Invocation, both ways.** For a call-free function, the abstract invocation
diverges exactly when `invokeRun` has no result at any fuel, and otherwise
computes `invokeRun`'s result. -/
theorem invoke_exact {s : Store H} {a : Nat} {vs : List Val} (hc : CallFreeAt s a) :
    (∀ fuel r, invokeRun fuel s a vs = some r →
      run' (denInvoke a vs : M E H _) ⟨s⟩ = invTree (some r)) ∧
    (run' (denInvoke a vs : M E H _) ⟨s⟩ = diverge ∨
      ∃ fuel r, invokeRun fuel s a vs = some r ∧
        run' (denInvoke a vs : M E H _) ⟨s⟩ = invTree (some r)) := by
  rw [run_denInvoke]
  cases hf : s.funcs[a]? with
  | none =>
    refine ⟨fun fuel r h => ?_, .inl rfl⟩
    rw [invokeRun_none (fun _ _ _ _ h' => by rw [hf] at h'; cases h')] at h; cases h
  | some fi =>
    simp only
    cases hcode : fi.code with
    | host h =>
      refine ⟨fun fuel r h => ?_, .inl rfl⟩
      rw [invokeRun_none (fun _ _ _ _ h' hc' _ => by
        rw [hf] at h'; cases h'; rw [hcode] at hc'; cases hc')] at h; cases h
    | wasm fn =>
      cases hty : Validation.DefType.funcType? fi.type with
      | none =>
        refine ⟨fun fuel r h => ?_, .inl rfl⟩
        rw [invokeRun_none (fun _ _ _ _ h' _ ht' => by
          rw [hf] at h'; cases h'; rw [hty] at ht'; cases ht')] at h; cases h
      | some p =>
        obtain ⟨ps, rs⟩ := p
        simp only
        have hcf := hc fi fn hf hcode
        refine ⟨fun fuel r h => ?_, ?_⟩
        · rw [invokeRun_of hf hcode hty] at h
          cases hr : run fuel s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body) with
          | none => rw [hr] at h; cases h
          | some r₁ =>
            rw [hr, Option.bind_some] at h
            rw [invokeK_eval (run_sound fuel hcf hr), h]
        · rcases list_good (E := E) _ hcf s (Frame.forCall fi.module vs fn.locals) [] with
            hd | ⟨r₁, hev, hy⟩
          · exact .inl (run_bind_diverge hd)
          · obtain ⟨fuel, hfuel⟩ := run_of_eval hev
            cases ho : invokeOut rs.length r₁ with
            | none =>
              left
              rw [invokeK_eval hy, ho]; rfl
            | some r =>
              right
              refine ⟨fuel, r, ?_, by rw [invokeK_eval hy, ho]⟩
              rw [invokeRun_of hf hcode hty, hfuel, Option.bind_some, ho]

end Silmaril.Proofs.Wasm.Abstract.StoreBody
