module

public import Silmaril.Proofs.Wasm.Cfg.Region

@[expose] public section

/-!
# Region runs with a call oracle: generic helper lemmas

`C`-generic versions of the `Region.Run` helpers (`Proofs/Wasm/Cfg/Region.lean`, which are
stated for `noCall`): value pushing, its inversion, and sequencing. The only new case in each
is `RunC.call` (a call answered by the oracle continues; a trapping or throwing one ends). The
`noCall` lemmas are unchanged.
-/

namespace Silmaril.Wasm.Cfg.Proofs.RegionC

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H}

/-- Values push. -/
theorem run_valsC {s s' : Store H} {f f' : Frame} {vs : List Val} :
    ∀ {ws : List Val} {code : List Admin} {o : Out},
      RunC P host C s f (vs ++ ws) code s' f' o → RunC P host C s f vs (vals ws ++ code) s' f' o
  | [], _, _, h => by simpa [vals] using h
  | w :: ws, code, o, h => by
    simp only [vals, List.map_cons, List.cons_append]
    exact .val (Admin.val?_toAdmin w) (run_valsC (vs := vs ++ [w]) (by simpa using h))

theorem run_val_invC {s s' : Store H} {f f' : Frame} {vs : List Val} {a : Admin} {v : Val}
    {code : List Admin} {o : Out} (hv : a.val? = some v)
    (h : RunC P host C s f vs (a :: code) s' f' o) :
    RunC P host C s f (vs ++ [v]) code s' f' o := by
  cases h with
  | val hv' h => rw [hv] at hv'; cases hv'; exact h
  | simple hi => exact absurd (Proofs.Region.famOf_val hv) hi
  | simpleTrap hi => exact absurd (Proofs.Region.famOf_val hv) hi
  | brData hb => cases hb <;> simp [Admin.val?] at hv
  | _ => simp [Admin.val?] at hv

theorem run_vals_invC {s s' : Store H} {f f' : Frame} {vs : List Val} :
    ∀ {ws : List Val} {code : List Admin} {o : Out},
      RunC P host C s f vs (vals ws ++ code) s' f' o → RunC P host C s f (vs ++ ws) code s' f' o
  | [], _, _, h => by simpa [vals] using h
  | w :: ws, code, o, h => by
    simp only [vals, List.map_cons, List.cons_append] at h
    have := run_vals_invC (vs := vs ++ [w]) (run_val_invC (Admin.val?_toAdmin w) h)
    simpa using this

/-- Sequencing with an oracle: after a first part ends with outcome `o₁`, the second part runs
on fall-through; any other outcome skips it. -/
def ThenC (P : Profile) (host : HostSemantics H) (C : Abstract.CallRel H) (s₁ : Store H)
    (f₁ : Frame) : Out → List Admin → Store H → Frame → Out → Prop
  | .normal us, B, s', f', o => RunC P host C s₁ f₁ us B s' f' o
  | o₁, _, s', f', o => o = o₁ ∧ s' = s₁ ∧ f' = f₁

theorem run_appendC {s s₁ s' : Store H} {f f₁ f' : Frame} {vs : List Val} {A B : List Admin}
    {o₁ o : Out} (h : RunC P host C s f vs A s₁ f₁ o₁) (hB : ThenC P host C s₁ f₁ o₁ B s' f' o) :
    RunC P host C s f vs (A ++ B) s' f' o := by
  induction h with
  | call hfi hty hn hcall hvs _ ih => exact .call hfi hty hn hcall hvs (ih hB)
  | callTrap hfi hty hn hcall => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .callTrap hfi hty hn hcall
  | callThrow hfi hty hn hcall => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .callThrow hfi hty hn hcall
  | nil => exact hB
  | val hv _ ih => exact .val hv (ih hB)
  | simple hi h₁ _ ih => exact .simple hi h₁ (ih hB)
  | simpleTrap hi h₁ => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .simpleTrap hi h₁
  | trap => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .trap
  | br => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .br
  | ret => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .ret
  | brIf _ ih => exact .brIf (by simpa using ih hB)
  | brData hb _ ih => exact .brData hb (by simpa using ih hB)
  | block hbt hm _ ih => exact .block hbt hm (ih hB)
  | loop hbt hm _ ih => exact .loop hbt hm (ih hB)
  | if_ _ ih => exact .if_ (ih hB)
  | labelNormal hin _ _ ih => exact .labelNormal hin (ih hB)
  | labelBr0 hin hn _ _ ih => exact .labelBr0 hin hn (by simpa using ih hB)
  | labelBrSucc hin => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .labelBrSucc hin
  | labelRet hin => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .labelRet hin
  | labelTrap hin => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .labelTrap hin
  | throw ht he hn => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .throw ht he hn
  | throwRefNull => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .throwRefNull
  | throwRefExn => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .throwRefExn
  | tryTable hbt hm _ ih => exact .tryTable hbt hm (ih hB)
  | labelThrow hin => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .labelThrow hin
  | handlerNormal hin _ _ ih => exact .handlerNormal hin (ih hB)
  | handlerBr hin => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .handlerBr hin
  | handlerRet hin => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .handlerRet hin
  | handlerTrap hin => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .handlerTrap hin
  | handlerCatch hin hc => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .handlerCatch hin hc
  | handlerRethrow hin hc => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .handlerRethrow hin hc

/-- With no oracle, sequencing is the region semantics' `Then`. -/
theorem thenC_noCall {s₁ s' : Store H} {f₁ f' : Frame} {o₁ o : Out} {B : List Admin} :
    ThenC P host noCall s₁ f₁ o₁ B s' f' o ↔ Then P host s₁ f₁ o₁ B s' f' o := by
  cases o₁ <;> rfl


theorem label_backC {s s₁ s' : Store H} {f f₁ f' : Frame} {vs : List Val} {n : Nat}
    {cont : List Instr} {inner inner' code : List Admin} {o : Out}
    (hb : ∀ {o₁ : Out} {s₂ : Store H} {f₂ : Frame},
      RunC P host C s₁ f₁ [] inner' s₂ f₂ o₁ → RunC P host C s f [] inner s₂ f₂ o₁)
    (h : RunC P host C s₁ f₁ vs (.label n cont inner' :: code) s' f' o) :
    RunC P host C s f vs (.label n cont inner :: code) s' f' o := by
  cases h with
  | val hv => simp [Admin.val?] at hv
  | labelNormal hin h => exact .labelNormal (hb hin) h
  | labelBr0 hin hn h => exact .labelBr0 (hb hin) hn h
  | labelBrSucc hin => exact .labelBrSucc (hb hin)
  | labelRet hin => exact .labelRet (hb hin)
  | labelTrap hin => exact .labelTrap (hb hin)
  | labelThrow hin => exact .labelThrow (hb hin)

theorem handler_backC {s s₁ s' : Store H} {f f₁ f' : Frame} {vs : List Val} {n : Nat}
    {cs : List Catch} {inner inner' code : List Admin} {o : Out}
    (hb : ∀ {o₁ : Out} {s₂ : Store H} {f₂ : Frame},
      RunC P host C s₁ f₁ [] inner' s₂ f₂ o₁ → RunC P host C s f [] inner s₂ f₂ o₁)
    (h : RunC P host C s₁ f₁ vs (.handler n cs inner' :: code) s' f' o) :
    RunC P host C s f vs (.handler n cs inner :: code) s' f' o := by
  cases h with
  | val hv => simp [Admin.val?] at hv
  | handlerNormal hin h => exact .handlerNormal (hb hin) h
  | handlerBr hin => exact .handlerBr (hb hin)
  | handlerRet hin => exact .handlerRet (hb hin)
  | handlerTrap hin => exact .handlerTrap (hb hin)
  | handlerCatch hin hc => exact .handlerCatch (hb hin) hc
  | handlerRethrow hin hc => exact .handlerRethrow (hb hin) hc

theorem run_vals_normalC {s : Store H} {f : Frame} (us : List Val) :
    RunC P host C s f [] (vals us) s f (.normal us) := by
  simpa using run_valsC (P := P) (host := host) (C := C) (s := s) (f := f) (vs := []) (ws := us)
    (code := []) (by simpa using (RunC.nil (P := P) (host := host) (C := C) (s := s) (f := f)
      (vs := us)))

end Silmaril.Wasm.Cfg.Proofs.RegionC
