module

public import Silmaril.Wasm.Cfg.DanglingTyped.Defs
public import Silmaril.Wasm.Interp.CheckComplete.Defs

@[expose] public section

/-!
# Checker-profile stores have supported functions (proofs)

* `isupp_of_supported`: an instruction whose lifted tree is in the checker's instruction profile
  (`CheckComplete.supported1`) is supported (`ISupp`): `XProfile.xInstr` contains no `ref.test`,
  `ref.cast`, `br_on_cast*` or aggregate instruction, and the profile recurses into every body;
* `funcsSupp_of_storeSupported`: a `StoreOk` store whose Wasm functions are in the profile
  (`CheckComplete.StoreSupported`) has supported functions. The tags of a function's module are
  addresses of the store (`ModuleInstOk`).
-/

namespace Silmaril.Wasm.Cfg.Proofs.DanglingTyped

open Silmaril.Wasm.Cfg.DanglingTyped
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen (liftInstr liftInstrs)
open Silmaril.Wasm.Interp.CheckComplete (supported1 supported StoreSupported)

variable {H : Type}

theorem liftInstr_atom {i : Instr} (hs : ¬ Structured i) : liftInstr i = .op i [] := by
  cases i <;> simp_all [Structured, liftInstr]

theorem not_unsupp_of_xInstr {i : Instr} (h : Interp.XProfile.xInstr i = true) : ¬ Unsupp i := by
  cases i <;> simp_all [Interp.XProfile.xInstr, Unsupp]

mutual
/-- **An instruction in the checker's profile is supported.** -/
theorem isupp_of_supported (i : Instr) (h : supported1 (liftInstr i) = true) : ISupp i := by
  by_cases hs : Structured i
  · match i, h, hs with
    | .block bt body, h, _ =>
      exact .block bt (isupps_of_supported body (by simpa [liftInstr, supported1] using h))
    | .loop bt body, h, _ =>
      exact .loop bt (isupps_of_supported body (by simpa [liftInstr, supported1] using h))
    | .if_ bt t e, h, _ =>
      simp only [liftInstr, supported1, Bool.and_eq_true] at h
      exact .if_ bt (isupps_of_supported t h.1.2) (isupps_of_supported e h.2)
    | .tryTable bt cs body, h, _ =>
      exact .tryTable bt cs (isupps_of_supported body (by simpa [liftInstr, supported1] using h))
    | .unreachable, _, hs | .nop, _, hs => simp [Structured] at hs
  · rw [liftInstr_atom hs] at h
    simp only [supported1, Bool.and_eq_true] at h
    exact .atom hs (not_unsupp_of_xInstr h.1)
termination_by sizeOf i
decreasing_by all_goals (simp_wf; first | done | omega)

/-- **A sequence in the checker's profile is supported.** -/
theorem isupps_of_supported (is : List Instr) (h : supported (liftInstrs is) = true) :
    ∀ i ∈ is, ISupp i := by
  match is, h with
  | [], _ => exact fun _ h => nomatch h
  | j :: js, h =>
    simp only [liftInstrs, supported, Bool.and_eq_true] at h
    intro i hi
    cases hi with
    | head => exact isupp_of_supported j h.1
    | tail _ hi => exact isupps_of_supported js h.2 i hi
termination_by sizeOf is
decreasing_by all_goals (simp_wf; first | done | omega)
end

theorem tag_lt_of_externAddrOk {s : Store H} {a : Nat} {xt : CExternType}
    (h : ExternAddrOk s (.tag a) xt) : a < s.tags.length := by
  generalize hx : ExternAddr.tag a = x at h
  induction h with
  | tag h => cases hx; exact (List.getElem?_eq_some_iff.1 h).1
  | global | mem | table | func => cases hx
  | sub _ _ _ ih => exact ih hx

theorem frameBelow_of_moduleInstOk {s : Store H} {mi : ModuleInst} {C : Context}
    (h : ModuleInstOk s mi C) : FrameBelow s.tags.length ⟨[], mi⟩ := by
  cases h with
  | mk _ htags =>
    intro t ht
    obtain ⟨_, hx⟩ : ∃ x, ExternAddrOk s (.tag t) x := by
      clear * - htags ht
      generalize mi.tags = l at htags ht
      induction htags with
      | nil => cases ht
      | cons hab _ ih =>
        rcases List.mem_cons.1 ht with rfl | ht
        · exact ⟨_, hab⟩
        · exact ih ht
    exact tag_lt_of_externAddrOk hx

/-- **A typed store whose Wasm functions are in the checker's profile has supported functions.** -/
theorem funcsSupp_of_storeSupported {s : Store H} (hs : StoreOk s)
    (hsup : StoreSupported s.funcs) : FuncsSupp s := by
  intro fi hfi code hcode
  obtain ⟨a, ha, hfa⟩ := List.getElem_of_mem hfi
  have hget : s.funcs[a]? = some fi := by rw [List.getElem?_eq_getElem ha, hfa]
  refine ⟨?_, isupps_of_supported _ (hsup a fi code hget hcode)⟩
  cases hs.funcs fi hfi with
  | wasm _ hm => exact frameBelow_of_moduleInstOk hm
  | host _ _ hc => rw [hcode] at hc; cases hc

end Silmaril.Wasm.Cfg.Proofs.DanglingTyped
