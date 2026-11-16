module

public import Silmaril.Wasm.Interp.EHExt.Defs
public import Silmaril.Proofs.Wasm.Interp.TailX

/-!
# The arity checker extension with exceptions (proofs)

`ehExt tags`: `tExt` with `throw`, `throw_ref` and `try_table` (`Silmaril.Wasm.Interp.EHExt`).

* `ehExt_of_not_eh`: off the exception forms it is `tExt`;
* `chkE_ehExt_of_chkE_tExt`: every `tExt`-checked tree is `ehExt`-checked, with the same result
  (`tExt` rejects the exception forms), so `StoreChkE tExt` gives `StoreChkE (ehExt tags)`;
* `tagFields_of_tag?`: the field count the checker reads is the one `throw` uses.
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- **The arity checker extension with exceptions**, for a store with tag instances `tags`. -/
def ehExt (tags : List TagInst) : ExtArity H := fun F mi i =>
  match i with
  | .throw x => (tagFields tags mi x).map .stop
  | .throwRef => some (.stop 1)
  | .tryTable _ cs _ => (cs.mapM (clauseCount tags mi)).map .catches
  | _ => tExt F mi i

instance (tags : List TagInst) : ExtStable (ehExt (H := H) tags) := ⟨fun {F F' mi i e} hF h => by
  cases i <;> first
    | exact h
    | (simp only [ehExt] at h ⊢; exact ExtStable.stable (ext := tExt) hF h)⟩

/-- Off the exception forms, `ehExt` is `tExt`. -/
theorem ehExt_of_not_eh {tags : List TagInst} {F : List (FuncInst H)} {mi : ModuleInst}
    {i : Instr} (h₁ : ∀ x, i ≠ .throw x) (h₂ : i ≠ .throwRef)
    (h₃ : ∀ bt cs b, i ≠ .tryTable bt cs b) : ehExt tags F mi i = tExt F mi i := by
  cases i <;> first | rfl | exact absurd rfl (h₁ _) | exact absurd rfl h₂ | exact absurd rfl (h₃ _ _ _)

/-- A `tExt` flat check is an `ehExt` flat check. -/
theorem flatChkE_ehExt_of_tExt {tags : List TagInst} {F : List (FuncInst H)} {mi : ModuleInst}
    {nl ret : Nat} {labels : List Nat} {h : Nat} {i : Instr} {o : Option Nat}
    (hc : flatChkE tExt F mi nl ret labels h i = some o) :
    flatChkE (ehExt tags) F mi nl ret labels h i = some o := by
  cases i <;> first
    | exact hc
    | (simp [flatChkE, tExt, extStep] at hc)

set_option linter.unusedSectionVars false in
mutual
/-- **Every `tExt`-checked tree is `ehExt`-checked**, with the same result. -/
theorem chkE_ehExt_of_tExt {tags : List TagInst} {F : List (FuncInst H)} {mi : ModuleInst}
    {nl ret : Nat} {labels : List Nat} :
    ∀ (oh : Option Nat) (es : List Binaryen.BExpr) {o : Option Nat},
      chkE tExt F mi nl ret labels oh es = some o → chkE (ehExt tags) F mi nl ret labels oh es = some o
  | none, es, o, hc => by
    rw [chk_noneE] at hc ⊢
    exact hc
  | some k, [], o, hc => hc
  | some k, e :: es, o, hc => by
    obtain ⟨o₁, h1, h2⟩ := chk_consE.mp hc
    exact chk_consE.mpr ⟨o₁, chk1E_ehExt_of_tExt k e h1, chkE_ehExt_of_tExt o₁ es h2⟩

theorem chk1E_ehExt_of_tExt {tags : List TagInst} {F : List (FuncInst H)} {mi : ModuleInst}
    {nl ret : Nat} {labels : List Nat} :
    ∀ (k : Nat) (e : Binaryen.BExpr) {o : Option Nat},
      chk1E tExt F mi nl ret labels k e = some o → chk1E (ehExt tags) F mi nl ret labels k e = some o
  | k, .op i args, o, hc => by
    simp only [chk1E, Option.bind_eq_some_iff] at hc ⊢
    obtain ⟨oa, ha, hk⟩ := hc
    refine ⟨oa, chkE_ehExt_of_tExt (some k) args ha, ?_⟩
    rcases oa with _ | h₁
    · exact hk
    · exact flatChkE_ehExt_of_tExt hk
  | k, .block bt body, o, hc => by
    obtain ⟨np, nr, hbt, hle, hends, rfl⟩ := chk1_blockE hc
    simp only [chk1E, hbt, hle, decide_true, Bool.true_and,
      endsAt_transfer (fun _ => chkE_ehExt_of_tExt (some np) body) hends, ite_true]
  | k, .loop bt body, o, hc => by
    obtain ⟨np, nr, hbt, hle, hends, rfl⟩ := chk1_loopE hc
    simp only [chk1E, hbt, hle, decide_true, Bool.true_and,
      endsAt_transfer (fun _ => chkE_ehExt_of_tExt (some np) body) hends, ite_true]
  | k, .if_ bt c t el, o, hc => by
    obtain ⟨oc, hco, hk⟩ := chk1_ifE hc
    simp only [chk1E, Option.bind_eq_some_iff]
    refine ⟨oc, chkE_ehExt_of_tExt (some k) c hco, ?_⟩
    rcases oc with _ | h₁
    · simp only [chk1E, Option.bind_eq_some_iff, hco] at hc
      obtain ⟨_, hx, hy⟩ := hc
      cases hx
      exact hy
    · obtain ⟨np, nr, hbt, hle, ht, he, rfl⟩ := hk h₁ rfl
      simp only [hbt, hle, decide_true,
        endsAt_transfer (fun _ => chkE_ehExt_of_tExt (some np) t) ht,
        endsAt_transfer (fun _ => chkE_ehExt_of_tExt (some np) el) he, Bool.and_self, ite_true]
  | k, .tryTable .., o, hc => by simp [chk1E, tExt] at hc
end

/-- A `tExt`-checked store is `ehExt`-checked. -/
theorem storeChkE_ehExt_of_tExt {tags : List TagInst} {F : List (FuncInst H)}
    (hS : StoreChkE tExt F) : StoreChkE (ehExt tags) F :=
  fun a fi fn ps rs ha hc ht =>
    endsAt_transfer (fun _ ho => chkE_ehExt_of_tExt _ _ ho) (hS a fi fn ps rs ha hc ht)

/-- **The field count the checker reads is the one `throw` uses.** -/
theorem tagFields_of_tag? {s : Store H} {f : Frame} {x : TagIdx} {ta : Nat} {ti : TagInst}
    {ts : Validation.Ty (.list .val)} (ht : s.tag? f x = some (ta, ti))
    (he : Validation.Expand ti.type (.func ts .nil)) :
    tagFields s.tags f.module x = some ts.length := by
  simp only [Store.tag?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Prod.mk.injEq] at ht
  obtain ⟨a, ha, ti', hti, rfl, rfl⟩ := ht
  have hty : Validation.DefType.funcType? ti'.type =
      some (ts.toList, (Validation.Ty.nil : Validation.Ty (.list .val)).toList) := by
    unfold Validation.DefType.funcType?; rw [Validation.Expand.iff.mp he]
  simp only [tagFields, ha, hti, Option.bind_eq_bind, Option.bind_some, hty]
  rfl

end Silmaril.Wasm.Interp
