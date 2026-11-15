module

public import Silmaril.Proofs.Wasm.Interp.Arity

@[expose] public section

/-!
# The arity check under a change of code (proofs)

The arity check `chk` reads the store's functions and the module instance only through the
arities of called functions (`callArity`) and of block types (`blockArity`). So a check passing
against one store and instance passes, with the same result, against any other that has (at
least) the same arities (`chk_transfer`): in particular a check passing against the empty
store and instance passes everywhere (`chk_of_free`), and replacing the code of one function
by code passing the check keeps `StoreChk` (`storeChk_modify`). New proofs.
-/

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

variable {H H' : Type}

section Transfer

variable {F₁ : List (FuncInst H)} {F₂ : List (FuncInst H')} {mi₁ mi₂ : ModuleInst} {nl ret : Nat}

/-- The empty store and instance know no arity of calls or of type-indexed blocks. -/
theorem arities_free (F : List (FuncInst H')) (mi : ModuleInst) :
    Arities ([] : List (FuncInst Empty)) {} F mi := by
  constructor
  · intro x p h
    simp [callArity] at h
  · intro bt p h
    cases bt
    · exact h
    · exact h
    · simp [blockArity, Binaryen.arity, Frame.type?] at h

/-- **A check passing against the empty store and instance passes everywhere.** -/
theorem chk_of_free {F : List (FuncInst H')} {mi : ModuleInst} {labels : List Nat}
    {oh : Option Nat} {es : List Binaryen.BExpr} {o : Option Nat}
    (hc : chk ([] : List (FuncInst Empty)) {} nl ret labels oh es = some o) :
    chk F mi nl ret labels oh es = some o :=
  chk_transfer (arities_free F mi) oh es hc

end Transfer

/-- Replacing code keeps the arities of called functions. -/
theorem arities_modify (F : List (FuncInst H)) (mi : ModuleInst) (a : Nat) (fn' : Func) :
    Arities F mi (F.modify a fun fi => { fi with code := .wasm fn' }) mi := by
  constructor
  · intro x p h
    unfold callArity at h ⊢
    rcases hx : mi.funcs[x.toNat]? with _ | b
    · simp [hx] at h
    · simp only [hx, bind, Option.bind] at h ⊢
      rw [List.getElem?_modify]
      rcases hb : F[b]? with _ | fi
      · simp [hb] at h
      · simp only [hb] at h
        by_cases hab : a = b <;> simpa [hab] using h
  · intro bt p h
    exact h

/-- **Replacing the code of a function by code passing the check keeps `StoreChk`.** The check
of the new code is against the empty store and instance (`chkFree`). -/
theorem storeChk_modify {F : List (FuncInst H)} (hS : StoreChk F) {a : Nat} {fn' : Func}
    (hc : ∀ fi ps rs, F[a]? = some fi → Validation.DefType.funcType? fi.type = some (ps, rs) →
      endsAt (chk ([] : List (FuncInst Empty)) {} (ps.length + fn'.locals.length) rs.length
        [rs.length] (some 0) (Binaryen.liftInstrs fn'.body)) rs.length = true) :
    StoreChk (F.modify a fun fi => { fi with code := .wasm fn' }) := by
  intro b fi' fn ps rs hfi' hcode hty
  rw [List.getElem?_modify] at hfi'
  rcases hb : F[b]? with _ | fi
  · simp [hb] at hfi'
  · simp only [hb, Option.map_eq_map, Option.map_some, Option.some.injEq] at hfi'
    by_cases hab : a = b
    · subst hab
      simp only [ite_true] at hfi'
      subst hfi'
      have hfn : fn' = fn := by simpa using hcode
      subst hfn
      exact endsAt_transfer (fun o h => chk_of_free h) (hc fi ps rs hb hty)
    · simp only [hab, ite_false] at hfi'
      subst hfi'
      exact endsAt_transfer (fun o h => chk_transfer (arities_modify F fi.module a fn') _ _ h)
        (hS b fi fn ps rs hb hcode hty)

end Silmaril.Wasm.Interp
