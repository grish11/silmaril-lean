module

public import Silmaril.Wasm.Component.Param.Start.Defs
import Silmaril.Proofs.Wasm.Component.Param.Start

/-!
# The game semantics of an engine instance with a start function: theorems

All proved, for every engine; proofs in `Silmaril.Proofs.Wasm.Component.Param.Start`.

**Without a start function nothing changes.**

* `instOf_eq`: `instOf` is `instOfS` forgetting the start function on instances without one,
  and `none` on instances with one (the gap `engineSemS` closes).
* `engineStrategyS_of_start_none`: on an instance without a start function, `engineStrategyS`
  is `engineStrategy`.
* `engineSemS_sem_of_noStart`: on a module without a start function, `engineSemS` is
  `engineSem`.

**The start phase** (instance `I` whose start function is at address `a`):

* `engineStrategyS_start_prefix`: after the first question `q`, the import calls and answers
  `w` of a start run (`StartRun`) are a play;
* `engineStrategyS_start_call`: a callout of import `h` reached by the start function is the
  import question `h`, nested in the first question;
* `engineStrategyS_start_trap`: a trap of the start function answers the first question with a
  trap;
* `engineStrategyS_start_mem`: a start run with import moves `w` returning at store `s'` is
  followed by every play of `engineStrategy` from `s'`: `ask q :: p` there gives
  `ask q :: (w ++ p)` here;
* `engineStrategyS_eq_trapAll`: a start function that traps and can reach neither returned values
  nor a callout makes the instance `trapAll`.
-/

public section

namespace Silmaril.Wasm.Component.Param

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Engine.CoreEngine (Steps)

variable {E : Engine}

/-- `instOf` is `instOfS` on instances without a start function, and `none` on the others. -/
theorem instOf_eq (E : Engine) (m : E.Module) (imps exps : CoreIface) :
    instOf E m imps exps = (instOfS E m imps exps).bind fun I =>
      match I.start with
      | none => some I.toE
      | some _ => none :=
  Silmaril.Proofs.Wasm.Component.Param.instOf_eq E m imps exps

/-- **Without a start function, `engineStrategyS` is `engineStrategy`.** -/
theorem engineStrategyS_of_start_none (I : SInstance E) (h : I.start = none)
    (imps exps : CoreIface) :
    engineStrategyS E I imps exps = engineStrategy E I.toE imps exps :=
  Silmaril.Proofs.Wasm.Component.Param.engineStrategyS_of_start_none I h imps exps

/-- **On a module without a start function, `engineSemS` is `engineSem`.** -/
theorem engineSemS_sem_of_noStart (M : Type) [CoreModule M] (emb : M → E.Module) (m : M)
    (h : ∀ I, instOfS E (emb m) (CoreModule.imports m) (CoreModule.exports m) = some I →
      I.start = none) :
    (engineSemS E M emb).sem m = (engineSem E M emb).sem m :=
  Silmaril.Proofs.Wasm.Component.Param.engineSemS_sem_of_noStart M emb m h

/-- The import calls of the start phase follow the first question. -/
theorem engineStrategyS_start_prefix {I : SInstance E} {imps exps : CoreIface} {a : E.FuncAddr}
    (hs : I.start = some a) {w : List (Move (sigN imps.length) (sigN exps.length))}
    {c' : E.Config Nat} (hrun : StartRun E imps (I.store, E.invoke a []) w c')
    (q : (sigN exps.length).Op) :
    .inr (.ask q) :: w ∈ engineStrategyS E I imps exps :=
  Silmaril.Proofs.Wasm.Component.Param.engineStrategyS_start_prefix hs hrun q

/-- **A callout of the start function is an import question**, nested in the first
question. -/
theorem engineStrategyS_start_call {I : SInstance E} {imps exps : CoreIface} {a : E.FuncAddr}
    (hs : I.start = some a) {w : List (Move (sigN imps.length) (sigN exps.length))}
    {s' : E.Store Nat} {t' : E.Thread Nat}
    (hrun : StartRun E imps (I.store, E.invoke a []) w (s', t')) {h : Nat} {args : List Flat}
    (hc : E.status s' t' = .callout h args) (hh : h < imps.length) (q : (sigN exps.length).Op) :
    .inr (.ask q) :: (w ++ [.inl (.ask (⟨h, hh⟩, .flat args))]) ∈
      engineStrategyS E I imps exps :=
  Silmaril.Proofs.Wasm.Component.Param.engineStrategyS_start_call hs hrun hc hh q

/-- **A trap of the start function answers the first question with a trap.** -/
theorem engineStrategyS_start_trap {I : SInstance E} {imps exps : CoreIface} {a : E.FuncAddr}
    (hs : I.start = some a) {w : List (Move (sigN imps.length) (sigN exps.length))}
    {s' : E.Store Nat} {t' : E.Thread Nat}
    (hrun : StartRun E imps (I.store, E.invoke a []) w (s', t'))
    (ht : E.status s' t' = .returned .trap) (q : (sigN exps.length).Op) :
    .inr (.ask q) :: (w ++ [.inr (.ans q none)]) ∈ engineStrategyS E I imps exps :=
  Silmaril.Proofs.Wasm.Component.Param.engineStrategyS_start_trap hs hrun ht q

/-- **The start phase, then `engineStrategy` from the store it returns at**: a start run with
import moves `w` returning at `s'` puts `w` between the first question and the rest of every
play of `engineStrategy` from `s'`. -/
theorem engineStrategyS_start_mem {I : SInstance E} {imps exps : CoreIface} {a : E.FuncAddr}
    (hs : I.start = some a) {w : List (Move (sigN imps.length) (sigN exps.length))}
    {s' : E.Store Nat} {t' : E.Thread Nat}
    (hrun : StartRun E imps (I.store, E.invoke a []) w (s', t')) {ys : List Flat}
    (hfin : E.status s' t' = .returned (.values ys)) {q : (sigN exps.length).Op}
    {p : List (Move (sigN imps.length) (sigN exps.length))}
    (hp : .inr (.ask q) :: p ∈ engineStrategy E ⟨s', I.addrs⟩ imps exps) :
    .inr (.ask q) :: (w ++ p) ∈ engineStrategyS E I imps exps :=
  Silmaril.Proofs.Wasm.Component.Param.engineStrategyS_start_mem hs hrun hfin hp

/-- **A start function that can only trap makes the instance trap on every question.** -/
theorem engineStrategyS_eq_trapAll {I : SInstance E} {imps exps : CoreIface} {a : E.FuncAddr}
    (hs : I.start = some a)
    (htrap : ∃ s' t', Steps E (I.store, E.invoke a []) (s', t') ∧ E.status s' t' = .returned .trap)
    (honly : ∀ s' t', Steps E (I.store, E.invoke a []) (s', t') →
      (∀ ys, E.status s' t' ≠ .returned (.values ys)) ∧ ∀ h args, E.status s' t' ≠ .callout h args) :
    engineStrategyS E I imps exps = trapAll _ _ :=
  Silmaril.Proofs.Wasm.Component.Param.engineStrategyS_eq_trapAll hs htrap honly

end Silmaril.Wasm.Component.Param
