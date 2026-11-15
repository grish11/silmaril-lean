module

public import Silmaril.Wasm.Abstract.FragBody.Defs
public import Silmaril.Wasm.Abstract.Body.Thms
public import Silmaril.Wasm.Abstract.BodyTrace.Thms
public import Silmaril.Wasm.Abstract.SSAFragment.Thms
public import Silmaril.Wasm.SSA.Fragment.Thms
import Silmaril.Proofs.Wasm.Abstract.FragBody.Basic
import Silmaril.Proofs.Wasm.Abstract.FragBody.Core
import Silmaril.Proofs.Wasm.Abstract.FragBody.Examples
import Silmaril.Proofs.Wasm.Abstract.FragBody.Diverge
import Silmaril.Proofs.Wasm.Abstract.FragBody.Typed

/-!
# Concrete Wasm bodies as abstract bodies: theorems

For the structured integer fragment (`Silmaril.Wasm.Abstract.FragBody.Defs`
lists the coverage), the denotation `den` of concrete bodies into `BodyM` is:

**Structure-preserving, by constructor.** `denSeq_cons` (sequencing is
Kleisli composition), `denH_block` (blocks compose with the exit copairing),
`denH_loop` (a loop is the Elgot iteration of its body with `br 0` as the
continuing summand), `den_unreachable` (a trap). Elgot laws transfer: the
fixpoint law unfolds every loop (`den_loop_unfold`), and every law of
`Body.bodyOps_lawful` holds for the denoted morphisms.

**A congruence for the observable quotient.** Bodies that are equivalent up
to trap ≈ divergence and pending calls (`BodyTrace.FullCollapseEquiv`) give
equivalent blocks and loops (`denH_block_congr`, `denH_loop_congr`); the same
holds for equality.

**Adequate, both ways, divergence included.** `exec_iff`: a big-step
derivation `Exec ls e o` exists exactly when the denotation's tree is the
outcome's; `den_diverge_iff`: the denotation diverges exactly when there is
no derivation (an infinite loop, or a stuck, ill-typed configuration). No
determinism or termination is assumed: determinism of `Exec` is a
consequence, and loops are handled by the iteration of event-free trees.

**Functions and Core 3.0.** `run_iff`, `denFunc_diverge_iff`,
`toAFun_denFunc`: a fragment function's abstract body has exactly its runs
as trace behaviours, divergence when there is none. `callSem_eq_den`: a Core
3.0 call site holding the function (`IsFragmentSite`, the hypotheses of
`behaviours_eq_run`) has exactly the behaviours read off the abstract body:
the end-to-end bridge Core → fragment → `BodyM`.

**Divergence is Core divergence on validated code.** The fragment semantics
reads "no derivation" as divergence; that is the repository's behavioural
convention, not by itself an operational fact. For a validated call site it
becomes one: `den_diverges_iff_core` — the abstract body diverges exactly when
the Core 3.0 invocation has an infinite run of steps (`Diverges`). Core type
safety (behind `behaviours_eq_run`) excludes stuck runs, so on validated code
the denotation's `stuck` branches never produce divergence of their own.

**Typed interface.** `Ty`, `ArgsTy`, `SeqTy` (Defs) type the fragment with a
local context, a label context and the result type, as Wasm validation does
on it; `OutTy` types outcomes. Preservation: `exec_ty`, `seq_ty` (typed code
on typed locals has typed outcomes: locals keep their types, results and
branch values have the types of their targets), `run_ty` (a typed function's
return value has its result type). Example: `exampleSum_typed`.
Not yet: progress for typed code at the expression level (that the
denotation of typed code never takes a `stuck` branch), and the derivation of
`funcTyped` from Core validation of a fragment site.

**Faithful on the run quotient.** `denFunc_eq_iff`: two fragment functions
have equal abstract bodies exactly when they have the same runs (for a
nonempty module state; with an empty one all bodies are equal). With
`callEquiv_of_denFunc_eq`, equal abstract bodies give Core-equivalent call
sites. These bodies make no import call, so the trace observation with
pending calls (`BodyTrace.faithful_iff`) is equality here, and traps carry no
payload.

**Examples.** `spinFunc_diverges`, `spinFunc_no_run`: `loop br 0 end`
denotes silent divergence, computed from the Elgot iteration, hence has no
run (a Core-relevant fact proved through the abstract body).
`exampleSum_den`: the counting loop `exampleSum` on `3` denotes return `6`.

**Not covered.** Code outside the fragment (floats, memory, globals, calls
and imports, tables, `br_table`, exceptions and handlers, multi-value
blocks); a typed (type-indexed) interface, rather than untyped locals with
stuck configurations; recursion between functions; and CFG or region
semantics. The concrete-to-abstract functor for full Wasm is not claimed.
-/

public section

namespace Silmaril.Wasm.Abstract.FragBody

open Silmaril.Games Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Abstract.BodyTrace
  Silmaril.Wasm.SSA

variable {E : Sig.{0}} {S : Type 1}

/-! ## Structure -/

theorem denSeq_cons (e : SSA.Expr) (es : List SSA.Expr) (ls : List WVal) (r : Option WVal) :
    (denSeq (e :: es) ls r : M E S OutE) = den e ls >>= fun o =>
      match o.down with
      | .ok ls₁ r₁ => denSeq es ls₁ r₁
      | out => fin out := by
  rw [denSeq]; rfl

theorem denH_block (ty : Option Silmaril.Wasm.IntType) (body : List SSA.Expr) :
    (denH (.block ty body) : Hom E S PUnit.{2} Loc OutE) =
      fun l => seqH body l >>= fun r => blockK ty r.down := by
  funext l; simp only [denH, seqH, den]

theorem denH_loop (ty : Option Silmaril.Wasm.IntType) (body : List SSA.Expr) :
    (denH (.loop ty body) : Hom E S PUnit.{2} Loc OutE) =
      Silmaril.Elgot.iter fun l => seqH body l >>= fun r => loopK ty r.down := by
  funext ⟨l⟩; simp only [denH, seqH, den]

theorem den_unreachable (ls : List WVal) : (den .unreachable ls : M E S OutE) = trap ⟨⟩ := by
  simp only [den]

/-- The Elgot fixpoint law, transferred: a loop unfolds once. -/
theorem den_loop_unfold (ty : Option Silmaril.Wasm.IntType) (body : List SSA.Expr) (ls : List WVal) :
    (den (.loop ty body) ls : M E S OutE) =
      ((denSeq body ls none >>= fun r => loopK ty r.down) >>= Sum.elim pure
        fun l : Loc => den (.loop ty body) l.down) :=
  Silmaril.Proofs.Wasm.Abstract.FragBody.loop_unfold ty body ls

/-- Blocks respect the observable quotient. -/
theorem denH_block_congr {ty : Option Silmaril.Wasm.IntType} {body body' : List SSA.Expr}
    (h : FullCollapseEquiv (seqH body : Hom E S PUnit.{2} Loc OutE) (seqH body')) :
    FullCollapseEquiv (denH (.block ty body) : Hom E S PUnit.{2} Loc OutE) (denH (.block ty body')) := by
  rw [denH_block, denH_block]
  exact FullCollapseEquiv.comp h ((fullCollapseEquiv_iff _ _).2 fun _ => rfl)

/-- Loops respect the observable quotient. -/
theorem denH_loop_congr {ty : Option Silmaril.Wasm.IntType} {body body' : List SSA.Expr}
    (h : FullCollapseEquiv (seqH body : Hom E S PUnit.{2} Loc OutE) (seqH body')) :
    FullCollapseEquiv (denH (.loop ty body) : Hom E S PUnit.{2} Loc OutE) (denH (.loop ty body')) := by
  rw [denH_loop, denH_loop]
  exact FullCollapseEquiv.iter (FullCollapseEquiv.comp h ((fullCollapseEquiv_iff _ _).2 fun _ => rfl))

/-! ## Adequacy -/

/-- A derivation exists exactly when the denotation computes its outcome. -/
theorem exec_iff (e : SSA.Expr) (ls : List WVal) (s : S) (o : Out (Option WVal)) :
    Exec ls e o ↔ ((den e ls : M E S OutE).run s).run = outTree o s :=
  (Silmaril.Proofs.Wasm.Abstract.FragBody.den_exact e ls s).1 o

/-- The denotation diverges exactly when there is no derivation. -/
theorem den_diverge_iff (e : SSA.Expr) (ls : List WVal) (s : S) :
    ((den e ls : M E S OutE).run s).run = Silmaril.Elgot.ITree.diverge ↔ ∀ o, ¬ Exec ls e o :=
  (Silmaril.Proofs.Wasm.Abstract.FragBody.den_exact e ls s).2

/-- A run exists exactly when the function's abstract body computes it. -/
theorem run_iff (f : FragFunc) (args : List WVal) (s : S) (o : FOut) :
    f.Run args o ↔ ((denFunc f ⟨args⟩ : M E S _).run s).run = callTree o s :=
  (Silmaril.Proofs.Wasm.Abstract.FragBody.denFunc_exact f args s).1 o

/-- The function's abstract body diverges exactly when there is no run. -/
theorem denFunc_diverge_iff (f : FragFunc) (args : List WVal) (s : S) :
    ((denFunc f ⟨args⟩ : M E S _).run s).run = Silmaril.Elgot.ITree.diverge ↔
      ∀ o, ¬ f.Run args o :=
  (Silmaril.Proofs.Wasm.Abstract.FragBody.denFunc_exact f args s).2

/-- The trace denotation of a fragment function: its runs, or divergence. -/
theorem toAFun_denFunc (f : FragFunc) (args : List WVal) (s : S) :
    toAFun (denFunc f : Hom E S PUnit.{2} _ _) s ⟨args⟩ =
      {x | (∃ o, f.Run args o ∧ x = ([], foutEnd o s)) ∨ (x = ([], .div) ∧ ∀ o, ¬ f.Run args o)} :=
  Silmaril.Proofs.Wasm.Abstract.FragBody.toAFun_denFunc f args s

/-! ## Core 3.0 and faithfulness -/

/-- **End to end.** A Core 3.0 fragment call site has exactly the behaviours
read off the abstract body of its function. -/
theorem callSem_eq_den {H : Type} {x : CallSite H} {ft : Silmaril.Wasm.FuncType}
    {bf : Silmaril.Wasm.Binaryen.BFunc} {f : FragFunc} (hx : IsFragmentSite x ft bf f)
    {vs : List Silmaril.Wasm.Execution.Core.Val} (hok : Silmaril.Wasm.Execution.Core.InvokeOk x.store x.addr vs)
    (P : Silmaril.Wasm.Numerics.Profile) (st : S) :
    ∃ args : List WVal, vs = args.map WVal.toVal ∧
      callSem P x vs = (fun y => outBeh (endFOut y.2)) ''
        toAFun (denFunc f : Hom E S PUnit.{2} _ _) st ⟨args⟩ :=
  Silmaril.Proofs.Wasm.Abstract.FragBody.callSem_eq_den hx hok P st

/-- **Faithful on runs.** Equal abstract bodies exactly when equal runs. -/
theorem denFunc_eq_iff [Nonempty S] (f g : FragFunc) :
    (denFunc f : Hom E S PUnit.{2} _ _) = denFunc g ↔ ∀ args o, f.Run args o ↔ g.Run args o :=
  Silmaril.Proofs.Wasm.Abstract.FragBody.denFunc_eq_iff f g

/-- Equal abstract bodies give Core-equivalent call sites. -/
theorem callEquiv_of_denFunc_eq [Nonempty S] {H H' : Type} {x : CallSite H} {y : CallSite H'}
    {ft ft' : Silmaril.Wasm.FuncType} {bf bf' : Silmaril.Wasm.Binaryen.BFunc} {f f' : FragFunc}
    (hx : IsFragmentSite x ft bf f) (hy : IsFragmentSite y ft' bf' f')
    (hinv : ∀ vs, Silmaril.Wasm.Execution.Core.InvokeOk x.store x.addr vs →
      Silmaril.Wasm.Execution.Core.InvokeOk y.store y.addr vs)
    (h : (denFunc f : Hom E S PUnit.{2} _ _) = denFunc f') : CallEquiv x y :=
  callEquiv_of_run_iff hx hy hinv ((denFunc_eq_iff f f').1 h)

/-- **Divergence is operational on validated code.** At a validated fragment
call site, the abstract body diverges exactly when the Core 3.0 invocation
runs forever. -/
theorem den_diverges_iff_core {H : Type} {x : CallSite H} {ft : Silmaril.Wasm.FuncType}
    {bf : Silmaril.Wasm.Binaryen.BFunc} {f : FragFunc} (hx : IsFragmentSite x ft bf f)
    {vs : List Silmaril.Wasm.Execution.Core.Val}
    (hok : Silmaril.Wasm.Execution.Core.InvokeOk x.store x.addr vs)
    (P : Silmaril.Wasm.Numerics.Profile) {args : List WVal} (hv : vs = args.map WVal.toVal) (s : S) :
    ((denFunc f ⟨args⟩ : M E S _).run s).run = Silmaril.Elgot.ITree.diverge ↔
      Silmaril.Wasm.Execution.Core.Diverges P Silmaril.Wasm.Binaryen.closedHost
        (Silmaril.Wasm.Execution.Core.invoke x.store x.addr vs) :=
  Silmaril.Proofs.Wasm.Abstract.FragBody.den_diverges_iff_core hx hok P hv s

/-! ## Typed interface -/

/-- Preservation for expressions. -/
theorem exec_ty {Γ : List Silmaril.Wasm.IntType} {ρ : Option Silmaril.Wasm.IntType}
    {ls : List WVal} {e : SSA.Expr} {o : Out (Option WVal)} (h : Exec ls e o)
    {Λ : List (Option Silmaril.Wasm.IntType)} {r : Option Silmaril.Wasm.IntType}
    (hty : Ty Γ ρ Λ e r) (hls : ValsTy Γ ls) : OutTy Γ ρ Λ (ValTy r) o :=
  Silmaril.Proofs.Wasm.Abstract.FragBody.exec_ty h hty hls

/-- Preservation for bodies. -/
theorem seq_ty {Γ : List Silmaril.Wasm.IntType} {ρ : Option Silmaril.Wasm.IntType}
    {Λ : List (Option Silmaril.Wasm.IntType)} {es : List SSA.Expr} {ls : List WVal}
    {r0 : Option WVal} {o : Out (Option WVal)} {r : Option Silmaril.Wasm.IntType}
    (h : Seq ls r0 es o) (hty : SeqTy Γ ρ Λ es r) (hls : ValsTy Γ ls)
    (hr : es = [] → ValTy r r0) : OutTy Γ ρ Λ (ValTy r) o :=
  Silmaril.Proofs.Wasm.Abstract.FragBody.seq_ty h hty hls hr

/-- A typed function returns a value of its result type. -/
theorem run_ty {f : FragFunc} {args : List WVal} {r : Option WVal} (hf : funcTyped f)
    (h : f.Run args (.ret r)) : ValTy f.result r :=
  Silmaril.Proofs.Wasm.Abstract.FragBody.run_ty hf h

/-- The counting loop is typed. -/
theorem exampleSum_typed : funcTyped exampleSum := by
  unfold funcTyped exampleSum
  repeat (first | rfl | constructor)

/-! ## Examples -/

/-- `loop br 0 end` denotes silent divergence. -/
theorem spinFunc_diverges (s : S) :
    ((denFunc spinFunc ⟨[]⟩ : M E S _).run s).run = Silmaril.Elgot.ITree.diverge :=
  Silmaril.Proofs.Wasm.Abstract.FragBody.run_spinFunc s

/-- Hence it has no run. -/
theorem spinFunc_no_run (o : FOut) : ¬ spinFunc.Run [] o :=
  Silmaril.Proofs.Wasm.Abstract.FragBody.spinFunc_no_run o

/-- The counting loop on `3` denotes return `6`. -/
theorem exampleSum_den (s : S) :
    ((denFunc exampleSum ⟨[.i32 3]⟩ : M E S _).run s).run = callTree (.ret (some (.i32 6))) s :=
  (run_iff exampleSum _ s _).1 (FragFunc.eval_sound (fuel := 100) (by decide))

end Silmaril.Wasm.Abstract.FragBody
