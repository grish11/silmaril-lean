module

public import Silmaril.Wasm.Abstract.FunctorP.Defs
public import Silmaril.Wasm.Abstract.ExposeP.Thms
import Silmaril.Proofs.Wasm.Abstract.FunctorP.Faithful

/-!
# Operational observations of the canonical F5 semantics, and the denotation functor: theorems

**1. Logged runs and pending observations are exactly the denotation's paths and pending calls**
(any oracle `C`, any store, frame and stack):

* `evalLXP_iff`, `evalLXP_trap_iff`: a logged run of `es` with log `cs` ending in a non-trap
  result (resp. a trap) is exactly a finished path of `ExposeP.denListXP es` with exactly the call
  events `cs`, each answered as `C` allows, to that result (resp. to the trap effect);
* `reachXP_iff_pend`: a logged pending observation is exactly a pending call of the exposed body
  after exactly `cs` (`BodyTrace.Pend`), `cs` answered by `C`; `exists_reachXP_iff` is the
  unlogged form of `XDecomp.reachX_iff_pend`;
* `evalOXP_iff_log`, `evalOXP_trap_iff_log`: `EvalOXP C` is the logged runs with the log
  forgotten;
* the frame: `frameLXP_iff`, `frameLXP_trap_iff`, `frameReachXP_iff_pend` (a pending tail call's
  event is made at the frame, after the body's events), `bodyCallXP_iff_log`.

**2. Faithfulness.** `opEquivP_iff`: two code lists have the same denotation up to trap payloads
(`BodyTrace.erasedRun (denL es) = erasedRun (denL es')`, the quotient of `BodyTrace.faithful_iff`)
**exactly** when they are operationally equivalent (`OpEquivP`): for every oracle, store, frame,
stack and log, the same non-trap logged outcomes, the same logged traps and the same logged pending
calls. `opCollapseEquivP_iff`: `BodyTrace.FullCollapseEquiv (denL es) (denL es')` exactly when
`OpCollapseEquivP` (non-trap outcomes and pending calls only; a trap identified with
divergence). Both observations see infinite productive runs through their prefixes:
`OpEquivP.toInf`, `OpCollapseEquivP.toInf` (with `BodyTrace.toInf_eq_of_faithful`).

The ← directions take the universal oracle, which answers every call: with the log recorded,
one oracle sees every path. Without the log the statement would be false for trees in general
(see `FunctorP.Defs`): an oracle is a relation and cannot tell two positions of the same event
apart, so quantifying over oracles does not recover a path from unlogged outcomes. Neither
direction uses finite closed answers or an injective encoding.

**3. The functor.** `denFunctor Γ` (Defs): the checked category `CObj Γ` (code typed by
`ExposePStruct.Hom`, composition concatenation) into the one-object category of exposed bodies
under `seqP`. `denFunctor_map`; blocks, loops (the Elgot iteration `loopP` of the step),
`if` and `try_table` morphisms are sent to `blockP`, `loopP`, `ifP`, `tryP` of their bodies'
images (`denFunctor_block`, `denFunctor_loop`, `denFunctor_if`, `denFunctor_try`), and
`ExposePStruct`'s congruences (`blockP_congr`, `loopP_congr`, …) make `FullCollapseEquiv` a
congruence. **Faithful on the quotients**: `denFunctor_faithful` (exact, `OpEquivP`) and
`denFunctor_faithful_collapse` (`OpCollapseEquivP`).
-/

public section

namespace Silmaril.Wasm.Abstract.FunctorP

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (CallRel)
open Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
open Silmaril.Wasm.Abstract.CallXP Silmaril.Wasm.Abstract.ExposeP Silmaril.Wasm.Abstract.ExposePStruct
open Silmaril.Wasm.Abstract.BodyTrace (Path Pend erasedRun FullCollapseEquiv toInf)
open Silmaril.Wasm.Interp

variable {H : Type}

/-! ## 1. Exactness of the logged observations -/

section
variable {C : CallRel H}

/-- **Logged runs are exactly answered paths (values).** -/
theorem evalLXP_iff {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {cs : List (ACall H)} {s' : Store H} {f' : Frame} {o : POut} (ho : o ≠ .flow .trap) :
    EvalLXP C s f stk es cs (s', f', o) ↔
      Answered C cs ∧ Path (((denListXP es f stk : M (CallSig H) H ResP).run ⟨s⟩).run) cs
        (.val (.ok (⟨(f', o)⟩, ⟨s'⟩))) :=
  Silmaril.Proofs.Wasm.Abstract.FunctorP.evalLXP_iff ho

/-- **Logged runs are exactly answered paths (traps).** -/
theorem evalLXP_trap_iff {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {cs : List (ACall H)} :
    (∃ s' f', EvalLXP C s f stk es cs (s', f', .flow .trap)) ↔
      Answered C cs ∧ Path (((denListXP es f stk : M (CallSig H) H ResP).run ⟨s⟩).run) cs
        (.val (.error ⟨⟩)) :=
  Silmaril.Proofs.Wasm.Abstract.FunctorP.evalLXP_trap_iff

/-- **Logged pending observations are exactly the denotation's pending calls.** -/
theorem reachXP_iff_pend {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {cs : List (ACall H)} {y : Nat × List Val × Store H} :
    ReachXP C s f stk es cs y ↔
      Answered C cs ∧ Pend (((denListXP es f stk : M (CallSig H) H ResP).run ⟨s⟩).run) cs y :=
  Silmaril.Proofs.Wasm.Abstract.FunctorP.reachXP_iff

/-- The unlogged form (as `XDecomp.reachX_iff_pend`). -/
theorem exists_reachXP_iff {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {y : Nat × List Val × Store H} :
    (∃ cs, ReachXP C s f stk es cs y) ↔
      ∃ cs, Answered C cs ∧ Pend (((denListXP es f stk : M (CallSig H) H ResP).run ⟨s⟩).run) cs y :=
  exists_congr fun _ => reachXP_iff_pend

/-- `EvalOXP C` is the logged runs with their log forgotten (non-trap results). -/
theorem evalOXP_iff_log {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {s' : Store H} {f' : Frame} {o : POut} (ho : o ≠ .flow .trap) :
    EvalOXP C s f stk es (s', f', o) ↔ ∃ cs, EvalLXP C s f stk es cs (s', f', o) :=
  Silmaril.Proofs.Wasm.Abstract.FunctorP.evalOXP_iff_log ho

/-- The same for traps. -/
theorem evalOXP_trap_iff_log {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr} :
    (∃ s' f', EvalOXP C s f stk es (s', f', .flow .trap)) ↔
      ∃ cs s' f', EvalLXP C s f stk es cs (s', f', .flow .trap) :=
  Silmaril.Proofs.Wasm.Abstract.FunctorP.evalOXP_trap_iff_log

/-- **A logged frame is exactly an answered path of `frameXP` (values).** -/
theorem frameLXP_iff {s : Store H} {a : Nat} {args : List Val} {cs : List (ACall H)}
    {s' : Store H} {fl : Flow} (hfl : fl ≠ .trap) :
    FrameLXP C s a args cs (s', fl) ↔
      Answered C cs ∧ Path (((frameXP a args : M (CallSig H) H (ULift.{1} Flow)).run ⟨s⟩).run) cs
        (.val (.ok (⟨fl⟩, ⟨s'⟩))) :=
  Silmaril.Proofs.Wasm.Abstract.FunctorP.frameLXP_iff hfl

theorem frameLXP_trap_iff {s : Store H} {a : Nat} {args : List Val} {cs : List (ACall H)} :
    (∃ s', FrameLXP C s a args cs (s', .trap)) ↔
      Answered C cs ∧ Path (((frameXP a args : M (CallSig H) H (ULift.{1} Flow)).run ⟨s⟩).run) cs
        (.val (.error ⟨⟩)) :=
  Silmaril.Proofs.Wasm.Abstract.FunctorP.frameLXP_trap_iff

/-- **Frame-level pending observations are exactly `frameXP`'s pending calls**, a pending tail
call's event made at the frame. -/
theorem frameReachXP_iff_pend {s : Store H} {a : Nat} {args : List Val} {cs : List (ACall H)}
    {y : Nat × List Val × Store H} :
    FrameReachXP C s a args cs y ↔
      Answered C cs ∧ Pend (((frameXP a args : M (CallSig H) H (ULift.{1} Flow)).run ⟨s⟩).run) cs y :=
  Silmaril.Proofs.Wasm.Abstract.FunctorP.frameReachXP_iff

/-- `bodyCallXP C` is the logged frames with their log forgotten (non-trap results). -/
theorem bodyCallXP_iff_log {s : Store H} {a : Nat} {args : List Val} {s' : Store H} {fl : Flow}
    (hfl : fl ≠ .trap) : bodyCallXP C s a args (s', fl) ↔ ∃ cs, FrameLXP C s a args cs (s', fl) := by
  rw [Silmaril.Wasm.Abstract.ExposeP.bodyCallXP_iff hfl]; simp only [frameLXP_iff hfl]

end

/-! ## 2. Faithfulness -/

/-- **Exact faithfulness**: equal denotations up to trap payloads are exactly operational
equivalence (logged outcomes, traps and pending calls, at every oracle). -/
theorem opEquivP_iff (es es' : List BExpr) :
    erasedRun (denL (H := H) es) = erasedRun (denL es') ↔ OpEquivP H es es' :=
  Silmaril.Proofs.Wasm.Abstract.FunctorP.opEquivP_iff es es'

/-- **Faithfulness up to trap ≈ divergence.** -/
theorem opCollapseEquivP_iff (es es' : List BExpr) :
    FullCollapseEquiv (denL (H := H) es) (denL es') ↔ OpCollapseEquivP H es es' :=
  Silmaril.Proofs.Wasm.Abstract.FunctorP.opCollapseEquivP_iff es es'

/-- Exact equivalence implies equivalence up to trap ≈ divergence. -/
theorem OpEquivP.collapse {es es' : List BExpr} (h : OpEquivP H es es') :
    OpCollapseEquivP H es es' := fun C s f stk cs =>
  ⟨(h C s f stk cs).1, (h C s f stk cs).2.2⟩

/-- Operationally equivalent code has the same infinite productive runs. -/
theorem OpEquivP.toInf {es es' : List BExpr} (h : OpEquivP H es es') :
    toInf (denL (H := H) es) = toInf (denL es') :=
  BodyTrace.toInf_eq_of_faithful ((opEquivP_iff es es').2 h)

theorem OpCollapseEquivP.toInf {es es' : List BExpr} (h : OpCollapseEquivP H es es') :
    toInf (denL (H := H) es) = toInf (denL es') :=
  BodyTrace.FullCollapseEquiv.toInf ((opCollapseEquivP_iff es es').2 h)

/-- Operationally equivalent code has the same `EvalOXP C` outcomes, for every oracle. -/
theorem OpEquivP.evalOXP {es es' : List BExpr} (h : OpEquivP H es es') (C : CallRel H)
    (s : Store H) (f : Frame) (stk : List Val) {s' : Store H} {f' : Frame} {o : POut}
    (ho : o ≠ .flow .trap) : EvalOXP C s f stk es (s', f', o) ↔ EvalOXP C s f stk es' (s', f', o) := by
  rw [evalOXP_iff_log ho, evalOXP_iff_log ho]
  exact exists_congr fun cs => (h C s f stk cs).1 s' f' o ho

/-- **Frames of operationally equivalent bodies are equal**: two Wasm functions of a store with
the same module instance and locals and operationally equivalent bodies have the same exposed
frame (`ExposeP.frameXP`) at every argument list, so the same `bodyCallXP C` answers for every
oracle (`bodyCallXP_iff`, `bodyCallXP_trap_iff`). -/
theorem frameXP_run_eq {s : Store H} {a b : Nat} {args : List Val} {fi fi' : FuncInst H}
    {fn fn' : Func} {ps rs ps' rs' : List Validation.CValType}
    (hfa : s.funcs[a]? = some fi) (hca : fi.code = .wasm fn)
    (htya : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hfb : s.funcs[b]? = some fi') (hcb : fi'.code = .wasm fn')
    (htyb : Validation.DefType.funcType? fi'.type = some (ps', rs'))
    (hmod : fi.module = fi'.module) (hloc : fn.locals = fn'.locals)
    (hbody : OpEquivP H (liftInstrs fn.body) (liftInstrs fn'.body)) :
    ((frameXP a args : M (CallSig H) H (ULift.{1} Flow)).run ⟨s⟩).run =
      ((frameXP b args : M (CallSig H) H (ULift.{1} Flow)).run ⟨s⟩).run :=
  Silmaril.Proofs.Wasm.Abstract.FunctorP.frameXP_run_eq hfa hca htya hfb hcb htyb hmod hloc hbody

/-! ## 3. The functor -/

section
variable {Γ : Ctx H}

theorem denFunctor_map {I J : CObj Γ} (m : I ⟶ J) :
    ((denFunctor Γ).map m : PHom H Cfg ResP) = denL m.1 := rfl

/-- **The functor is faithful up to trap payloads**: checked morphisms with the same image
modulo `erasedRun` are exactly the operationally equivalent ones. -/
theorem denFunctor_faithful {I J : CObj Γ} (m m' : I ⟶ J) :
    erasedRun ((denFunctor Γ).map m : PHom H Cfg ResP) = erasedRun ((denFunctor Γ).map m') ↔
      OpEquivP H m.1 m'.1 :=
  opEquivP_iff m.1 m'.1

/-- **The functor is faithful on the trap ≈ divergence quotient.** -/
theorem denFunctor_faithful_collapse {I J : CObj Γ} (m m' : I ⟶ J) :
    FullCollapseEquiv ((denFunctor Γ).map m : PHom H Cfg ResP) ((denFunctor Γ).map m') ↔
      OpCollapseEquivP H m.1 m'.1 :=
  opCollapseEquivP_iff m.1 m'.1

/-- A checked `block` is a morphism, sent to the exit copairing of its body's image. -/
theorem denFunctor_block {I : Iface} {bt : BlockType} {body : List BExpr} {np nr : Nat}
    {o : Option Nat} (hbt : blockArity I.env.mi bt = some (np, nr)) (hle : np ≤ I.h)
    (hb : Mor Γ ⟨I.env.push nr, np⟩ o body) (he : endsAt (some o) nr = true) :
    ∃ m : @Quiver.Hom (CObj Γ) _ I (Iface.mk I.env (I.h - np + nr)),
      m.1 = [.block bt body] ∧
        ((denFunctor Γ).map m : PHom H Cfg ResP) = blockP bt (denL body) :=
  ⟨⟨_, rfl, mor_block hbt hle hb he⟩, rfl, by
    show denL _ = _
    rw [denL_singleton, denT_block]⟩

/-- A checked `loop` is a morphism, sent to the Elgot iteration of its body's step. -/
theorem denFunctor_loop {I : Iface} {bt : BlockType} {body : List BExpr} {np nr : Nat}
    {o : Option Nat} (hbt : blockArity I.env.mi bt = some (np, nr)) (hle : np ≤ I.h)
    (hb : Mor Γ ⟨I.env.push np, np⟩ o body) (he : endsAt (some o) nr = true) :
    ∃ m : @Quiver.Hom (CObj Γ) _ I (Iface.mk I.env (I.h - np + nr)),
      m.1 = [.loop bt body] ∧
        ((denFunctor Γ).map m : PHom H Cfg ResP) = loopP bt (denL body) :=
  ⟨⟨_, rfl, mor_loop hbt hle hb he⟩, rfl, by
    show denL _ = _
    rw [denL_singleton, denT_loop]; rfl⟩

/-- A checked `if` is a morphism, sent to `ifP` of its condition's and arms' images. -/
theorem denFunctor_if {I : Iface} {bt : BlockType} {c t el : List BExpr} {h₁ np nr : Nat}
    {ot oe : Option Nat} (hc : Mor Γ I (some h₁) c) (hbt : blockArity I.env.mi bt = some (np, nr))
    (hle : np + 1 ≤ h₁) (ht : Mor Γ ⟨I.env.push nr, np⟩ ot t) (het : endsAt (some ot) nr = true)
    (he : Mor Γ ⟨I.env.push nr, np⟩ oe el) (hee : endsAt (some oe) nr = true) :
    ∃ m : @Quiver.Hom (CObj Γ) _ I (Iface.mk I.env (h₁ - 1 - np + nr)),
      m.1 = [.if_ bt c t el] ∧
        ((denFunctor Γ).map m : PHom H Cfg ResP) = ifP bt (denL c) (denL t) (denL el) :=
  ⟨⟨_, rfl, mor_if hc hbt hle ht het he hee⟩, rfl, by
    show denL _ = _
    rw [denL_singleton, denT_if]⟩

/-- A checked `try_table` is a morphism, sent to the handler copairing of its body's image. -/
theorem denFunctor_try {I : Iface} {bt : BlockType} {cls : List Catch} {body : List BExpr}
    {ns : List Nat} {np nr : Nat} {o : Option Nat}
    (hcs : cls.mapM (Interp.clauseCount Γ.tags I.env.mi) = some ns)
    (hbt : blockArity I.env.mi bt = some (np, nr)) (hle : np ≤ I.h)
    (hok : Interp.catchOk I.env.labels cls ns = true)
    (hb : Mor Γ ⟨I.env.push nr, np⟩ o body) (he : endsAt (some o) nr = true) :
    ∃ m : @Quiver.Hom (CObj Γ) _ I (Iface.mk I.env (I.h - np + nr)),
      m.1 = [.tryTable bt cls body] ∧
        ((denFunctor Γ).map m : PHom H Cfg ResP) = tryP bt cls (denL body) :=
  ⟨⟨_, rfl, mor_try hcs hbt hle hok hb he⟩, rfl, by
    show denL _ = _
    rw [denL_singleton, denT_try]⟩

end

end Silmaril.Wasm.Abstract.FunctorP
