module

public import Silmaril.Wasm.Abstract.ExposePStruct.Defs
public import Silmaril.Wasm.Abstract.Body.Thms
public import Silmaril.Wasm.Abstract.BodyTrace.Thms
import Silmaril.Proofs.Wasm.Abstract.ExposePStruct.Basic
import Silmaril.Proofs.Wasm.Abstract.ExposePStruct.Check
import Silmaril.Proofs.Wasm.Abstract.ExposePStruct.Image

/-!
# The structure of the exact F5 denotation, and its typed subcategory: theorems

The exact denotation `ExposeP.denListXP` of the canonical F5 semantics (`CallXP.EvalOXP`) is
structure-preserving, constructor by constructor, at every frame and stack.

**The exit-aware Kleisli category.** `denListXP_nil`, `denListXP_append`: the empty sequence
falls through, concatenation is sequencing that continues only after a fallthrough
(`ExposeP.thenKP`). `thenKP` is associative and unital (`thenKP_assoc`, `thenKP_unit`), so
`seqP` is a category with unit `idP` (`seqP_assoc`, `seqP_id_left`, `seqP_id_right`), and
`denL` is a functor from code under concatenation into it (`denL_nil`, `denL_append`).

**Constructors.** `denT_op`, `denT_block`, `denT_loop`, `denT_if`, `denT_try`: an operator after
its operands, a block and an `if` with the exit copairing `blockKP`, a `try_table` with `tryKP`,
a loop as the Elgot iteration of its step `loopStepP`; `denT_loop_unfold` is the fixpoint law.
A pending tail call passes every continuation (`thenKP_tail`, `blockKP_tail`, `loopKP_tail`,
`tryKP_tail`, `ifKP_tail`): it ends the body.

**Congruence for #299's quotient.** `BodyTrace.FullCollapseEquiv` (the same finished behaviours
up to trap ≈ divergence and the same pending calls) is a congruence for every constructor:
`seqP_congr`, `opP_congr`, `blockP_congr`, `loopP_congr`, `ifP_congr`, `tryP_congr`, and on
syntax `denL_append_congr`, `denT_block_congr`, `denT_loop_congr`, `denT_if_congr`,
`denT_try_congr`.

**The typed subcategory** (`Mor`, `Hom`, objects `Iface`; see Defs for the scope). Typed code is
closed under the identity (`mor_id`), composition (`mor_comp`, `hom_comp`; after a morphism to
the never-falls-through target, anything: `mor_stop`), operators (`mor_op`, `mor_op_stop`),
`block`, `loop`, `if`, `try_table` (`mor_block`, `mor_loop`, `mor_if`, `mor_try`) with their
arity premises, the call forms (`mor_call`, `mor_callIndirect`, `mor_callRef`), the tail calls,
which end a morphism at the never-falls-through target (`mor_returnCall`,
`mor_returnCallIndirect`, `mor_returnCallRef`), and `throw`/`throw_ref` (`mor_throw`,
`mor_throwRef`). Every typed problem (`Interp.TypedP`) is typed code in its store's context
(`typedP_mor`).

**Image closure.** The image `DenMor` of typed code under the denotation is closed under the
operations on bodies: `idP_mem`, `seqP_mem`, `seqP_stop_mem` (exit-aware Kleisli
composition), `opP_mem`, `blockP_mem`, `ifP_mem`, `tryP_mem` (exit copairing), `loopP_mem`
(Elgot iteration). Elgot laws hold of the denoted loops (`denT_loop_unfold`, `seqP_loopP`:
naturality, code after a loop is the loop's exit continuation; `loopP_uniform`: uniformity);
every law of `Body.bodyOps_lawful` holds for the denoted morphisms, which are morphisms of
`BodyM`. No closure hypothesis is assumed: the code witnessing each image is given.
-/

public section

namespace Silmaril.Wasm.Abstract.ExposePStruct

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Abstract.BodyTrace
open Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
open Silmaril.Wasm.Abstract.ExposeP
open Silmaril.Wasm.Abstract.CallXT (typeArity)
open Silmaril.Wasm.Interp

variable {H : Type}

/-! ## The exit-aware Kleisli category -/

/-- The empty sequence falls through. -/
theorem denListXP_nil (f : Frame) (stk : List Val) :
    (denListXP (H := H) [] f stk) = pure ⟨(f, .flow (.normal stk))⟩ :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.denListXP_nil f stk

/-- **Composition**: concatenation is exit-aware sequencing. -/
theorem denListXP_append (es₁ es₂ : List BExpr) (f : Frame) (stk : List Val) :
    (denListXP (H := H) (es₁ ++ es₂) f stk) = denListXP es₁ f stk >>= thenKP (denListXP es₂) :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.denListXP_append es₁ es₂ f stk

/-- A one-tree sequence is the tree. -/
theorem denListXP_singleton (e : BExpr) (f : Frame) (stk : List Val) :
    (denListXP (H := H) [e] f stk) = denXP e f stk :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.denListXP_singleton e f stk

/-- `thenKP` continues after a fallthrough. -/
theorem thenKP_normal (k : Frame → List Val → M (CallSig H) H ResP) (f : Frame)
    (stk : List Val) : thenKP k ⟨(f, .flow (.normal stk))⟩ = k f stk := rfl

/-- The right unit of `thenKP`: continuing with a fallthrough. -/
theorem thenKP_unit (r : ResP) :
    thenKP (H := H) (fun f stk => pure ⟨(f, .flow (.normal stk))⟩) r = pure r :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.thenKP_unit r

/-- Associativity of `thenKP`. -/
theorem thenKP_assoc (k k' : Frame → List Val → M (CallSig H) H ResP) (r : ResP) :
    (thenKP k r >>= thenKP k') = thenKP (fun f stk => k f stk >>= thenKP k') r :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.thenKP_assoc k k' r

theorem seqP_id_left (g : PHom H Cfg ResP) : seqP idP g = g :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.seqP_id_left g

theorem seqP_id_right (g : PHom H Cfg ResP) : seqP g idP = g :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.seqP_id_right g

theorem seqP_assoc (g₁ g₂ g₃ : PHom H Cfg ResP) : seqP (seqP g₁ g₂) g₃ = seqP g₁ (seqP g₂ g₃) :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.seqP_assoc g₁ g₂ g₃

/-- The empty sequence denotes the identity. -/
theorem denL_nil : (denL (H := H) []) = idP := Silmaril.Proofs.Wasm.Abstract.ExposePStruct.denL_nil

/-- **Functoriality**: concatenation denotes exit-aware composition. -/
theorem denL_append (es₁ es₂ : List BExpr) :
    (denL (H := H) (es₁ ++ es₂)) = seqP (denL es₁) (denL es₂) :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.denL_append es₁ es₂

theorem denL_cons (e : BExpr) (es : List BExpr) :
    (denL (H := H) (e :: es)) = seqP (denT e) (denL es) :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.denL_cons e es

theorem denL_singleton (e : BExpr) : (denL (H := H) [e]) = denT e :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.denL_singleton e

/-! ## Constructors -/

theorem denT_op (i : Instr) (args : List BExpr) :
    (denT (H := H) (.op i args)) = opP i (denL args) :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.denT_op i args

theorem denT_block (bt : BlockType) (body : List BExpr) :
    (denT (H := H) (.block bt body)) = blockP bt (denL body) :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.denT_block bt body

/-- A loop is the Elgot iteration of its step. -/
theorem denT_loop (bt : BlockType) (body : List BExpr) :
    (denT (H := H) (.loop bt body)) = Silmaril.Elgot.iter (loopStepP bt (denL body)) :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.denT_loop bt body

/-- The loop step of the denotation is `ExposeP.loopBodyXP`. -/
theorem loopStepP_denL (bt : BlockType) (body : List BExpr) :
    (loopStepP (H := H) bt (denL body)) = loopBodyXP bt body := rfl

theorem denT_if (bt : BlockType) (c t el : List BExpr) :
    (denT (H := H) (.if_ bt c t el)) = ifP bt (denL c) (denL t) (denL el) :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.denT_if bt c t el

theorem denT_try (bt : BlockType) (cs : List Catch) (body : List BExpr) :
    (denT (H := H) (.tryTable bt cs body)) = tryP bt cs (denL body) :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.denT_try bt cs body

/-- **The fixpoint law, transferred**: a loop unfolds once. -/
theorem denT_loop_unfold (bt : BlockType) (body : List BExpr) :
    (denT (H := H) (.loop bt body)) =
      fun c => loopStepP bt (denL body) c >>= Sum.elim pure (denT (.loop bt body)) := by
  rw [denT_loop]; exact Silmaril.Proofs.Wasm.Abstract.ExposePStruct.loopP_unfold bt _

/-! ## Pending tail calls pass -/

theorem thenKP_tail (k : Frame → List Val → M (CallSig H) H ResP) (f : Frame) (a : Nat)
    (args : List Val) (n : Nat) : thenKP k ⟨(f, .tail a args n)⟩ = pure ⟨(f, .tail a args n)⟩ :=
  rfl

theorem blockKP_tail (np nr : Nat) (stk : List Val) (f : Frame) (a : Nat) (args : List Val)
    (n : Nat) :
    (blockKP (H := H) np nr stk ⟨(f, .tail a args n)⟩) = pure ⟨(f, .tail a args n)⟩ := rfl

theorem loopKP_tail (np nr : Nat) (stk : List Val) (f : Frame) (a : Nat) (args : List Val)
    (n : Nat) :
    (loopKP (H := H) np nr stk ⟨(f, .tail a args n)⟩) = pure (.inl ⟨(f, .tail a args n)⟩) := rfl

theorem tryKP_tail (np nr : Nat) (stk : List Val) (cs : List Catch) (f : Frame) (a : Nat)
    (args : List Val) (n : Nat) :
    (tryKP (H := H) np nr stk cs ⟨(f, .tail a args n)⟩) = pure ⟨(f, .tail a args n)⟩ := rfl

theorem ifKP_tail (bt : BlockType) (gt ge : PHom H Cfg ResP) (f : Frame) (a : Nat)
    (args : List Val) (n : Nat) : ifKP bt gt ge ⟨(f, .tail a args n)⟩ = pure ⟨(f, .tail a args n)⟩ :=
  rfl

/-! ## Congruence for the observable quotient -/

theorem seqP_congr {g₁ g₁' g₂ g₂' : PHom H Cfg ResP} (h₁ : FullCollapseEquiv g₁ g₁')
    (h₂ : FullCollapseEquiv g₂ g₂') : FullCollapseEquiv (seqP g₁ g₂) (seqP g₁' g₂') :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.seqP_congr h₁ h₂

theorem opP_congr (i : Instr) {g g' : PHom H Cfg ResP} (h : FullCollapseEquiv g g') :
    FullCollapseEquiv (opP i g) (opP i g') :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.opP_congr i h

theorem blockP_congr (bt : BlockType) {g g' : PHom H Cfg ResP} (h : FullCollapseEquiv g g') :
    FullCollapseEquiv (blockP bt g) (blockP bt g') :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.blockP_congr bt h

theorem loopP_congr (bt : BlockType) {g g' : PHom H Cfg ResP} (h : FullCollapseEquiv g g') :
    FullCollapseEquiv (loopP bt g) (loopP bt g') :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.loopP_congr bt h

theorem ifP_congr (bt : BlockType) {gc gc' gt gt' ge ge' : PHom H Cfg ResP}
    (hc : FullCollapseEquiv gc gc') (ht : FullCollapseEquiv gt gt')
    (he : FullCollapseEquiv ge ge') : FullCollapseEquiv (ifP bt gc gt ge) (ifP bt gc' gt' ge') :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.ifP_congr bt hc ht he

theorem tryP_congr (bt : BlockType) (cs : List Catch) {g g' : PHom H Cfg ResP}
    (h : FullCollapseEquiv g g') : FullCollapseEquiv (tryP bt cs g) (tryP bt cs g') :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.tryP_congr bt cs h

/-- Sequences of equivalent code are equivalent. -/
theorem denL_append_congr {es₁ es₁' es₂ es₂' : List BExpr}
    (h₁ : FullCollapseEquiv (denL (H := H) es₁) (denL es₁'))
    (h₂ : FullCollapseEquiv (denL (H := H) es₂) (denL es₂')) :
    FullCollapseEquiv (denL (H := H) (es₁ ++ es₂)) (denL (es₁' ++ es₂')) := by
  rw [denL_append, denL_append]; exact seqP_congr h₁ h₂

theorem denT_block_congr (bt : BlockType) {body body' : List BExpr}
    (h : FullCollapseEquiv (denL (H := H) body) (denL body')) :
    FullCollapseEquiv (denT (H := H) (.block bt body)) (denT (.block bt body')) := by
  rw [denT_block, denT_block]; exact blockP_congr bt h

theorem denT_loop_congr (bt : BlockType) {body body' : List BExpr}
    (h : FullCollapseEquiv (denL (H := H) body) (denL body')) :
    FullCollapseEquiv (denT (H := H) (.loop bt body)) (denT (.loop bt body')) := by
  rw [denT_loop, denT_loop]; exact loopP_congr bt h

theorem denT_if_congr (bt : BlockType) {c c' t t' el el' : List BExpr}
    (hc : FullCollapseEquiv (denL (H := H) c) (denL c'))
    (ht : FullCollapseEquiv (denL (H := H) t) (denL t'))
    (he : FullCollapseEquiv (denL (H := H) el) (denL el')) :
    FullCollapseEquiv (denT (H := H) (.if_ bt c t el)) (denT (.if_ bt c' t' el')) := by
  rw [denT_if, denT_if]; exact ifP_congr bt hc ht he

theorem denT_try_congr (bt : BlockType) (cs : List Catch) {body body' : List BExpr}
    (h : FullCollapseEquiv (denL (H := H) body) (denL body')) :
    FullCollapseEquiv (denT (H := H) (.tryTable bt cs body)) (denT (.tryTable bt cs body')) := by
  rw [denT_try, denT_try]; exact tryP_congr bt cs h

theorem denT_op_congr (i : Instr) {args args' : List BExpr}
    (h : FullCollapseEquiv (denL (H := H) args) (denL args')) :
    FullCollapseEquiv (denT (H := H) (.op i args)) (denT (.op i args')) := by
  rw [denT_op, denT_op]; exact opP_congr i h

/-! ## The typed subcategory: closure -/

variable {Γ : Ctx H}

theorem mor_id (I : Iface) : Mor Γ I (some I.h) [] := rfl

theorem mor_comp {I : Iface} {k : Nat} {o : Option Nat} {es₁ es₂ : List BExpr}
    (h₁ : Mor Γ I (some k) es₁) (h₂ : Mor Γ ⟨I.env, k⟩ o es₂) : Mor Γ I o (es₁ ++ es₂) :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.mor_comp h₁ h₂

/-- Code after a morphism that never falls through is dead: the composite never falls
through. -/
theorem mor_stop {I : Iface} {es₁ : List BExpr} (h₁ : Mor Γ I none es₁) (es₂ : List BExpr) :
    Mor Γ I none (es₁ ++ es₂) :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.mor_stop h₁ es₂

theorem hom_id (I : Iface) : Hom Γ I I [] := ⟨rfl, rfl⟩

theorem hom_comp {I J K : Iface} {es₁ es₂ : List BExpr} (h₁ : Hom Γ I J es₁)
    (h₂ : Hom Γ J K es₂) : Hom Γ I K (es₁ ++ es₂) :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.hom_comp h₁ h₂

theorem mor_op {I : Iface} {i : Instr} {args : List BExpr} {h₁ : Nat} {o : Option Nat}
    (ha : Mor Γ I (some h₁) args)
    (hi : flatChkE (ehExt Γ.tags) Γ.funcs I.env.mi I.env.nl I.env.ret I.env.labels h₁ i = some o) :
    Mor Γ I o [.op i args] :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.mor_op ha hi

theorem mor_op_stop {I : Iface} {i : Instr} {args : List BExpr} (ha : Mor Γ I none args) :
    Mor Γ I none [.op i args] :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.mor_op_stop ha

theorem mor_block {I : Iface} {bt : BlockType} {body : List BExpr} {np nr : Nat}
    {o : Option Nat} (hbt : blockArity I.env.mi bt = some (np, nr)) (hle : np ≤ I.h)
    (hb : Mor Γ ⟨I.env.push nr, np⟩ o body) (he : endsAt (some o) nr = true) :
    Mor Γ I (some (I.h - np + nr)) [.block bt body] :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.mor_block hbt hle hb he

theorem mor_loop {I : Iface} {bt : BlockType} {body : List BExpr} {np nr : Nat}
    {o : Option Nat} (hbt : blockArity I.env.mi bt = some (np, nr)) (hle : np ≤ I.h)
    (hb : Mor Γ ⟨I.env.push np, np⟩ o body) (he : endsAt (some o) nr = true) :
    Mor Γ I (some (I.h - np + nr)) [.loop bt body] :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.mor_loop hbt hle hb he

theorem mor_if {I : Iface} {bt : BlockType} {c t el : List BExpr} {h₁ np nr : Nat}
    {ot oe : Option Nat} (hc : Mor Γ I (some h₁) c) (hbt : blockArity I.env.mi bt = some (np, nr))
    (hle : np + 1 ≤ h₁) (ht : Mor Γ ⟨I.env.push nr, np⟩ ot t) (het : endsAt (some ot) nr = true)
    (he : Mor Γ ⟨I.env.push nr, np⟩ oe el) (hee : endsAt (some oe) nr = true) :
    Mor Γ I (some (h₁ - 1 - np + nr)) [.if_ bt c t el] :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.mor_if hc hbt hle ht het he hee

theorem mor_try {I : Iface} {bt : BlockType} {cs : List Catch} {body : List BExpr}
    {ns : List Nat} {np nr : Nat} {o : Option Nat}
    (hcs : cs.mapM (clauseCount Γ.tags I.env.mi) = some ns)
    (hbt : blockArity I.env.mi bt = some (np, nr)) (hle : np ≤ I.h)
    (hok : catchOk I.env.labels cs ns = true)
    (hb : Mor Γ ⟨I.env.push nr, np⟩ o body) (he : endsAt (some o) nr = true) :
    Mor Γ I (some (I.h - np + nr)) [.tryTable bt cs body] :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.mor_try hcs hbt hle hok hb he

/-- A direct call pops its parameters and pushes its results. -/
theorem mor_call {I : Iface} {x : FuncIdx} {p q : Nat}
    (hx : callArity Γ.funcs I.env.mi x = some (p, q)) (hle : p ≤ I.h) :
    Mor Γ I (some (I.h - p + q)) [.op (.call x) []] :=
  mor_op (mor_id I) (Silmaril.Proofs.Wasm.Abstract.ExposePStruct.flat_call hx hle)

theorem mor_callIndirect {I : Iface} {x : TableIdx} {y : TypeIdx} {p q : Nat}
    (hy : typeArity I.env.mi y = some (p, q)) (hle : p + 1 ≤ I.h) :
    Mor Γ I (some (I.h - (p + 1) + q)) [.op (.callIndirect x y) []] :=
  mor_op (mor_id I) (Silmaril.Proofs.Wasm.Abstract.ExposePStruct.flat_callIndirect hy hle)

theorem mor_callRef {I : Iface} {y : TypeIdx} {p q : Nat}
    (hy : typeArity I.env.mi y = some (p, q)) (hle : p + 1 ≤ I.h) :
    Mor Γ I (some (I.h - (p + 1) + q)) [.op (.callRef y) []] :=
  mor_op (mor_id I) (Silmaril.Proofs.Wasm.Abstract.ExposePStruct.flat_callRef hy hle)

/-- **A tail call ends a morphism**: at the never-falls-through target, its callee's results
being the function's. -/
theorem mor_returnCall {I : Iface} {x : FuncIdx} {p : Nat}
    (hx : callArity Γ.funcs I.env.mi x = some (p, I.env.ret)) (hle : p ≤ I.h) :
    Mor Γ I none [.op (.returnCall x) []] :=
  mor_op (mor_id I) (Silmaril.Proofs.Wasm.Abstract.ExposePStruct.flat_returnCall hx hle)

theorem mor_returnCallIndirect {I : Iface} {x : TableIdx} {y : TypeIdx} {p : Nat}
    (hy : typeArity I.env.mi y = some (p, I.env.ret)) (hle : p + 1 ≤ I.h) :
    Mor Γ I none [.op (.returnCallIndirect x y) []] :=
  mor_op (mor_id I) (Silmaril.Proofs.Wasm.Abstract.ExposePStruct.flat_returnCallIndirect hy hle)

theorem mor_returnCallRef {I : Iface} {y : TypeIdx} {p : Nat}
    (hy : typeArity I.env.mi y = some (p, I.env.ret)) (hle : p + 1 ≤ I.h) :
    Mor Γ I none [.op (.returnCallRef y) []] :=
  mor_op (mor_id I) (Silmaril.Proofs.Wasm.Abstract.ExposePStruct.flat_returnCallRef hy hle)

theorem mor_throw {I : Iface} {x : TagIdx} {p : Nat}
    (hx : tagFields Γ.tags I.env.mi x = some p) (hle : p ≤ I.h) :
    Mor Γ I none [.op (.throw x) []] :=
  mor_op (mor_id I) (Silmaril.Proofs.Wasm.Abstract.ExposePStruct.flat_throw hx hle)

theorem mor_throwRef {I : Iface} (hle : 1 ≤ I.h) : Mor Γ I none [.op .throwRef []] :=
  mor_op (mor_id I) (Silmaril.Proofs.Wasm.Abstract.ExposePStruct.flat_throwRef hle)

theorem mor_br {I : Iface} {l : LabelIdx} {n : Nat} (hl : I.env.labels[l.toNat]? = some n)
    (hle : n ≤ I.h) : Mor Γ I none [.op (.br l) []] :=
  mor_op (mor_id I) (Silmaril.Proofs.Wasm.Abstract.ExposePStruct.flat_br hl hle)

theorem mor_return {I : Iface} (hle : I.env.ret ≤ I.h) : Mor Γ I none [.op .return_ []] :=
  mor_op (mor_id I) (Silmaril.Proofs.Wasm.Abstract.ExposePStruct.flat_return hle)

/-- **Typed problems are typed code**: a `TypedP tags` configuration's code is a morphism from
its interface, in the context of its store, which the store satisfies. -/
theorem typedP_mor {tags : List TagInst} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} (ht : TypedP tags s f stk es) :
    ∃ (hS : StoreChkE (ehExt tags) s.funcs) (labels : List Nat) (ret : Nat) (o : Option Nat),
      Mor ⟨tags, s.funcs, hS⟩ (ifaceOf f ret labels stk) o es ∧
        Ctx.Good ⟨tags, s.funcs, hS⟩ s :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.typedP_mor ht

/-! ## Image closure -/

theorem idP_mem (I : Iface) : (idP : PHom H Cfg ResP) ∈ DenMor Γ I (some I.h) :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.idP_mem I

/-- Composition of denoted morphisms is denoted (by the concatenation). -/
theorem seqP_mem {I : Iface} {k : Nat} {o : Option Nat} {g₁ g₂ : PHom H Cfg ResP}
    (h₁ : g₁ ∈ DenMor Γ I (some k)) (h₂ : g₂ ∈ DenMor Γ ⟨I.env, k⟩ o) :
    seqP g₁ g₂ ∈ DenMor Γ I o :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.seqP_mem h₁ h₂

theorem seqP_stop_mem {I : Iface} {g₁ : PHom H Cfg ResP} (h₁ : g₁ ∈ DenMor Γ I none)
    (es₂ : List BExpr) : seqP g₁ (denL es₂) ∈ DenMor Γ I none :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.seqP_stop_mem h₁ es₂

theorem opP_mem {I : Iface} {i : Instr} {h₁ : Nat} {o : Option Nat} {g : PHom H Cfg ResP}
    (hg : g ∈ DenMor Γ I (some h₁))
    (hi : flatChkE (ehExt Γ.tags) Γ.funcs I.env.mi I.env.nl I.env.ret I.env.labels h₁ i = some o) :
    opP i g ∈ DenMor Γ I o :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.opP_mem hg hi

theorem opP_stop_mem {I : Iface} {i : Instr} {g : PHom H Cfg ResP} (hg : g ∈ DenMor Γ I none) :
    opP i g ∈ DenMor Γ I none :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.opP_stop_mem hg

/-- The exit copairing of a denoted body is denoted (by the block). -/
theorem blockP_mem {I : Iface} {bt : BlockType} {np nr : Nat} {o : Option Nat}
    {g : PHom H Cfg ResP} (hbt : blockArity I.env.mi bt = some (np, nr)) (hle : np ≤ I.h)
    (hg : g ∈ DenMor Γ ⟨I.env.push nr, np⟩ o) (he : endsAt (some o) nr = true) :
    blockP bt g ∈ DenMor Γ I (some (I.h - np + nr)) :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.blockP_mem hbt hle hg he

/-- The Elgot iteration of a denoted loop step is denoted (by the loop). -/
theorem loopP_mem {I : Iface} {bt : BlockType} {np nr : Nat} {o : Option Nat}
    {g : PHom H Cfg ResP} (hbt : blockArity I.env.mi bt = some (np, nr)) (hle : np ≤ I.h)
    (hg : g ∈ DenMor Γ ⟨I.env.push np, np⟩ o) (he : endsAt (some o) nr = true) :
    loopP bt g ∈ DenMor Γ I (some (I.h - np + nr)) :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.loopP_mem hbt hle hg he

theorem ifP_mem {I : Iface} {bt : BlockType} {h₁ np nr : Nat} {ot oe : Option Nat}
    {gc gt ge : PHom H Cfg ResP} (hc : gc ∈ DenMor Γ I (some h₁))
    (hbt : blockArity I.env.mi bt = some (np, nr)) (hle : np + 1 ≤ h₁)
    (ht : gt ∈ DenMor Γ ⟨I.env.push nr, np⟩ ot) (het : endsAt (some ot) nr = true)
    (he : ge ∈ DenMor Γ ⟨I.env.push nr, np⟩ oe) (hee : endsAt (some oe) nr = true) :
    ifP bt gc gt ge ∈ DenMor Γ I (some (h₁ - 1 - np + nr)) :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.ifP_mem hc hbt hle ht het he hee

/-- The handler copairing of a denoted body is denoted (by the `try_table`). -/
theorem tryP_mem {I : Iface} {bt : BlockType} {cs : List Catch} {ns : List Nat} {np nr : Nat}
    {o : Option Nat} {g : PHom H Cfg ResP}
    (hcs : cs.mapM (clauseCount Γ.tags I.env.mi) = some ns)
    (hbt : blockArity I.env.mi bt = some (np, nr)) (hle : np ≤ I.h)
    (hok : catchOk I.env.labels cs ns = true)
    (hg : g ∈ DenMor Γ ⟨I.env.push nr, np⟩ o) (he : endsAt (some o) nr = true) :
    tryP bt cs g ∈ DenMor Γ I (some (I.h - np + nr)) :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.tryP_mem hcs hbt hle hok hg he

/-- **Naturality, transferred**: code after a loop is its exit continuation. -/
theorem seqP_loopP (bt : BlockType) (g g₂ : PHom H Cfg ResP) :
    seqP (loopP bt g) g₂ =
      Silmaril.Elgot.iter (Silmaril.Elgot.mapReturn (loopStepP bt g) (contP g₂)) :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.seqP_loopP bt g g₂

/-- **Uniformity, transferred.** -/
theorem loopP_uniform (bt : BlockType) (g : PHom H Cfg ResP) {C : Type 1}
    (G : C → M (CallSig H) H (ResP ⊕ C)) (h : Cfg → C)
    (comm : (loopStepP bt g >=> Silmaril.Elgot.liftPure (Sum.map id h)) =
      (Silmaril.Elgot.liftPure h >=> G)) :
    loopP bt g = (Silmaril.Elgot.liftPure h >=> Silmaril.Elgot.iter G) :=
  Silmaril.Proofs.Wasm.Abstract.ExposePStruct.loopP_uniform bt g G h comm

end Silmaril.Wasm.Abstract.ExposePStruct
