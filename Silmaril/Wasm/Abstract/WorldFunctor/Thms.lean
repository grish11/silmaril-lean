module

public import Silmaril.Wasm.Abstract.WorldFunctor.Defs
public import Silmaril.Wasm.Abstract.TypedFunctor.Thms
public import Silmaril.Wasm.Abstract.TypedCat.Thms
public import Silmaril.Wasm.Abstract.TypedCatFit.Thms
import Silmaril.Proofs.Wasm.Abstract.WorldFunctor.Rel
import Silmaril.Proofs.Wasm.Abstract.WorldFunctor.World

/-!
# The typed premonoidal Elgot functor of the supported checked fragment, in a world

**Domain: the world category `WObj Γ`.** A world is a context `Γ : Ctx H`: tag instances, the
store's functions, and the checker's acceptance `Γ.storeChk : StoreChkE (ehExt Γ.tags) Γ.funcs`.
The checker covers the integer, control, call and exception fragment only, so this is the
**supported checked fragment**, not all Core-valid Wasm: a store with a float, vector,
reference, table, memory, conversion or GC instruction in any function is in no world, and
extending the checker (and every proof below that reads it) to those forms is a separate
obligation. Objects: typed interfaces with valid stack types (`TIface.Ok`) coherent with the
world (`TypedCat.Coh`). Morphisms `I ⟶ J`: #572's `TQ Γ I J`, typed checked code
(`THom Γ I J es`: Core-typed `I.ts → J.ts` and accepted by the checker) **modulo the open
interaction equivalence** `OpEquivP`. Identity `[]`, composition concatenation (`tqComp`).

**The stack tensor** (`tensorW R hR`, for closed value types `R`, `ResultOk {} R`): on objects
`I ↦ I.withBelow R` (`R` below the stack), on morphisms the same code (`TypedCat.tmor_frame`);
a functor `WObj Γ ⥤ WObj Γ`. Its unitor and associator on objects are equalities
(`withBelow_nil`, `withBelow_withBelow`: list append).

**Codomain: `RObj Γ`.** The same objects; `RHom Γ I J`: relations of answered runs
(`TypedCat.ORel`) supported on the world states `WSt Γ I`, landing in `WSt Γ J`, trap-closed.
Identity `resR (WSt Γ I) idR`, composition `TypedCat.seqR`; the laws are #543's `seqR_idR_left`,
`seqR_idR_right`, `seqR_assoc`, with support and landing. Whiskering `whiskW R g`: run `g` on the
top `|I.ts|` values with the rest passive below (`TypedCat.leftR`, the `whiskO` of #543),
restricted to `WSt Γ (I.withBelow R)`; it keeps identities and composition (`whiskW_id`,
`whiskW_comp`). Iteration: `iterR` of a relational step (Defs), the least fixpoint of its
unfolding (`iterR_fix`, `iterR_least`).

**The world functor** `worldFunctor Γ : WObj Γ ⥤ RObj Γ`: a typed morphism `es` goes to
`resR (WSt Γ I) (Ans closedCallXP (denK es))`, which is `resR (WSt Γ I) (trapR (denR
closedCallXP es))` (`worldFunctor_map_mk`): its answered runs under the closure, from world
states, a trap's store and frame forgotten. Bundled with the preserved structure as
`worldElgot Γ : WorldElgot Γ`:

* `map_id`, `map_comp` (the functor's fields): exactly. Composition uses that typed code keeps
  the world (`thom_lands`, from the checker's result invariant `evalOXP_goodO_closed`);
* `map_whisker`: whiskering, exactly up to reading branches and returns at their target's arity
  (`trimR`), at every world state (`thom_whisker`, from `TypedCatFit.evalOXP_tensor_closed`).
  Without `trimR` it is false: a branch carries the whole stack, passive values included;
* `map_iter`: a typed loop goes to the iteration of its step (`denR_loop`: the loop's answered
  runs are exactly `iterR (loopStepR C bt body)`, for every oracle).

**Two corrections to the naive statement, both forced.** (1) *World states, not typed states.*
The restriction is to `WSt` (store agreeing with `Γ`, frame in the instance with the checked local
count, stack of the checked height), which contains every typed state (`realizes_wst`;
`worldFunctor_realizes`: on `Realizes` states the functor is exactly `trapR (denR closedCallXP
es)`). Exact `map_comp` restricted to `Realizes` states would need answered runs to *preserve*
`Realizes` (Core subject reduction carried through the `PendSim` bridge, frame and store typing
included), which is not proved; `WSt` is preserved by the checker's invariant alone. (2) *Traps
forget their store and frame* (`trapR`). The exact `BodyM` denotation, and so `OpEquivP`, records
a trap without store or frame (`ExposeP.evalOXP_trap_iff`), while `EvalOXP` records them; so
`es ↦ denR closedCallXP es` is not a function of the `OpEquivP` class (two codes setting a local
differently before `unreachable` have one exit-monad denotation and different `EvalOXP` frames),
and the functor sends `es` to the trap-forgetting `trapR (denR closedCallXP es)`.

**Factorization through the faithful functor.** `Ans C k` answers an arrow of the exit monad by
the oracle `C`: `ans_denK : Ans C (denK es) = trapR (denR C es)` for every oracle, by `ExposeP`'s
exactness (`evalOXP_iff`, `evalOXP_trap_iff`). So `worldFunctor_factor`: the world functor is
`Ans closedCallXP` (restricted to world states) after #572's `tmap`, the map on morphisms of
`worldTyped Γ = toTObj ⋙ typedFunctor Γ`, #572's typed Elgot functor, which is **faithful**
(`Functor.Faithful`, `worldTyped_map_injective`): injective modulo `OpEquivP`. Faithfulness
lives there. The world functor itself is **not** claimed faithful:
answering by the one oracle `closedCallXP` forgets behaviour under every other answer (a call to
an address with no function has no closed answer, so whatever follows it is invisible), and the
restriction to world states forgets the rest; only `worldFunctor_map_eq_of_tmap` (the kernel of
`tmap` is contained in that of `worldFunctor`) is stated, and no non-injectivity example is
formalized.

**Centrality.** Pure code is central in the image (`worldFunctor_pure_central`: a `PureAt`
denotation interchanges with every relation, #543's `interchange_of_pure` through `trapR`);
`premonoidal_not_monoidal` (#543's `not_interchange`, under a typed recording oracle) gives typed
morphisms that do not interchange: the structure is premonoidal, not monoidal.

**Scope.** Host-level Core faithfulness (the closed, host-answered semantics against Core 3.0
with hosts) awaits the H2 bridge and is not claimed.
-/

public section

namespace Silmaril.Wasm.Abstract.WorldFunctor

open CategoryTheory
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
open Silmaril.Wasm.Abstract.ExposeP Silmaril.Wasm.Abstract.ExposePStruct
open Silmaril.Wasm.Abstract.ExposePTyped Silmaril.Wasm.Abstract.TypedCat
open Silmaril.Wasm.Abstract.TypedFunctor
open Silmaril.Wasm.Abstract.CallXP (POut EvalOXP)
open Silmaril.Wasm.Abstract.XRecursionP (closedCallXP)
open Silmaril.Wasm.Validation (CValType ResultOk)
open Silmaril.Wasm.Abstract.FunctorP (OpEquivP)

variable {H : Type}

/-! ## 1. Relations: answering, traps, iteration, the loop -/

/-- **Answering the exit-monad denotation** by any oracle is the trap-forgetting answered
semantics (`ExposeP` exactness). -/
theorem ans_denK (C : Abstract.CallRel H) (es : List BExpr) :
    Ans C (denK es) = trapR (denR C es) :=
  Silmaril.Proofs.Wasm.Abstract.WorldFunctor.ans_denK C es

theorem trapR_idR : trapR (idR : ORel H) = idR :=
  Silmaril.Proofs.Wasm.Abstract.WorldFunctor.trapR_idR

theorem trapR_seqR (g₁ g₂ : ORel H) : trapR (seqR g₁ g₂) = seqR (trapR g₁) (trapR g₂) :=
  Silmaril.Proofs.Wasm.Abstract.WorldFunctor.trapR_seqR g₁ g₂

/-- **The fixpoint law**: the iteration is its own unfolding. -/
theorem iterR_fix (F : LStep H) : unfoldR F (iterR F) = iterR F := by
  funext s f stk s' f' o
  exact propext (Silmaril.Proofs.Wasm.Abstract.WorldFunctor.iterR_iff F).symm

/-- **Least**: the iteration is contained in every relation closed under unfolding. -/
theorem iterR_least (F : LStep H) {g : ORel H}
    (hg : ∀ s f stk s' f' o, unfoldR F g s f stk s' f' o → g s f stk s' f' o) :
    ∀ s f stk s' f' o, iterR F s f stk s' f' o → g s f stk s' f' o :=
  Silmaril.Proofs.Wasm.Abstract.WorldFunctor.iterR_least F hg

/-- **A loop denotes the iteration of its step**, under every oracle. -/
theorem denR_loop (C : Abstract.CallRel H) (bt : BlockType) (body : List BExpr) :
    denR C [.loop bt body] = iterR (loopStepR C bt body) :=
  Silmaril.Proofs.Wasm.Abstract.WorldFunctor.denR_loop C bt body

/-! ## 2. World states -/

/-- **Typed states are world states.** -/
theorem realizes_wst {Γ : Ctx H} {I : TIface} {s : Store H} {f : Frame} {stk : List Val}
    (hr : Realizes Γ I s f stk) : WSt Γ I s f stk :=
  Silmaril.Proofs.Wasm.Abstract.WorldFunctor.realizes_wst hr

/-- **Typed code keeps the world** under the closure. -/
theorem thom_lands {Γ : Ctx H} {I J : TIface} {es : List BExpr} (hm : THom Γ I J es)
    {s : Store H} {f : Frame} {stk : List Val} (hw : WSt Γ I s f stk) {s' : Store H}
    {f' : Frame} {vs : List Val}
    (d : EvalOXP closedCallXP s f stk es (s', f', .flow (.normal vs))) :
    WSt Γ J s' f' vs :=
  Silmaril.Proofs.Wasm.Abstract.WorldFunctor.thom_lands hm hw d

/-! ## Laws of the codomain -/

theorem resultOk_of_closed {Δ : Validation.TypeCtx} {R : List CValType} (hR : ResultOk {} R) :
    ResultOk Δ R :=
  Silmaril.Proofs.Wasm.Abstract.WorldFunctor.resultOk_of_closed hR

theorem withBelow_ok {I : TIface} (hI : I.Ok) {R : List CValType} (hR : ResultOk {} R) :
    (I.withBelow R).Ok :=
  Silmaril.Proofs.Wasm.Abstract.WorldFunctor.withBelow_ok hI hR

theorem idR_lands {Γ : Ctx H} {I : TIface} :
    ∀ s f stk s' f' vs, resR (WSt Γ I) idR s f stk s' f' (.flow (.normal vs)) →
      WSt Γ I s' f' vs :=
  Silmaril.Proofs.Wasm.Abstract.WorldFunctor.idR_lands

theorem idR_trap {Γ : Ctx H} {I : TIface} :
    ∀ s f stk s' f' s'' f'', resR (WSt Γ I) (idR : ORel H) s f stk s' f' (.flow .trap) →
      resR (WSt Γ I) idR s f stk s'' f'' (.flow .trap) :=
  Silmaril.Proofs.Wasm.Abstract.WorldFunctor.idR_trap

theorem seqR_supp {P : Store H → Frame → List Val → Prop} {g₁ : ORel H} (g₂ : ORel H)
    (h₁ : ∀ s f stk s' f' o, g₁ s f stk s' f' o → P s f stk) :
    ∀ s f stk s' f' o, seqR g₁ g₂ s f stk s' f' o → P s f stk :=
  Silmaril.Proofs.Wasm.Abstract.WorldFunctor.seqR_supp g₂ h₁

theorem seqR_lands {Q : Store H → Frame → List Val → Prop} (g₁ : ORel H) {g₂ : ORel H}
    (h₂ : ∀ s f stk s' f' vs, g₂ s f stk s' f' (.flow (.normal vs)) → Q s' f' vs) :
    ∀ s f stk s' f' vs, seqR g₁ g₂ s f stk s' f' (.flow (.normal vs)) → Q s' f' vs :=
  Silmaril.Proofs.Wasm.Abstract.WorldFunctor.seqR_lands g₁ h₂

theorem seqR_trap {g₁ g₂ : ORel H}
    (h₁ : TrapClosed g₁) (h₂ : TrapClosed g₂) :
    TrapClosed (seqR g₁ g₂) :=
  Silmaril.Proofs.Wasm.Abstract.WorldFunctor.seqR_trap h₁ h₂

/-- The restricted identity is a left unit on relations supported in the restriction. -/
theorem seqR_resR_idR_left (P : Store H → Frame → List Val → Prop) {g : ORel H}
    (hs : ∀ s f stk s' f' o, g s f stk s' f' o → P s f stk) : seqR (resR P idR) g = g :=
  Silmaril.Proofs.Wasm.Abstract.WorldFunctor.seqR_resR_idR_left P hs

/-- The restricted identity is a right unit on relations landing in the restriction. -/
theorem seqR_resR_idR_right (Q : Store H → Frame → List Val → Prop) {g : ORel H}
    (hl : ∀ s f stk s' f' vs, g s f stk s' f' (.flow (.normal vs)) → Q s' f' vs) :
    seqR g (resR Q idR) = g :=
  Silmaril.Proofs.Wasm.Abstract.WorldFunctor.seqR_resR_idR_right Q hl

theorem whisk_lands {Γ : Ctx H} {I J : TIface} (R : List CValType) {g : ORel H}
    (hl : ∀ s f stk s' f' vs, g s f stk s' f' (.flow (.normal vs)) → WSt Γ J s' f' vs) :
    ∀ s f stk s' f' vs, resR (WSt Γ (I.withBelow R)) (leftR I.ts.length g) s f stk s' f'
      (.flow (.normal vs)) → WSt Γ (J.withBelow R) s' f' vs :=
  Silmaril.Proofs.Wasm.Abstract.WorldFunctor.whisk_lands R hl

theorem whisk_trap {Γ : Ctx H} {I : TIface} (R : List CValType) (n : Nat) {g : ORel H}
    (ht : TrapClosed g) :
    TrapClosed (resR (WSt Γ (I.withBelow R)) (leftR n g)) :=
  Silmaril.Proofs.Wasm.Abstract.WorldFunctor.whisk_trap R n ht

/-- Typed code lands in the world, answered by the closure. -/
theorem ans_lands {Γ : Ctx H} {I J : TIface} {es : List BExpr} (hm : THom Γ I J es) :
    ∀ s f stk s' f' vs, resR (WSt Γ I) (Ans closedCallXP (denK es)) s f stk s' f'
      (.flow (.normal vs)) → WSt Γ J s' f' vs :=
  Silmaril.Proofs.Wasm.Abstract.WorldFunctor.gRel_lands hm

theorem ans_nil {Γ : Ctx H} (I : TIface) :
    resR (WSt Γ I) (Ans closedCallXP (denK (H := H) [])) = resR (WSt Γ I) idR :=
  Silmaril.Proofs.Wasm.Abstract.WorldFunctor.gRel_nil I

theorem ans_append {Γ : Ctx H} {I J : TIface} {es₁ : List BExpr} (h₁ : THom Γ I J es₁)
    (es₂ : List BExpr) :
    resR (WSt Γ I) (Ans closedCallXP (denK (es₁ ++ es₂))) =
      seqR (resR (WSt Γ I) (Ans closedCallXP (denK es₁)))
        (resR (WSt Γ J) (Ans closedCallXP (denK es₂))) :=
  Silmaril.Proofs.Wasm.Abstract.WorldFunctor.gRel_append h₁ es₂

/-! ## 3. The world category -/

/-- **The world category**: typed coherent interfaces, typed checked code modulo `OpEquivP`. -/
instance (Γ : Ctx H) : Category (WObj Γ) where
  Hom I J := TQ Γ I.1 J.1
  id I := Quotient.mk _ ⟨[], thom_id I.2.1⟩
  comp := tqComp
  id_comp q := by
    induction q using Quotient.inductionOn
    rfl
  comp_id q := by
    induction q using Quotient.inductionOn with
    | h m => exact congrArg (Quotient.mk _) (Subtype.ext (List.append_nil m.1))
  assoc q₁ q₂ q₃ := by
    induction q₁ using Quotient.inductionOn
    induction q₂ using Quotient.inductionOn
    induction q₃ using Quotient.inductionOn with
    | h m₃ => exact congrArg (Quotient.mk _) (Subtype.ext (List.append_assoc _ _ _))

/-- Forget coherence: the world category into #572's typed category. -/
@[expose] def toTObj (Γ : Ctx H) : WObj Γ ⥤ TObj Γ where
  obj I := ⟨I.1, I.2.1⟩
  map q := q
  map_id _ := rfl
  map_comp _ _ := rfl

instance (Γ : Ctx H) : (toTObj Γ).Faithful where
  map_injective h := h

/-- **#572's typed Elgot functor on the world category.** -/
@[expose] noncomputable def worldTyped (Γ : Ctx H) : WObj Γ ⥤ SingleObj (TMon Γ) :=
  toTObj Γ ⋙ typedFunctor Γ

/-- **It is faithful** (injective modulo `OpEquivP`). -/
instance (Γ : Ctx H) : (worldTyped Γ).Faithful := by
  unfold worldTyped; infer_instance

/-! ## 4. The stack tensor of the world category -/

/-- The interface with closed value types `R` below its stack is a world object. -/
@[expose] def tensorObj {Γ : Ctx H} (R : List CValType) (hR : ResultOk {} R) (I : WObj Γ) :
    WObj Γ :=
  ⟨I.1.withBelow R, withBelow_ok I.2.1 hR,
    ⟨I.2.2.types, I.2.2.funcs, I.2.2.tags⟩⟩

/-- The same code, typed with `R` below (`tmor_frame`). -/
@[expose] def tensorMap {Γ : Ctx H} (R : List CValType) (hR : ResultOk {} R) {I J : TIface} :
    TQ Γ I J → TQ Γ (I.withBelow R) (J.withBelow R) :=
  Quotient.map
    (fun m => ⟨m.1, tmor_frame m.2
      (resultOk_of_closed hR)⟩)
    fun _ _ h => h

/-- **The stack tensor `- ⊗ R` is a functor** of the world category. -/
@[expose] def tensorW {Γ : Ctx H} (R : List CValType) (hR : ResultOk {} R) : WObj Γ ⥤ WObj Γ where
  obj := tensorObj R hR
  map q := tensorMap R hR q
  map_id _ := rfl
  map_comp q₁ q₂ := by
    induction q₁ using Quotient.inductionOn
    induction q₂ using Quotient.inductionOn
    rfl

/-- The tensor is the same code. -/
theorem tensorW_map_mk {Γ : Ctx H} (R : List CValType) (hR : ResultOk {} R) {I J : WObj Γ}
    (m : THomE Γ I.1 J.1) :
    (tensorW R hR).map (Quotient.mk _ m : I ⟶ J) =
      (Quotient.mk _ ⟨m.1, tmor_frame m.2
        (resultOk_of_closed hR)⟩ :
        TQ Γ (I.1.withBelow R) (J.1.withBelow R)) := rfl

/-- **The unitor**, on objects: nothing below. -/
theorem withBelow_nil (I : TIface) : I.withBelow [] = I := rfl

/-- **The associator**, on objects: list append. -/
theorem withBelow_withBelow (I : TIface) (R₁ R₂ : List CValType) :
    (I.withBelow R₁).withBelow R₂ = I.withBelow (R₂ ++ R₁) := by
  simp [TIface.withBelow]

/-! ## 5. The codomain -/

/-- **The relational codomain**: relations of answered runs from world states to world states,
trap-closed, composed by exit-aware composition. -/
instance (Γ : Ctx H) : Category (RObj Γ) where
  Hom I J := RHom Γ I.1 J.1
  id I := ⟨resR (WSt Γ I.1) idR, fun _ _ _ _ _ _ h => h.1,
    idR_lands,
    idR_trap⟩
  comp g₁ g₂ := ⟨seqR g₁.rel g₂.rel,
    seqR_supp _ g₁.supp,
    seqR_lands _ g₂.lands,
    seqR_trap g₁.trap g₂.trap⟩
  id_comp g := RHom.ext
    (seqR_resR_idR_left _ g.supp)
  comp_id g := RHom.ext
    (seqR_resR_idR_right _ g.lands)
  assoc g₁ g₂ g₃ := RHom.ext (seqR_assoc g₁.rel g₂.rel g₃.rel)

theorem rObj_comp_rel {Γ : Ctx H} {I J K : RObj Γ} (g₁ : I ⟶ J) (g₂ : J ⟶ K) :
    RHom.rel (g₁ ≫ g₂) = seqR (RHom.rel g₁) (RHom.rel g₂) := rfl

theorem rObj_id_rel {Γ : Ctx H} (I : RObj Γ) : RHom.rel (𝟙 I) = resR (WSt Γ I.1) idR := rfl

/-- **The codomain's whiskering** `g ⋉ R`: `g` on the top `|I.ts|` values, the rest passive below
(#543's `leftR`), at the world states of `I` with `R` below. -/
@[expose] def whiskW {Γ : Ctx H} (R : List CValType) {I J : TIface} (g : RHom Γ I J) :
    RHom Γ (I.withBelow R) (J.withBelow R) :=
  ⟨resR (WSt Γ (I.withBelow R)) (leftR I.ts.length g.rel),
    fun _ _ _ _ _ _ h => h.1,
    whisk_lands R g.lands,
    whisk_trap R _ g.trap⟩

/-- **The codomain's whiskering keeps identities.** -/
theorem whiskW_id {Γ : Ctx H} (R : List CValType) (I : RObj Γ) :
    (whiskW R (𝟙 I)).rel = resR (WSt Γ (I.1.withBelow R)) idR :=
  Silmaril.Proofs.Wasm.Abstract.WorldFunctor.whisk_idR I.1 R

/-- **The codomain's whiskering keeps composition.** -/
theorem whiskW_comp {Γ : Ctx H} (R : List CValType) {I J K : RObj Γ} (g₁ : I ⟶ J) (g₂ : J ⟶ K) :
    (whiskW R (g₁ ≫ g₂)).rel = seqR (whiskW R g₁).rel (whiskW R g₂).rel :=
  Silmaril.Proofs.Wasm.Abstract.WorldFunctor.whisk_seqR R g₂.rel g₁.lands

/-! ## 6. The world functor -/

/-- The answered runs of a typed morphism under the closure, from world states. -/
@[expose] noncomputable def gHom {Γ : Ctx H} {I J : TIface} (m : THomE Γ I J) : RHom Γ I J :=
  ⟨resR (WSt Γ I) (Ans closedCallXP (denK m.1)),
    fun _ _ _ _ _ _ h => h.1,
    ans_lands m.2,
    fun _ _ _ _ _ _ _ h => h⟩

/-- On `OpEquivP` classes: the answered runs depend on the exit-monad denotation only. -/
@[expose] noncomputable def gMap {Γ : Ctx H} {I J : TIface} : TQ Γ I J → RHom Γ I J :=
  Quotient.lift gHom fun a b h => RHom.ext (by
    change resR _ (Ans _ (denK a.1)) = resR _ (Ans _ (denK b.1))
    rw [(denK_eq_iff a.1 b.1).2 h])

/-- **The world functor**: typed checked code modulo `OpEquivP` to its answered runs under the
closure, from world states, traps forgetting their store and frame. -/
@[expose] noncomputable def worldFunctor (Γ : Ctx H) : WObj Γ ⥤ RObj Γ where
  obj I := I
  map q := gMap q
  map_id I := RHom.ext (ans_nil I.1)
  map_comp q₁ q₂ := by
    induction q₁ using Quotient.inductionOn with
    | h m₁ =>
      induction q₂ using Quotient.inductionOn with
      | h m₂ => exact RHom.ext (ans_append m₁.2 m₂.1)

/-- **The world functor on a typed morphism**: its trap-forgetting answered runs under the
closure, from world states. -/
theorem worldFunctor_map_mk {Γ : Ctx H} {I J : WObj Γ} (m : THomE Γ I.1 J.1) :
    ((worldFunctor Γ).map (Quotient.mk _ m : I ⟶ J)).rel =
      resR (WSt Γ I.1) (trapR (denR closedCallXP m.1)) :=
  Silmaril.Proofs.Wasm.Abstract.WorldFunctor.gRel_eq m.1

/-- **On typed states** it is exactly the trap-forgetting answered runs under the closure. -/
theorem worldFunctor_realizes {Γ : Ctx H} {I J : WObj Γ} (m : THomE Γ I.1 J.1) {s : Store H}
    {f : Frame} {stk : List Val} (hr : Realizes Γ I.1 s f stk) (s' : Store H) (f' : Frame)
    (o : POut) :
    ((worldFunctor Γ).map (Quotient.mk _ m : I ⟶ J)).rel s f stk s' f' o ↔
      trapR (denR closedCallXP m.1) s f stk s' f' o :=
  Silmaril.Proofs.Wasm.Abstract.WorldFunctor.gRel_realizes m.1 hr s' f' o

/-! ## 7. The premonoidal Elgot functor, bundled -/

/-- **A premonoidal Elgot functor of the world**: a functor of the world category into the
relational codomain (its fields `map_id`, `map_comp`) preserving objects, whiskering (read at the
targets' arities) and loops. -/
structure WorldElgot (Γ : Ctx H) where
  /-- The functor, with `map_id` and `map_comp`. -/
  toFunctor : WObj Γ ⥤ RObj Γ
  /-- It keeps the interfaces. -/
  obj_eq : ∀ I : WObj Γ, (toFunctor.obj I).1 = I.1
  /-- **Whiskering**: the image of `q ⊗ R` is the whiskered image of `q`, branches and returns
  read at their target's arity. -/
  map_whisker : ∀ (R : List CValType) (hR : ResultOk {} R) {I J : WObj Γ} (q : I ⟶ J),
    trimR I.1.env.labels I.1.env.ret (toFunctor.map ((tensorW R hR).map q)).rel =
      trimR I.1.env.labels I.1.env.ret
        (resR (WSt Γ (I.1.withBelow R)) (leftR I.1.ts.length (toFunctor.map q).rel))
  /-- **Iteration**: a typed loop goes to the iteration of its step. -/
  map_iter : ∀ {I J : WObj Γ} {bt : BlockType} {body : List BExpr}
    (h : THom Γ I.1 J.1 [.loop bt body]),
    (toFunctor.map (Quotient.mk _ ⟨_, h⟩ : I ⟶ J)).rel =
      resR (WSt Γ I.1) (trapR (iterR (loopStepR closedCallXP bt body)))

/-- **Whiskering is preserved** (read at the targets' arities). -/
theorem worldFunctor_map_whisker {Γ : Ctx H} (R : List CValType) (hR : ResultOk {} R)
    {I J : WObj Γ} (q : I ⟶ J) :
    trimR I.1.env.labels I.1.env.ret ((worldFunctor Γ).map ((tensorW R hR).map q)).rel =
      trimR I.1.env.labels I.1.env.ret (whiskW R ((worldFunctor Γ).map q)).rel := by
  induction q using Quotient.inductionOn with
  | h m =>
    change trimR _ _ (resR _ (Ans _ (denK m.1))) = trimR _ _ (resR _ (leftR _ (resR _ (Ans _ _))))
    rw [ans_denK]
    exact Silmaril.Proofs.Wasm.Abstract.WorldFunctor.thom_whisker m.2 R

/-- **Loops are preserved.** -/
theorem worldFunctor_map_iter {Γ : Ctx H} {I J : WObj Γ} {bt : BlockType} {body : List BExpr}
    (h : THom Γ I.1 J.1 [.loop bt body]) :
    ((worldFunctor Γ).map (Quotient.mk _ ⟨_, h⟩ : I ⟶ J)).rel =
      resR (WSt Γ I.1) (trapR (iterR (loopStepR closedCallXP bt body))) :=
  Silmaril.Proofs.Wasm.Abstract.WorldFunctor.gRel_loop I.1 bt body

/-- **The typed premonoidal Elgot functor of the world**, all fields proved. -/
@[expose] noncomputable def worldElgot (Γ : Ctx H) : WorldElgot Γ where
  toFunctor := worldFunctor Γ
  obj_eq _ := rfl
  map_whisker R hR _ _ q := worldFunctor_map_whisker R hR q
  map_iter h := worldFunctor_map_iter h

/-! ## 8. Factorization and faithfulness -/

/-- **The world functor factors through #572's faithful functor**: it is answering by the
closure, at world states, after `worldTyped`. -/
theorem worldFunctor_factor {Γ : Ctx H} {I J : WObj Γ} (q : I ⟶ J) :
    ((worldFunctor Γ).map q).rel =
      resR (WSt Γ I.1) (Ans closedCallXP (tmap q).1) := by
  induction q using Quotient.inductionOn
  rfl

/-- The kernel of `worldTyped` (that is, `OpEquivP`) is contained in that of the world functor. -/
theorem worldFunctor_map_eq_of_tmap {Γ : Ctx H} {I J : WObj Γ} {q q' : I ⟶ J}
    (h : tmap q = tmap q') : (worldFunctor Γ).map q = (worldFunctor Γ).map q' :=
  RHom.ext (by rw [worldFunctor_factor, worldFunctor_factor, h])

/-- **`worldTyped` is faithful**: morphisms with equal images are equal. -/
theorem worldTyped_map_injective {Γ : Ctx H} {I J : WObj Γ} {q q' : I ⟶ J}
    (h : (worldTyped Γ).map q = (worldTyped Γ).map q') : q = q' :=
  (worldTyped Γ).map_injective h

/-! ## 9. Centrality -/

/-- **Pure code is central in the image**: a pure denotation under the closure interchanges with
every relation. -/
theorem worldFunctor_pure_central {n n' : Nat} {φ : List Val → List Val} {es : List BExpr}
    (hp : PureAt n n' φ (denR (closedCallXP (H := H)) es)) (g : ORel H) :
    Interchange n n' (Ans closedCallXP (denK es)) g := by
  rw [ans_denK]
  exact interchange_of_pure (Silmaril.Proofs.Wasm.Abstract.WorldFunctor.pureAt_trapR hp) g

/-- **Premonoidal, not monoidal** (#543): typed morphisms that do not interchange. -/
theorem premonoidal_not_monoidal :
    ∃ (Γ : Ctx Unit) (C : Abstract.CallRel Unit) (I : TIface) (e₁ e₂ : List BExpr)
      (s : Store Unit) (f : Frame),
      TypedAns Γ C ∧ ArityResp Γ C ∧ Coh Γ I ∧ THom Γ I I e₁ ∧ THom Γ I I e₂ ∧
        Realizes Γ I s f [] ∧ ¬ Interchange 0 0 (denR C e₁) (denR C e₂) := by
  obtain ⟨Γ, C, I, e₁, e₂, s, f, h₁, h₂, h₃, h₄, h₅, h₆, -, h₈⟩ := not_interchange
  exact ⟨Γ, C, I, e₁, e₂, s, f, h₁, h₂, h₃, h₄, h₅, h₆, h₈⟩

end Silmaril.Wasm.Abstract.WorldFunctor
