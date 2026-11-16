module

public import Silmaril.Wasm.Abstract.LegalFunctor.Defs
public import Silmaril.Wasm.Abstract.WorldFunctor.Thms
public import Silmaril.Wasm.Abstract.TypedCatFit.Thms
import Silmaril.Proofs.Wasm.Abstract.LegalFunctor.Rel
import Silmaril.Proofs.Wasm.Abstract.LegalFunctor.Examples

/-!
# The typed premonoidal Elgot functor over legal oracles

**Why.** #572's `TypedFunctor.exists_not_whisker` refutes the whiskering equation of the exit
monad for checked `call 0; drop` (callee `[] → [i32]`, one passive value). The failing branch
answers the call with **no values**, an answer that no arity-respecting oracle gives
(`not_legal_obstruction`). #579's `WorldFunctor.worldElgot` keeps whiskering, but answers every
call by the closure `closedCallXP` alone, and so is not faithful. Here the codomain quantifies
over **legal** oracles: whiskering holds for all checked code, and the functor is faithful
modulo an operational equivalence over legal oracles.

**Legal oracles** (`Legal Γ C := ArityResp Γ (fitP C)`). On fitting calls, answers keep the
store agreeing with the world and return at least the callee's declared result count. The laws
use nothing more: the checker's result invariant and the answered tensor need arity respect on
fitting calls only (`TypedCatFit.evalOXP_goodO_fit`, `evalOXP_tensor_fit`). It follows from
`ArityResp Γ C` (`legal_of_arityResp`) and from typed answers (`legal_of_typedAns`), and the
closure satisfies it (`legal_closed`). `TypedAns` (well-typed answered values) is not needed: world
states (`WSt`) constrain only the store's functions and tags, the frame's instance and local
count, and the stack height.

**Domain.** #579's world category `WObj Γ`: typed interfaces with valid stack types coherent with
the world, and #572's `TQ`, typed checked code (`THom`) modulo `OpEquivP`. Its stack tensor is
#579's `tensorW`.

**Codomain `LObj Γ`.** The same objects. A morphism `I ⟶ J` (`LHom Γ I J`) is a family, indexed
by legal oracles, of #579's `RHom Γ I J`: relations of answered runs supported on `WSt Γ I`,
landing in `WSt Γ J`, and trap-closed. Identity, composition (`lid`, `lcomp`) and whiskering
(`whiskL`) are #579's, pointwise in the oracle (`lid_apply`, `lcomp_apply`, `whiskL_apply`), with
#579's laws (`whiskL_id`, `whiskL_comp`). Iteration is #579's `iterR`, pointwise.

**The functor** `legalFunctor Γ : WObj Γ ⥤ LObj Γ` sends `es` to
`fun C _ => resR (WSt Γ I) (Ans C (denK es))`, that is `resR (WSt Γ I) (trapR (denR C es))`
(`legalFunctor_map_mk`). Bundled as `legalElgot Γ : LegalElgot Γ`:

* `map_id`, `map_comp`: exactly, for every legal oracle. Landing uses the checker's invariant under
  a legal oracle (`thom_lands_legal`);
* `map_whisker`: for **all** checked code and every legal oracle, exactly up to reading branches
  and returns at their target's arity (`trimR`). This is #579's statement with
  `evalOXP_tensor_fit` in place of the closure's instance;
* `map_iter`: a typed loop goes to `iterR (loopStepR C bt body)` under each legal oracle
  (`WorldFunctor.denR_loop` holds for every oracle).

The component at the closure is #579's world functor (`legalFunctor_closed`).

**Faithfulness, modulo `OpEquivL`.** `OpEquivL Γ I es es'` (Defs) holds when, under every legal
oracle and from every world state of `I`, `EvalOXP` reaches the same non-trap outcomes and traps
alike. It is defined with runs, not denotations.

* `legalFunctor_map_eq_iff`: two typed morphisms have the same image exactly when their codes are
  `OpEquivL`;
* `opEquivP_le_opEquivL`: `OpEquivP` implies `OpEquivL`, so `legalFunctor` factors through #572's
  quotient (it is defined on it) and through the quotient by `OpEquivL`;
* `legalQ Γ : LDom Γ ⥤ LObj Γ`, on typed code modulo `OpEquivL`, is `Functor.Faithful`;
  `legalFunctor_factor` puts `legalFunctor` through it (`toLDom`).

No witness that `OpEquivL` is strictly coarser than `OpEquivP` is formalized.

The stack tensor is stated on `WObj Γ` and not on `LDom Γ`. `OpEquivL` compares runs at the
world states of `I`. Whether it is preserved by putting values below (`I.withBelow R`) is not
proved: the answered tensor determines the runs on the larger stack only up to `trimO`.

**Audit of #572's obstruction** (`exists_not_whisker_illegal`). At the obstruction's data (code,
world, frame and stacks, restated in this topic's proofs): the relational whiskering equation
holds under **every** legal oracle, and fails under #572's oracle `C₁` (every call answered with
no values). `C₁` is neither `ArityResp` nor `Legal`. The general form, for all checked code and
any legal oracle, is `mor_whisker_legal`.

**Premonoidal, not monoidal.** `legal_not_interchange`: at a legal oracle with typed answers, the
images of the typed calls `call 0` and `call 1` do not interchange (#543's `not_interchange`
data, restated). `legal_pure_central`: pure code is central under every oracle.

**Scope.** Only the supported checked fragment is covered (the checker's integer, control, call and
exception forms), not full Wasm. Faithfulness is injectivity modulo the operational
`OpEquivL`; it is not contextual full abstraction. Host-level Core faithfulness (the closed,
host-answered semantics against Core with hosts) is not claimed. "Legal" means callee-arity
respecting answers that keep the world; with typed answers it is the oracle class of #543.
-/

public section

namespace Silmaril.Wasm.Abstract.LegalFunctor

open CategoryTheory
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
open Silmaril.Wasm.Abstract.ExposeP Silmaril.Wasm.Abstract.ExposePStruct
open Silmaril.Wasm.Abstract.ExposePTyped Silmaril.Wasm.Abstract.TypedCat
open Silmaril.Wasm.Abstract.TypedFunctor Silmaril.Wasm.Abstract.WorldFunctor
open Silmaril.Wasm.Abstract.CallXP (POut EvalOXP)
open Silmaril.Wasm.Abstract.XRecursionP (closedCallXP)
open Silmaril.Wasm.Validation (CValType ResultOk)
open Silmaril.Wasm.Abstract.FunctorP (OpEquivP)

variable {H : Type}

/-! ## 1. Legal oracles -/

theorem legal_of_arityResp {Γ : Ctx H} {C : Abstract.CallRel H} (h : ArityResp Γ C) :
    Legal Γ C :=
  Silmaril.Proofs.Wasm.Abstract.LegalFunctor.legal_of_arityResp h

theorem legal_of_typedAns {Γ : Ctx H} {C : Abstract.CallRel H} (h : TypedAns Γ C) : Legal Γ C :=
  legal_of_arityResp (arityResp_of_typedAns h)

/-- **The closure is legal.** -/
theorem legal_closed (Γ : Ctx H) : Legal Γ (closedCallXP (H := H)) := arityResp_fitClosed Γ

/-- **Typed code keeps the world under every legal oracle.** -/
theorem thom_lands_legal {Γ : Ctx H} {C : Abstract.CallRel H} (hC : Legal Γ C) {I J : TIface}
    {es : List BExpr} (hm : THom Γ I J es) {s : Store H} {f : Frame} {stk : List Val}
    (hw : WSt Γ I s f stk) {s' : Store H} {f' : Frame} {vs : List Val}
    (d : EvalOXP C s f stk es (s', f', .flow (.normal vs))) : WSt Γ J s' f' vs :=
  Silmaril.Proofs.Wasm.Abstract.LegalFunctor.thom_lands_legal hC hm hw d

/-- Typed code lands in the world, answered by a legal oracle. -/
theorem ans_lands_legal {Γ : Ctx H} {C : Abstract.CallRel H} (hC : Legal Γ C) {I J : TIface}
    {es : List BExpr} (hm : THom Γ I J es) :
    ∀ s f stk s' f' vs, resR (WSt Γ I) (Ans C (denK es)) s f stk s' f'
      (.flow (.normal vs)) → WSt Γ J s' f' vs :=
  Silmaril.Proofs.Wasm.Abstract.LegalFunctor.ans_lands_legal hC hm

/-- The empty code answers as the restricted identity, under every oracle. -/
theorem ans_nil_oracle {Γ : Ctx H} (C : Abstract.CallRel H) (I : TIface) :
    resR (WSt Γ I) (Ans C (denK (H := H) [])) = resR (WSt Γ I) idR :=
  Silmaril.Proofs.Wasm.Abstract.LegalFunctor.ans_nil C I

theorem opEquivL_refl {Γ : Ctx H} (I : TIface) (es : List BExpr) : OpEquivL Γ I es es :=
  Silmaril.Proofs.Wasm.Abstract.LegalFunctor.opEquivL_refl I es

theorem opEquivL_symm {Γ : Ctx H} {I : TIface} {es es' : List BExpr} (h : OpEquivL Γ I es es') :
    OpEquivL Γ I es' es :=
  Silmaril.Proofs.Wasm.Abstract.LegalFunctor.opEquivL_symm h

theorem opEquivL_trans {Γ : Ctx H} {I : TIface} {es₁ es₂ es₃ : List BExpr}
    (h₁ : OpEquivL Γ I es₁ es₂) (h₂ : OpEquivL Γ I es₂ es₃) : OpEquivL Γ I es₁ es₃ :=
  Silmaril.Proofs.Wasm.Abstract.LegalFunctor.opEquivL_trans h₁ h₂

/-! ## 2. The codomain -/

/-- Equality of morphisms of the codomain: equal relations at every legal oracle. -/
theorem LHom.ext' {Γ : Ctx H} {I J : TIface} {g h : LHom Γ I J}
    (e : ∀ C hC, (g C hC).rel = (h C hC).rel) : g = h :=
  funext fun C => funext fun hC => RHom.ext (e C hC)

/-- The identity: #579's, at every legal oracle. -/
@[expose] def lid (Γ : Ctx H) (I : TIface) : LHom Γ I I := fun _ _ =>
  ⟨resR (WSt Γ I) idR, fun _ _ _ _ _ _ h => h.1, idR_lands, idR_trap⟩

/-- Composition: #579's exit-aware composition, at every legal oracle. -/
@[expose] def lcomp {Γ : Ctx H} {I J K : TIface} (g : LHom Γ I J) (h : LHom Γ J K) :
    LHom Γ I K := fun C hC =>
  ⟨seqR (g C hC).rel (h C hC).rel, seqR_supp _ (g C hC).supp, seqR_lands _ (h C hC).lands,
    seqR_trap (g C hC).trap (h C hC).trap⟩

/-- **The codomain over legal oracles.** -/
instance (Γ : Ctx H) : Category (LObj Γ) where
  Hom I J := LHom Γ I.1 J.1
  id I := lid Γ I.1
  comp := lcomp
  id_comp g := LHom.ext' fun C hC => seqR_resR_idR_left _ (g C hC).supp
  comp_id g := LHom.ext' fun C hC => seqR_resR_idR_right _ (g C hC).lands
  assoc g₁ g₂ g₃ := LHom.ext' fun C hC => seqR_assoc (g₁ C hC).rel (g₂ C hC).rel (g₃ C hC).rel

/-- **Pointwise**: the identity at a legal oracle is #579's identity. -/
theorem lid_apply {Γ : Ctx H} (I : LObj Γ) (C : Abstract.CallRel H) (hC : Legal Γ C) :
    lid Γ I.1 C hC = CategoryStruct.id (obj := RObj Γ) ⟨I.1, I.2⟩ := rfl

/-- **Pointwise**: composition at a legal oracle is #579's composition. -/
theorem lcomp_apply {Γ : Ctx H} {I J K : LObj Γ} (g : I ⟶ J) (h : J ⟶ K)
    (C : Abstract.CallRel H) (hC : Legal Γ C) :
    (g ≫ h) C hC = CategoryStruct.comp (obj := RObj Γ) (X := ⟨I.1, I.2⟩) (Y := ⟨J.1, J.2⟩)
      (Z := ⟨K.1, K.2⟩) (g C hC) (h C hC) := rfl

/-- **The codomain's whiskering** `g ⋉ R`: #579's `whiskW R`, at every legal oracle. -/
@[expose] def whiskL {Γ : Ctx H} (R : List CValType) {I J : TIface} (g : LHom Γ I J) :
    LHom Γ (I.withBelow R) (J.withBelow R) := fun C hC => whiskW R (g C hC)

theorem whiskL_apply {Γ : Ctx H} (R : List CValType) {I J : TIface} (g : LHom Γ I J)
    (C : Abstract.CallRel H) (hC : Legal Γ C) : whiskL R g C hC = whiskW R (g C hC) := rfl

/-- **Whiskering keeps identities.** -/
theorem whiskL_id {Γ : Ctx H} (R : List CValType) (I : LObj Γ) :
    whiskL R (𝟙 I) = lid Γ (I.1.withBelow R) :=
  LHom.ext' fun _ _ => whiskW_id R ⟨I.1, I.2⟩

/-- **Whiskering keeps composition.** -/
theorem whiskL_comp {Γ : Ctx H} (R : List CValType) {I J K : LObj Γ} (g₁ : I ⟶ J) (g₂ : J ⟶ K) :
    whiskL R (g₁ ≫ g₂) = lcomp (whiskL R g₁) (whiskL R g₂) :=
  LHom.ext' fun C hC =>
    whiskW_comp (I := ⟨I.1, I.2⟩) (J := ⟨J.1, J.2⟩) (K := ⟨K.1, K.2⟩) R (g₁ C hC) (g₂ C hC)

/-! ## 3. The functor -/

/-- The answered runs of a typed morphism under every legal oracle, from world states. -/
@[expose] noncomputable def gL {Γ : Ctx H} {I J : TIface} (m : THomE Γ I J) : LHom Γ I J :=
  fun C hC => ⟨resR (WSt Γ I) (Ans C (denK m.1)), fun _ _ _ _ _ _ h => h.1,
    ans_lands_legal hC m.2,
    fun _ _ _ _ _ _ _ h => h⟩

/-- Concatenation goes to composition, for every legal oracle. -/
theorem gL_append {Γ : Ctx H} {I J K : TIface} (m₁ : THomE Γ I J) (m₂ : THomE Γ J K) :
    gL (⟨m₁.1 ++ m₂.1, tmor_comp m₁.2 m₂.2⟩ : THomE Γ I K) = lcomp (gL m₁) (gL m₂) :=
  LHom.ext' fun _ hC => Silmaril.Proofs.Wasm.Abstract.LegalFunctor.ans_append_legal hC m₁.2 m₂.1

/-- **Faithfulness on representatives**: equal images exactly when `OpEquivL`. -/
theorem gL_eq_iff {Γ : Ctx H} {I J : TIface} (m m' : THomE Γ I J) :
    gL m = gL m' ↔ OpEquivL Γ I m.1 m'.1 :=
  ⟨fun h => Silmaril.Proofs.Wasm.Abstract.LegalFunctor.ans_eq_iff.1 fun C hC =>
      congrArg (fun g : LHom Γ I J => (g C hC).rel) h,
    fun h => LHom.ext' (Silmaril.Proofs.Wasm.Abstract.LegalFunctor.ans_eq_iff.2 h)⟩

/-- **`OpEquivP` implies `OpEquivL`.** -/
theorem opEquivP_le_opEquivL (Γ : Ctx H) (I : TIface) {es es' : List BExpr}
    (h : OpEquivP H es es') : OpEquivL Γ I es es' :=
  Silmaril.Proofs.Wasm.Abstract.LegalFunctor.opEquivL_of_opEquivP h I

/-- On #572's `OpEquivP` classes. -/
@[expose] noncomputable def lMap {Γ : Ctx H} {I J : TIface} : TQ Γ I J → LHom Γ I J :=
  Quotient.lift gL fun a b h => (gL_eq_iff a b).2 (opEquivP_le_opEquivL Γ I h)

/-- **The functor over legal oracles**: typed checked code modulo `OpEquivP` to its answered runs
under every legal oracle, from world states, traps forgetting their store and frame. -/
@[expose] noncomputable def legalFunctor (Γ : Ctx H) : WObj Γ ⥤ LObj Γ where
  obj I := ⟨I.1, I.2⟩
  map q := lMap q
  map_id I := LHom.ext' fun C _ => ans_nil_oracle C I.1
  map_comp q₁ q₂ := by
    induction q₁ using Quotient.inductionOn with
    | h m₁ =>
      induction q₂ using Quotient.inductionOn with
      | h m₂ => exact gL_append m₁ m₂

/-- **The functor on a typed morphism**: at each legal oracle, its trap-forgetting answered runs
from world states. -/
theorem legalFunctor_map_mk {Γ : Ctx H} {I J : WObj Γ} (m : THomE Γ I.1 J.1)
    (C : Abstract.CallRel H) (hC : Legal Γ C) :
    ((legalFunctor Γ).map (Quotient.mk _ m : I ⟶ J) C hC).rel =
      resR (WSt Γ I.1) (trapR (denR C m.1)) :=
  congrArg (resR (WSt Γ I.1)) (ans_denK C m.1)

/-- **Its component at the closure is #579's world functor.** -/
theorem legalFunctor_closed {Γ : Ctx H} {I J : WObj Γ} (q : I ⟶ J) :
    (legalFunctor Γ).map q closedCallXP (legal_closed Γ) = (worldFunctor Γ).map q := by
  induction q using Quotient.inductionOn
  rfl

/-! ## 4. The premonoidal Elgot functor, bundled -/

/-- **A premonoidal Elgot functor over legal oracles**: a functor of the world category into the
codomain over legal oracles preserving objects, whiskering (read at the targets' arities) and
loops, at every legal oracle. -/
structure LegalElgot (Γ : Ctx H) where
  /-- The functor, with `map_id` and `map_comp`. -/
  toFunctor : WObj Γ ⥤ LObj Γ
  /-- It keeps the interfaces. -/
  obj_eq : ∀ I : WObj Γ, (toFunctor.obj I).1 = I.1
  /-- **Whiskering**, at every legal oracle. -/
  map_whisker : ∀ (R : List CValType) (hR : ResultOk {} R) {I J : WObj Γ} (q : I ⟶ J)
    (C : Abstract.CallRel H) (hC : Legal Γ C),
    trimR I.1.env.labels I.1.env.ret (toFunctor.map ((tensorW R hR).map q) C hC).rel =
      trimR I.1.env.labels I.1.env.ret
        (resR (WSt Γ (I.1.withBelow R)) (leftR I.1.ts.length (toFunctor.map q C hC).rel))
  /-- **Iteration**: a typed loop goes to the iteration of its step, at every legal oracle. -/
  map_iter : ∀ {I J : WObj Γ} {bt : BlockType} {body : List BExpr}
    (h : THom Γ I.1 J.1 [.loop bt body]) (C : Abstract.CallRel H) (hC : Legal Γ C),
    (toFunctor.map (Quotient.mk _ ⟨_, h⟩ : I ⟶ J) C hC).rel =
      resR (WSt Γ I.1) (trapR (iterR (loopStepR C bt body)))

/-- **Whiskering is preserved for all checked code, under every legal oracle** (read at the
targets' arities). -/
theorem legalFunctor_map_whisker {Γ : Ctx H} (R : List CValType) (hR : ResultOk {} R)
    {I J : WObj Γ} (q : I ⟶ J) (C : Abstract.CallRel H) (hC : Legal Γ C) :
    trimR I.1.env.labels I.1.env.ret ((legalFunctor Γ).map ((tensorW R hR).map q) C hC).rel =
      trimR I.1.env.labels I.1.env.ret (whiskL R ((legalFunctor Γ).map q) C hC).rel := by
  induction q using Quotient.inductionOn with
  | h m =>
    change trimR _ _ (resR _ (Ans _ (denK m.1))) = trimR _ _ (resR _ (leftR _ (resR _ (Ans _ _))))
    rw [ans_denK]
    exact Silmaril.Proofs.Wasm.Abstract.LegalFunctor.thom_whisker_legal hC m.2 R

/-- **Loops are preserved**, under every legal oracle. -/
theorem legalFunctor_map_iter {Γ : Ctx H} {I J : WObj Γ} {bt : BlockType} {body : List BExpr}
    (h : THom Γ I.1 J.1 [.loop bt body]) (C : Abstract.CallRel H) (hC : Legal Γ C) :
    ((legalFunctor Γ).map (Quotient.mk _ ⟨_, h⟩ : I ⟶ J) C hC).rel =
      resR (WSt Γ I.1) (trapR (iterR (loopStepR C bt body))) := by
  rw [legalFunctor_map_mk, denR_loop]

/-- **The typed premonoidal Elgot functor over legal oracles**, all fields proved. -/
@[expose] noncomputable def legalElgot (Γ : Ctx H) : LegalElgot Γ where
  toFunctor := legalFunctor Γ
  obj_eq _ := rfl
  map_whisker R hR _ _ q C hC := legalFunctor_map_whisker R hR q C hC
  map_iter h C hC := legalFunctor_map_iter h C hC

/-! ## 5. Faithfulness modulo `OpEquivL` -/

/-- **Faithful modulo `OpEquivL`**: two typed morphisms have the same image exactly when their
codes are operationally equivalent over legal oracles at the source's world states. -/
theorem legalFunctor_map_eq_iff {Γ : Ctx H} {I J : WObj Γ} (m m' : THomE Γ I.1 J.1) :
    (legalFunctor Γ).map (Quotient.mk _ m : I ⟶ J) = (legalFunctor Γ).map (Quotient.mk _ m') ↔
      OpEquivL Γ I.1 m.1 m'.1 :=
  gL_eq_iff m m'

/-- `OpEquivL` on typed morphisms. -/
@[expose] def lSetoid (Γ : Ctx H) (I J : TIface) : Setoid (THomE Γ I J) where
  r m m' := OpEquivL Γ I m.1 m'.1
  iseqv := ⟨fun m => opEquivL_refl I m.1, opEquivL_symm, opEquivL_trans⟩

/-- **Typed morphisms modulo `OpEquivL`.** -/
@[expose, reducible] def LQ (Γ : Ctx H) (I J : TIface) : Type := Quotient (lSetoid Γ I J)

/-- Composition modulo `OpEquivL`: `OpEquivL` is a congruence for concatenation of typed code. -/
@[expose] def lqComp {Γ : Ctx H} {I J K : TIface} : LQ Γ I J → LQ Γ J K → LQ Γ I K :=
  Quotient.map₂ (fun m₁ m₂ => ⟨m₁.1 ++ m₂.1, tmor_comp m₁.2 m₂.2⟩) fun a a' ha b b' hb =>
    (gL_eq_iff _ _).1 (by rw [gL_append, gL_append, (gL_eq_iff a a').2 ha, (gL_eq_iff b b').2 hb])

/-- **The domain modulo `OpEquivL`.** -/
instance (Γ : Ctx H) : Category (LDom Γ) where
  Hom I J := LQ Γ I.1 J.1
  id I := Quotient.mk _ ⟨[], thom_id I.2.1⟩
  comp := lqComp
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

/-- **The functor on `OpEquivL` classes.** -/
@[expose] noncomputable def legalQ (Γ : Ctx H) : LDom Γ ⥤ LObj Γ where
  obj I := ⟨I.1, I.2⟩
  map q := Quotient.lift (s := lSetoid Γ _ _) gL (fun a b h => (gL_eq_iff a b).2 h) q
  map_id I := LHom.ext' fun C _ => ans_nil_oracle C I.1
  map_comp q₁ q₂ := by
    induction q₁ using Quotient.inductionOn with
    | h m₁ =>
      induction q₂ using Quotient.inductionOn with
      | h m₂ => exact gL_append m₁ m₂

/-- **It is faithful.** -/
instance (Γ : Ctx H) : (legalQ Γ).Faithful where
  map_injective {_ _} {q q'} h := by
    induction q using Quotient.inductionOn
    induction q' using Quotient.inductionOn
    exact Quotient.sound ((gL_eq_iff _ _).1 h)

/-- #572's quotient onto the quotient by `OpEquivL` (`opEquivP_le_opEquivL`). -/
@[expose] def toLDom (Γ : Ctx H) : WObj Γ ⥤ LDom Γ where
  obj I := ⟨I.1, I.2⟩
  map q := Quotient.map (sa := opSetoid Γ _ _) (sb := lSetoid Γ _ _) (fun m => m)
    (fun _ _ h => opEquivP_le_opEquivL Γ _ h) q
  map_id _ := rfl
  map_comp q₁ q₂ := by
    induction q₁ using Quotient.inductionOn
    induction q₂ using Quotient.inductionOn
    rfl

/-- **The functor factors through the faithful functor on `OpEquivL` classes.** -/
theorem legalFunctor_factor {Γ : Ctx H} {I J : WObj Γ} (q : I ⟶ J) :
    (legalFunctor Γ).map q = (legalQ Γ).map ((toLDom Γ).map q) := by
  induction q using Quotient.inductionOn
  rfl

/-! ## 6. The audit of #572's obstruction -/

/-- **The whiskering equation of checked code under every legal oracle**, as relations: on a
stack of the checked height with `rest` below, in a frame of the checked instance and local
count, from a store agreeing with the world. -/
theorem mor_whisker_legal {Γ : Ctx H} {C : Abstract.CallRel H} (hC : Legal Γ C) {I : Iface}
    {oc : Option Nat} {es : List BExpr} (hm : Mor Γ I oc es) {s : Store H} {f : Frame}
    {stk : List Val} (hg : Γ.Good s) (hf : f.module = I.env.mi) (hn : f.locals.length = I.env.nl)
    (hs : stk.length = I.h) (rest : List Val) :
    trimR I.env.labels I.env.ret (denR C es) s f (stk ++ rest) =
      trimR I.env.labels I.env.ret (whiskR rest (denR C es)) s f (stk ++ rest) :=
  Silmaril.Proofs.Wasm.Abstract.LegalFunctor.mor_whisker_legal hC hm hg hf hn hs rest

/-- **The audit of `TypedFunctor.exists_not_whisker`.** At its data (checked `call 0; drop`, a
callee `[] → [i32]`, one passive value), the relational whiskering equation holds under every
legal oracle, and fails under the oracle `C` answering every call with no values. The answer
`C s 0 [] (s, .normal [])` to that fitting call is short of the callee's result, so `C` is neither
`ArityResp` nor `Legal`. -/
theorem exists_not_whisker_illegal :
    ∃ (Γ : Ctx Unit) (I : Iface) (es : List BExpr) (s : Store Unit) (f : Frame)
      (stk rest : List Val) (C : Abstract.CallRel Unit),
      Mor Γ I (some I.h) es ∧ Γ.Good s ∧ f.module = I.env.mi ∧ f.locals.length = I.env.nl ∧
        stk.length = I.h ∧
        (∀ C', Legal Γ C' →
          trimR I.env.labels I.env.ret (denR C' es) s f (stk ++ rest) =
            trimR I.env.labels I.env.ret (whiskR rest (denR C' es)) s f (stk ++ rest)) ∧
        C s 0 [] (s, .normal []) ∧ ¬ ArityResp Γ C ∧ ¬ Legal Γ C ∧
        ¬ (trimR I.env.labels I.env.ret (denR C es) s f (stk ++ rest) =
            trimR I.env.labels I.env.ret (whiskR rest (denR C es)) s f (stk ++ rest)) :=
  open Silmaril.Proofs.Wasm.Abstract.LegalFunctor.Obs in
  ⟨Γ₁, I₁, es₁, s₁, f₁, [], [v₁], C₁, audit⟩

/-- The obstruction's oracle is not legal, in general form: an answer with fewer values than the
callee's declared results, to a fitting call from a store agreeing with the world, rules a
legal oracle out. -/
theorem not_legal_obstruction {Γ : Ctx H} {C : Abstract.CallRel H} {s s₂ : Store H} {a : Nat}
    {args : List Val} {fl : Flow} {fi : FuncInst H} {ps rs : List CValType} {vs : List Val}
    (hg : Γ.Good s) (hfi : s.funcs[a]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hfit : args.length = ps.length)
    (hc : C s a args (s₂, fl)) (hvs : fl.retVals = some vs) (hshort : vs.length < rs.length) :
    ¬ Legal Γ C := fun h =>
  absurd ((h s s₂ a args fl ⟨hc, fun _ _ _ h₁ h₂ => by
    rw [hfi] at h₁; cases h₁; rw [hty] at h₂; cases h₂; exact hfit⟩ hg).2 fi ps rs vs hfi hty hvs)
    (Nat.not_le.2 hshort)

/-! ## 7. Premonoidal, not monoidal -/

/-- **Interchange fails in the codomain over legal oracles**: at a legal oracle with typed answers,
the images of two typed endomorphisms (#543's `call 0` and `call 1`) do not interchange. -/
theorem legal_not_interchange :
    ∃ (Γ : Ctx Unit) (C : Abstract.CallRel Unit) (hC : Legal Γ C) (I : WObj Γ) (q₁ q₂ : I ⟶ I),
      TypedAns Γ C ∧ ArityResp Γ C ∧
        ¬ Interchange 0 0 ((legalFunctor Γ).map q₁ C hC).rel
          ((legalFunctor Γ).map q₂ C hC).rel := by
  obtain ⟨Γ, C, I, e₁, e₂, hT, hA, hI, hco, h₁, h₂, hn⟩ :=
    Silmaril.Proofs.Wasm.Abstract.LegalFunctor.Inter.not_interchange_legal
  exact ⟨Γ, C, legal_of_arityResp hA, ⟨I, hI, hco⟩, Quotient.mk _ ⟨e₁, h₁⟩,
    Quotient.mk _ ⟨e₂, h₂⟩, hT, hA, hn⟩

/-- **Pure code is central** under every oracle: a pure denotation interchanges with every
relation (#543's `interchange_of_pure` through `trapR`). -/
theorem legal_pure_central {C : Abstract.CallRel H} {n n' : Nat} {φ : List Val → List Val}
    {es : List BExpr} (hp : PureAt n n' φ (denR C es)) (g : ORel H) :
    Interchange n n' (Ans C (denK es)) g := by
  rw [ans_denK]
  exact interchange_of_pure (Silmaril.Proofs.Wasm.Abstract.LegalFunctor.pureAt_trapR hp) g

end Silmaril.Wasm.Abstract.LegalFunctor
