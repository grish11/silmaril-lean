module

public import Silmaril.Wasm.Abstract.TypedFunctor.Defs
public import Silmaril.Wasm.Abstract.ExposePTyped.Thms
public import Silmaril.Wasm.Abstract.FullObsFaithful.Thms
public import Silmaril.Semantics.IterOpsGen.Thms
import Silmaril.Proofs.Wasm.Abstract.TypedFunctor.Basic
import Silmaril.Proofs.Wasm.Abstract.TypedFunctor.Obstruction

/-!
# The typed premonoidal Elgot functor of the exact F5 denotation

**Domain.** Typed code: the category `TObj Γ` of Core-typed interfaces (`ExposePTyped.TIface`
with valid stack types) in a store context `Γ`, whose morphisms `I ⟶ J` are the typed code
`THom Γ I J es` (#540/#543: Core-validated at `I → J` and passing #529's check) **modulo the open
interaction equivalence** `FunctorP.OpEquivP` (`TQ Γ I J`). The identity is `[]` and
composition is concatenation; the category laws hold already on syntax.

**Codomain.** Not a new category: the sub-structure `TOps Γ` of the generic premonoidal Elgot
structure `IterOps.kleisliOps (PX H)` (#216) of the **exit monad**
`PX H = ExceptT Exit (M (CallSig H) H)` generated (`IterOps.genOps`) by the images of typed code
(`TypedFunctor.TGen`). `PX H` is a lawful Elgot monad by the library's `ExceptT`, `StateT` and
interaction-tree layers (`px_lawfulElgot`), so `kleisliOps (PX H)` is lawful (`kOps_lawful`,
`IterOps.kleisli_lawful`), and so is the generated sub-structure (`tOps_lawful`), by transfer
along its inclusion, a faithful, operation-preserving `IterOps.Hom` (`tIncl`).

**The exit encoding.** `resEquiv : ResP ≃ Except Exit Cfg` (a fallthrough is the value, every
other result an exit); `kEquiv : PHom H Cfg ResP ≃ (Cfg → PX H Cfg)` is `toK`/`ofK`, and
`denL es = ofK (denK es)` (`denL_eq_ofK`).

**Exact preservation** (equations of arrows of `PX H`, on all code, untyped):

* `denK_nil`, `denK_append`: identity and composition (`toK_idP`, `toK_seqP`: `seqP` is
  exactly Kleisli composition of the exit monad);
* `denK_loop`: a loop is the Elgot iteration of its step `loopK` (`br 0` continues),
  `toK_iter` in general;
* `denK_if`: an `if` is its condition, then the boolean test `testK`, then the **copairing**
  of its two arms read as blocks (`toK_ifP`).

Blocks and `try_table` resolve exits (`br 0`, a caught exception) with a handler on the exit
summand of `PX H`, which is not an operation of `Ops`; they enter the sub-structure as
generators (typed code), not as copairings.

**The typed Elgot functor.** `tmap : TQ Γ I J → TArr Γ Cfg Cfg` sends a typed morphism to its
denotation in the generated sub-structure.

* `tmap_injective`: **faithful**, injective modulo `OpEquivP` (`denK_eq_iff`, from
  `FunctorP.opEquivP_iff` and the trap payloads being `PUnit`); `denK_eq_iff_toFull`: through the
  canonical full observation, `FullObsFaithful.toFull_denL_eq_iff`;
* `tmap_id`, `tmap_comp`: identity and composition, exactly; `typedFunctor Γ` bundles them as a
  functor `TObj Γ ⥤ SingleObj (TMon Γ)` (the one-object category of the endomorphism monoid of
  `Cfg` in `TOps Γ`), `Functor.Faithful`;
* `tmap_loop`: iteration, exactly (`TOps Γ`'s `iter` of the loop step);
* `tmap_if`: copairing, exactly (`TOps Γ`'s `comp`, `case` and the test).

Faithfulness is injectivity modulo `OpEquivP`, the **operational open interaction
equivalence** (logged runs, logged traps and logged pending calls of `CallXP` at every oracle,
store, frame and stack). It is not contextual full abstraction: nothing here relates
`OpEquivP` to equivalence in program contexts. The functor is about the canonical F5 semantics
with every call an event; Core faithfulness with hosts (the closed, host-answered semantics)
awaits the H2 bridge and is not claimed.

**The premonoidal part, honestly.** `TOps Γ`'s whiskering is the strength of `PX H` with a
passive *Lean type*; Wasm's stack tensor appends a passive *stack*, and the two agree only where
proved:

* `tmor_whisker` (on the **stack-pure fragment**, #529's `denListXP_whisker`): for checked
  stack-pure code (no call form, tail call, `throw` or `try_table`) at a configuration of the
  checked height in a frame of the checked instance, precomposing with the stack append
  `appK` is whiskering by the passive stack and then appending, every exit read at its
  target's arity (`trimK`). This is `map_whisker` on that fragment and at those configurations;
* `whiskK_iff`: that equation of `PX H` arrows is exactly #529's equation of `BodyM`
  computations, on all code;
* `exists_not_whisker` (**an obstruction of this codomain only**): the equation of `PX H`
  arrows fails for checked code with a call (`call 0; drop`, callee `[] → [i32]`), at a
  configuration of the checked height. The failing branch answers the call with **no values**,
  which no arity-respecting oracle does (`ExposePTyped.ArityResp`): `PX H` quantifies over every
  answer `Store H × Flow`, legal or not. So the stack-pure hypothesis cannot be dropped *for
  `PX H`*. This is not a counterexample to a typed premonoidal functor into a codomain of legal
  answers, and it is not a legal typed strategy;
* on all checked code the tensor holds for answered runs under **arity-respecting** oracles
  (#540's `ExposePTyped.tmor_tensor`, #545's `TypedCatFit`), and #579's
  `WorldFunctor.worldFunctor_map_whisker` is `map_whisker` for all checked code in the world
  codomain answered by `closedCallXP`. In `PX H` itself no `map_whisker` is claimed for all
  code, so `typedFunctor` is stated as an Elgot functor (identity, composition, iteration,
  copairing). The codomain with only legal answers is the intended target for the premonoidal
  structure on all checked code;
* `pure_central_of_denK`: code denoting a pure map is central: it commutes with every
  whiskered arrow (`IterOps.Ops.Lawful.pure_central`), the transfer of
  `TypedCat.interchange_of_pure`. Effectful typed code is not central in general
  (`TypedCat.not_interchange`: two typed calls do not interchange under a typed oracle), which is
  why the structure is premonoidal, not monoidal.
-/

public section

namespace Silmaril.Wasm.Abstract.TypedFunctor

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
open Silmaril.Wasm.Abstract.ExposeP Silmaril.Wasm.Abstract.ExposePStruct
open Silmaril.Wasm.Abstract.ExposePTyped
open Silmaril.Wasm.Abstract.FunctorP (OpEquivP)

variable {H : Type}

/-! ## 1. The exit monad -/

/-- The exit monad is a lawful Elgot monad. -/
theorem px_lawfulElgot : Silmaril.Elgot.LawfulElgotMonad (PX H) := inferInstance

/-- **The Kleisli operations of the exit monad are lawful.** -/
theorem kOps_lawful : (kOps H).Lawful := IterOps.kleisli_lawful _

/-- **The exit encoding.** -/
def resEquiv : ResP ≃ Except Exit Cfg where
  toFun := enc
  invFun := dec
  left_inv := Silmaril.Proofs.Wasm.Abstract.TypedFunctor.dec_enc
  right_inv := Silmaril.Proofs.Wasm.Abstract.TypedFunctor.enc_dec

/-- Bodies are the arrows of the exit monad. -/
noncomputable def kEquiv : PHom H Cfg ResP ≃ (Cfg → PX H Cfg) where
  toFun := toK
  invFun := ofK
  left_inv := Silmaril.Proofs.Wasm.Abstract.TypedFunctor.ofK_toK
  right_inv := Silmaril.Proofs.Wasm.Abstract.TypedFunctor.toK_ofK

/-- The denotation is recovered from its exit-monad form. -/
theorem denL_eq_ofK (es : List BExpr) : denL (H := H) es = ofK (denK es) :=
  (Silmaril.Proofs.Wasm.Abstract.TypedFunctor.ofK_toK _).symm

/-! ## 2. The concrete map -/

/-- The identity is the Kleisli identity. -/
theorem toK_idP : toK (idP : PHom H Cfg ResP) = (kOps H).id Cfg :=
  Silmaril.Proofs.Wasm.Abstract.TypedFunctor.toK_idP

/-- **Exit-aware composition is Kleisli composition of the exit monad.** -/
theorem toK_seqP (g₁ g₂ : PHom H Cfg ResP) :
    toK (seqP g₁ g₂) = (kOps H).comp (toK g₁) (toK g₂) :=
  Silmaril.Proofs.Wasm.Abstract.TypedFunctor.toK_seqP g₁ g₂

/-- Elgot iteration of bodies is Elgot iteration of the exit monad. -/
theorem toK_iter (F : Cfg → M (CallSig H) H (ResP ⊕ Cfg)) :
    toK (Silmaril.Elgot.iter F) = (kOps H).iter (stepK F) :=
  Silmaril.Proofs.Wasm.Abstract.TypedFunctor.toK_iter F

/-- An `if` is its condition, the test, and the copairing of its arms. -/
theorem toK_ifP (bt : BlockType) (gc gt ge : PHom H Cfg ResP) :
    toK (ifP bt gc gt ge) = (kOps H).comp (toK gc) ((kOps H).comp testK
      ((kOps H).case (toK (blockP bt gt)) (toK (blockP bt ge)))) :=
  Silmaril.Proofs.Wasm.Abstract.TypedFunctor.toK_ifP bt gc gt ge

/-- The empty sequence denotes the identity. -/
theorem denK_nil : denK (H := H) [] = (kOps H).id Cfg := by
  rw [denK, denL_nil, toK_idP]

/-- **Concatenation denotes composition**, exactly. -/
theorem denK_append (es₁ es₂ : List BExpr) :
    denK (H := H) (es₁ ++ es₂) = (kOps H).comp (denK es₁) (denK es₂) := by
  rw [denK, denL_append, toK_seqP]; rfl

/-- **A loop denotes the iteration of its step**, exactly. -/
theorem denK_loop (bt : BlockType) (body : List BExpr) :
    denK (H := H) [.loop bt body] = (kOps H).iter (loopK bt body) := by
  rw [denK, denL_singleton, denT_loop, toK_iter]; rfl

/-- **An `if` denotes a copairing**, exactly. -/
theorem denK_if (bt : BlockType) (c t el : List BExpr) :
    denK (H := H) [.if_ bt c t el] = (kOps H).comp (denK c) ((kOps H).comp testK
      ((kOps H).case (denK [.block bt t]) (denK [.block bt el]))) := by
  rw [denK, denL_singleton, denT_if, toK_ifP, denK, denK, denK, denL_singleton, denL_singleton,
    denT_block, denT_block]

/-- **Faithfulness**: two code lists have the same exit-monad denotation exactly when they are
open-interaction equivalent. -/
theorem denK_eq_iff (es es' : List BExpr) : denK (H := H) es = denK es' ↔ OpEquivP H es es' :=
  (kEquiv.injective.eq_iff).trans
    (Silmaril.Proofs.Wasm.Abstract.TypedFunctor.opEquivP_iff_eq es es').symm

/-- The same through the canonical full observation. -/
theorem denK_eq_iff_toFull (es es' : List BExpr) :
    denK (H := H) es = denK es' ↔ FullObs.toFull (denL (H := H) es) = FullObs.toFull (denL es') :=
  (denK_eq_iff es es').trans (FullObsFaithful.toFull_denL_eq_iff es es').symm

/-! ## 3. The generated sub-structure -/

/-- **The generated sub-structure is lawful**, by transfer along its inclusion. -/
theorem tOps_lawful (Γ : Ctx H) : (TOps Γ).Lawful :=
  IterOps.genOps_kleisli_lawful _ _

/-- Its inclusion into the Kleisli operations of the exit monad. -/
noncomputable def tIncl (Γ : Ctx H) : IterOps.Hom (TOps Γ) (kOps H) := IterOps.genIncl _ _

/-! ## The typed Elgot functor -/

/-- The open interaction equivalence on typed morphisms. -/
@[expose] def opSetoid (Γ : Ctx H) (I J : TIface) : Setoid (THomE Γ I J) where
  r := OpRel Γ I J
  iseqv :=
    ⟨fun m => (denK_eq_iff m.1 m.1).1 rfl,
      fun h => (denK_eq_iff _ _).1 ((denK_eq_iff _ _).2 h).symm,
      fun h₁ h₂ => (denK_eq_iff _ _).1 (((denK_eq_iff _ _).2 h₁).trans ((denK_eq_iff _ _).2 h₂))⟩

/-- **Typed morphisms modulo `OpEquivP`.** -/
@[expose, reducible] def TQ (Γ : Ctx H) (I J : TIface) : Type := Quotient (opSetoid Γ I J)

/-- **The typed Elgot functor on morphisms**: a typed morphism's denotation in the generated
sub-structure. -/
@[expose] noncomputable def tmap {Γ : Ctx H} {I J : TIface} : TQ Γ I J → TArr Γ Cfg Cfg :=
  Quotient.lift (fun m : THomE Γ I J => denKT m.2) fun _ _ h => Subtype.ext ((denK_eq_iff _ _).2 h)

theorem tmap_mk {Γ : Ctx H} {I J : TIface} (m : THomE Γ I J) :
    tmap (Quotient.mk _ m : TQ Γ I J) = denKT m.2 := rfl

/-- **Faithful**: injective modulo `OpEquivP`. -/
theorem tmap_injective {Γ : Ctx H} {I J : TIface} :
    Function.Injective (tmap (Γ := Γ) (I := I) (J := J)) := by
  intro q q' h
  induction q using Quotient.inductionOn
  induction q' using Quotient.inductionOn
  exact Quotient.sound ((denK_eq_iff _ _).1 (congrArg Subtype.val h))

/-- **Preserves the identity.** -/
theorem tmap_id {Γ : Ctx H} {I : TIface} (hI : I.Ok) :
    tmap (Quotient.mk _ ⟨[], thom_id hI⟩ : TQ Γ I I) = (TOps Γ).id Cfg :=
  Subtype.ext denK_nil

/-- **Preserves composition.** -/
theorem tmap_comp {Γ : Ctx H} {I J K : TIface} (m₁ : THomE Γ I J) (m₂ : THomE Γ J K) :
    tmap (Quotient.mk _ ⟨m₁.1 ++ m₂.1, tmor_comp m₁.2 m₂.2⟩ : TQ Γ I K) =
      (TOps Γ).comp (tmap (Quotient.mk _ m₁ : TQ Γ I J)) (tmap (Quotient.mk _ m₂ : TQ Γ J K)) :=
  Subtype.ext (denK_append _ _)

/-- **Preserves iteration**: a typed loop is the iteration of its (generated) step. -/
theorem tmap_loop {Γ : Ctx H} {I J : TIface} {bt : BlockType} {body : List BExpr}
    (h : THom Γ I J [.loop bt body]) :
    tmap (Quotient.mk _ ⟨_, h⟩ : TQ Γ I J) = (TOps Γ).iter (IterOps.GHom.ofGen (TGen.step h)) :=
  Subtype.ext (denK_loop bt body)

/-- **Preserves copairing**: a typed `if` is its condition, the test and the copairing of its
arms. -/
theorem tmap_if {Γ : Ctx H} {I J : TIface} {bt : BlockType} {c t el : List BExpr}
    (h : THom Γ I J [.if_ bt c t el]) :
    tmap (Quotient.mk _ ⟨_, h⟩ : TQ Γ I J) =
      (TOps Γ).comp (IterOps.GHom.ofGen (TGen.ifCond h))
        ((TOps Γ).comp (IterOps.GHom.ofGen TGen.test)
          ((TOps Γ).case (IterOps.GHom.ofGen (TGen.ifThen h))
            (IterOps.GHom.ofGen (TGen.ifElse h)))) :=
  Subtype.ext (denK_if bt c t el)

/-- Composition of typed morphisms modulo `OpEquivP`. -/
@[expose] def tqComp {Γ : Ctx H} {I J K : TIface} : TQ Γ I J → TQ Γ J K → TQ Γ I K :=
  Quotient.map₂ (fun m₁ m₂ => ⟨m₁.1 ++ m₂.1, tmor_comp m₁.2 m₂.2⟩) fun a a' ha b b' hb => by
    have ha' := (denK_eq_iff (H := H) a.1 a'.1).2 ha
    have hb' := (denK_eq_iff (H := H) b.1 b'.1).2 hb
    exact (denK_eq_iff _ _).1 (by rw [denK_append, denK_append, ha', hb'])

/-- **The typed category**: interfaces with valid stack types, typed code modulo `OpEquivP`. -/
instance (Γ : Ctx H) : CategoryTheory.Category (TObj Γ) where
  Hom I J := TQ Γ I.1 J.1
  id I := Quotient.mk _ ⟨[], thom_id I.2⟩
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

/-- The endomorphisms of `Cfg` in the generated sub-structure. -/
@[expose] def TMon (Γ : Ctx H) : Type 1 := TArr Γ Cfg Cfg

/-- Their monoid: `g * g'` is `g'` then `g` (so that composition in `SingleObj` is `comp`). -/
noncomputable instance (Γ : Ctx H) : Monoid (TMon Γ) where
  mul g g' := (TOps Γ).comp (g' : TArr Γ Cfg Cfg) g
  one := (TOps Γ).id Cfg
  mul_assoc g₁ g₂ g₃ := ((tOps_lawful Γ).comp_assoc g₃ g₂ g₁).symm
  one_mul := (tOps_lawful Γ).comp_id
  mul_one := (tOps_lawful Γ).id_comp

/-- **The typed Elgot functor**, bundled: typed code modulo `OpEquivP` into the endomorphism
monoid of the generated sub-structure. -/
noncomputable def typedFunctor (Γ : Ctx H) :
    CategoryTheory.Functor (TObj Γ) (CategoryTheory.SingleObj (TMon Γ)) where
  obj _ := CategoryTheory.SingleObj.star _
  map q := (tmap q : TArr Γ Cfg Cfg)
  map_id I := tmap_id I.2
  map_comp q₁ q₂ := by
    induction q₁ using Quotient.inductionOn
    induction q₂ using Quotient.inductionOn with
    | h m₂ => exact tmap_comp _ m₂

/-- **The typed Elgot functor is faithful.** -/
instance (Γ : Ctx H) : (typedFunctor Γ).Faithful where
  map_injective h := tmap_injective h

/-! ## 4. The premonoidal part -/

/-- **The stack tensor on the stack-pure fragment** (`map_whisker` there): for checked
stack-pure code at a configuration of the checked height in a frame of the checked instance,
appending the passive stack and running is whiskering by it and appending, every exit read at
its target's arity. -/
theorem tmor_whisker {Γ : Ctx H} {I : Iface} {o : Option Nat} {es : List BExpr}
    (hm : Mor Γ I o es) (hp : stackPureL es = true) {f : Frame} {stk : List Val}
    (hf : f.module = I.env.mi) (hs : stk.length = I.h) (rest : List Val) :
    trimK I.env.labels I.env.ret
        ((kOps H).comp ((kOps H).pure appK) (denK es)
          ((⟨rest⟩ : ULift.{1} (List Val)), (⟨(f, stk)⟩ : Cfg))) =
      trimK I.env.labels I.env.ret
        ((kOps H).comp ((kOps H).whisker (ULift.{1} (List Val)) (denK es)) ((kOps H).pure appK)
          ((⟨rest⟩ : ULift.{1} (List Val)), (⟨(f, stk)⟩ : Cfg))) :=
  Silmaril.Proofs.Wasm.Abstract.TypedFunctor.denK_whisker_ops hp (by rw [hs]; exact hm) hf rest

/-- **The stack tensor of the exit monad is #529's**: on all code, at every configuration, the
whiskering equation of `tmor_whisker` is exactly `ExposePStruct.denListXP_whisker`'s equation. -/
theorem whiskK_iff (labels : List Nat) (ret : Nat) (es : List BExpr) (f : Frame)
    (stk rest : List Val) :
    trimK labels ret ((kOps H).comp ((kOps H).pure appK) (denK es)
        ((⟨rest⟩ : ULift.{1} (List Val)), (⟨(f, stk)⟩ : Cfg))) =
      trimK labels ret ((kOps H).comp ((kOps H).whisker (ULift.{1} (List Val)) (denK es))
        ((kOps H).pure appK) ((⟨rest⟩ : ULift.{1} (List Val)), (⟨(f, stk)⟩ : Cfg))) ↔
    obsP labels ret (denListXP (H := H) es f (stk ++ rest)) =
      denListXP es f stk >>= fun r => pure (trimP labels ret (whiskP rest r)) :=
  Silmaril.Proofs.Wasm.Abstract.TypedFunctor.whiskK_iff labels ret es f stk rest

/-- **The obstruction in the raw exit monad: the stack tensor of `PX H` arrows fails for
checked code with a call.** `call 0; drop`, checked at height `0` (the callee `[] → [i32]`), at
a configuration of the checked height in a frame of the checked instance, with one passive
value: the equation of `tmor_whisker` fails. `PX H` admits every answer `Store H × Flow`; the
failing branch answers with no values, which violates `ExposePTyped.ArityResp`, leaves the
passive value on top, and `drop` pops it. So `stackPure` cannot be dropped from `tmor_whisker`
in `PX H`. Under arity-respecting oracles the tensor holds for all checked code
(`ExposePTyped.tmor_tensor`); this is not a counterexample for a codomain of legal answers. -/
theorem exists_not_whisker :
    ∃ (Γ : Ctx Unit) (I : Iface) (es : List BExpr) (f : Frame) (stk rest : List Val),
      Mor Γ I (some I.h) es ∧ stackPureL es = false ∧ f.module = I.env.mi ∧ stk.length = I.h ∧
        ¬ (trimK I.env.labels I.env.ret ((kOps Unit).comp ((kOps Unit).pure appK) (denK es)
            ((⟨rest⟩ : ULift.{1} (List Val)), (⟨(f, stk)⟩ : Cfg))) =
          trimK I.env.labels I.env.ret
            ((kOps Unit).comp ((kOps Unit).whisker (ULift.{1} (List Val)) (denK es))
              ((kOps Unit).pure appK) ((⟨rest⟩ : ULift.{1} (List Val)), (⟨(f, stk)⟩ : Cfg)))) :=
  Silmaril.Proofs.Wasm.Abstract.TypedFunctor.Ex.exists_not_whisker

/-- **Pure code is central**: code denoting a pure map commutes with every whiskered arrow,
run on the context side (`rwhiskK`, `- ⋊ A`); the transfer of `TypedCat.interchange_of_pure`. -/
theorem pure_central_of_denK {es : List BExpr} {φ : Cfg → Cfg}
    (h : denK (H := H) es = (kOps H).pure φ) {A B : Type 1} (g : A → PX H B) :
    (kOps H).comp ((kOps H).whisker Cfg g) (rwhiskK (denK es)) =
      (kOps H).comp (rwhiskK (denK es)) ((kOps H).whisker Cfg g) := by
  rw [Silmaril.Proofs.Wasm.Abstract.TypedFunctor.rwhiskK_pure h,
    Silmaril.Proofs.Wasm.Abstract.TypedFunctor.rwhiskK_pure h]
  exact kOps_lawful.pure_central φ g

/-- The empty code is pure, hence central. -/
theorem denK_nil_pure : denK (H := H) [] = (kOps H).pure id := by
  rw [denK_nil]; rfl

end Silmaril.Wasm.Abstract.TypedFunctor
