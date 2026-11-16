module

public import Silmaril.Wasm.Abstract.TypedFunctor.Defs
public import Silmaril.Wasm.Abstract.ExposePStruct.Thms
public import Silmaril.Wasm.Abstract.FunctorP.Thms

/-! Proofs for `Silmaril.Wasm.Abstract.TypedFunctor`. -/

public section

namespace Silmaril.Proofs.Wasm.Abstract.TypedFunctor

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
open Silmaril.Wasm.Abstract.ExposeP Silmaril.Wasm.Abstract.ExposePStruct
open Silmaril.Wasm.Abstract.TypedFunctor
open Silmaril.Wasm.Abstract.CallXP (POut)

variable {H : Type}

/-! ## The encoding -/

theorem dec_enc (r : ResP) : dec (enc r) = r := by
  rcases r with ⟨f, ((vs | ⟨n, vs⟩ | vs | _ | a) | ⟨a, args, n⟩)⟩ <;> rfl

theorem enc_dec (x : Except Exit Cfg) : enc (dec x) = x := by
  rcases x with ⟨f, (⟨n, vs⟩ | vs | _ | a | ⟨a, args, n⟩)⟩ | ⟨f, vs⟩ <;> rfl

theorem ofK_toK (g : PHom H Cfg ResP) : ofK (toK g) = g := by
  funext c
  change dec <$> (enc <$> g c) = g c
  rw [Functor.map_map]
  conv_rhs => rw [← id_map (g c)]
  congr 1
  funext r
  exact dec_enc r

theorem toK_ofK (k : Cfg → PX H Cfg) : toK (ofK k) = k := by
  funext c
  change enc <$> (dec <$> (k c).run) = (k c).run
  rw [Functor.map_map]
  conv_rhs => rw [← id_map (k c).run]
  congr 1
  funext r
  exact enc_dec r

/-! ## Faithfulness -/

theorem erasedRun_inj {f g : PHom H Cfg ResP}
    (h : Abstract.BodyTrace.erasedRun f = Abstract.BodyTrace.erasedRun g) : f = g := by
  have he : ∀ X : Type 1, (Abstract.BodyTrace.eraseTrap : Except PUnit.{2} X → Except PUnit.{2} X) = id := by
    intro X; funext r; rcases r with ⟨⟨⟩⟩ | _ <;> rfl
  have hr : ∀ k : PHom H Cfg ResP, Abstract.BodyTrace.erasedRun k = fun s a => ((k a).run s).run := by
    intro k; funext s a
    simp only [Abstract.BodyTrace.erasedRun, he, id, bind_pure]
  rw [hr, hr] at h
  funext a s
  exact congrFun (congrFun h s) a

theorem opEquivP_iff_eq (es es' : List BExpr) :
    Abstract.FunctorP.OpEquivP H es es' ↔ denL (H := H) es = denL es' :=
  (Abstract.FunctorP.opEquivP_iff es es').symm.trans ⟨erasedRun_inj, congrArg _⟩

/-! ## Identity and composition -/

theorem toK_idP : toK (idP : PHom H Cfg ResP) = (kOps H).id Cfg := by
  funext c
  apply ExceptT.ext
  change enc <$> (pure _ : M (CallSig H) H ResP) = pure (Except.ok c)
  rw [map_pure]
  rfl

theorem toK_seqP (g₁ g₂ : PHom H Cfg ResP) :
    toK (seqP g₁ g₂) = (kOps H).comp (toK g₁) (toK g₂) := by
  funext c
  apply ExceptT.ext
  change enc <$> (g₁ c >>= contP g₂) = ((toK g₁ c) >>= toK g₂).run
  rw [ExceptT.run_bind]
  change enc <$> (g₁ c >>= contP g₂) = (enc <$> g₁ c) >>= _
  rw [map_bind, bind_map_left]
  congr 1
  funext r
  rcases r with ⟨f, ((vs | ⟨n, vs⟩ | vs | _ | a) | ⟨a, args, n⟩)⟩
  · rfl
  all_goals (change enc <$> (pure _ : M (CallSig H) H ResP) = _; rw [map_pure]; rfl)

/-! ## Iteration -/

theorem distribute_encStep (x : ResP ⊕ Cfg) :
    Silmaril.Elgot.ExceptT.distribute (encStep x) = Sum.map enc id x := by
  rcases x with ⟨f, ((vs | ⟨n, vs⟩ | vs | _ | a) | ⟨a, args, n⟩)⟩ | c <;> rfl

theorem toK_iter (F : Cfg → M (CallSig H) H (ResP ⊕ Cfg)) :
    toK (Silmaril.Elgot.iter F) = (kOps H).iter (stepK F) := by
  have hb : Silmaril.Elgot.ExceptT.body (stepK F) =
      Silmaril.Elgot.mapReturn F (Silmaril.Elgot.liftPure enc) := by
    funext a
    change (encStep <$> F a) >>= (pure ∘ Silmaril.Elgot.ExceptT.distribute) = _
    rw [bind_map_left]
    unfold Silmaril.Elgot.mapReturn
    congr 1
    funext x
    rw [Function.comp_apply, distribute_encStep]
    rcases x with r | c
    · simp [Silmaril.Elgot.liftPure]
    · rfl
  funext c
  apply ExceptT.ext
  change enc <$> Silmaril.Elgot.iter F c = Silmaril.Elgot.iter (Silmaril.Elgot.ExceptT.body (stepK F)) c
  rw [hb, ← Silmaril.Elgot.LawfulElgotMonad.naturality]
  exact (bind_pure_comp _ _).symm

/-! ## Copairing: `if` -/

theorem stuck_bind {X Y : Type 1} (g : X → M (CallSig H) H Y) :
    (stuck >>= g : M (CallSig H) H Y) = stuck := by
  funext s
  change ((stuck >>= g : M (CallSig H) H Y).run s) = (stuck : M (CallSig H) H Y).run s
  rw [StateT.run_bind]
  apply ExceptT.ext
  simp [stuck, ExceptT.run_bind, StateT.run, ExceptT.run_mk]

theorem map_stuck {X Y : Type 1} (g : X → Y) : (g <$> stuck : M (CallSig H) H Y) = stuck := by
  rw [map_eq_bind_pure_comp, stuck_bind]

theorem toK_stuck {X : Type 1} :
    (ExceptT.mk (stuck : M (CallSig H) H (Except Exit X)) : PX H X) = ExceptT.mk stuck := rfl

theorem pxStuck_bind {X Y : Type 1} (g : X → PX H Y) :
    ((ExceptT.mk stuck : PX H X) >>= g) = ExceptT.mk stuck := by
  apply ExceptT.ext
  rw [ExceptT.run_bind]
  exact stuck_bind _

/-- The arms of an `if`, after a fallthrough of its condition. -/
noncomputable def armP (bt : BlockType) (gt ge : PHom H Cfg ResP) : PHom H Cfg ResP :=
  fun c => ifKP bt gt ge ⟨(c.down.1, .flow (.normal c.down.2))⟩

theorem ifP_eq_seqP (bt : BlockType) (gc gt ge : PHom H Cfg ResP) :
    ifP bt gc gt ge = seqP gc (armP bt gt ge) := by
  funext c
  change gc c >>= ifKP bt gt ge = gc c >>= contP (armP bt gt ge)
  congr 1
  funext r
  rcases r with ⟨f, ((vs | ⟨n, vs⟩ | vs | _ | a) | ⟨a, args, n⟩)⟩ <;> rfl

theorem toK_armP (bt : BlockType) (gt ge : PHom H Cfg ResP) :
    toK (armP bt gt ge) = (kOps H).comp testK
      ((kOps H).case (toK (blockP bt gt)) (toK (blockP bt ge))) := by
  funext c
  rcases c with ⟨f, _ | ⟨cv, stk⟩⟩
  · change ExceptT.mk (enc <$> stuck) = (ExceptT.mk stuck : PX H (Cfg ⊕ Cfg)) >>= _
    rw [pxStuck_bind, map_stuck]
  · cases h : truthy cv with
    | none =>
      change ExceptT.mk (enc <$> ifKP bt gt ge ⟨(f, .flow (.normal (cv :: stk)))⟩) =
        testK ⟨(f, cv :: stk)⟩ >>= _
      simp only [ifKP, testK, h]
      rw [pxStuck_bind, map_stuck]
    | some b =>
      change ExceptT.mk (enc <$> ifKP bt gt ge ⟨(f, .flow (.normal (cv :: stk)))⟩) =
        testK ⟨(f, cv :: stk)⟩ >>= _
      simp only [ifKP, testK, h, pure_bind]
      cases ha : arity f bt with
      | none =>
        cases b
        · change ExceptT.mk (enc <$> stuck) = ExceptT.mk (enc <$> blockP bt ge ⟨(f, stk)⟩)
          simp only [blockP, ha]
        · change ExceptT.mk (enc <$> stuck) = ExceptT.mk (enc <$> blockP bt gt ⟨(f, stk)⟩)
          simp only [blockP, ha]
      | some p =>
        rcases p with ⟨np, nr⟩
        cases b
        · change _ = ExceptT.mk (enc <$> blockP bt ge ⟨(f, stk)⟩)
          simp only [blockP, ha, Bool.false_eq_true, ↓reduceIte]
        · change _ = ExceptT.mk (enc <$> blockP bt gt ⟨(f, stk)⟩)
          simp only [blockP, ha, ↓reduceIte]

theorem toK_ifP (bt : BlockType) (gc gt ge : PHom H Cfg ResP) :
    toK (ifP bt gc gt ge) = (kOps H).comp (toK gc) ((kOps H).comp testK
      ((kOps H).case (toK (blockP bt gt)) (toK (blockP bt ge)))) := by
  rw [ifP_eq_seqP, toK_seqP, toK_armP]

/-! ## The stack tensor -/

theorem enc_trim_whisk (labels : List Nat) (ret : Nat) (rest : List Val) (r : ResP) :
    enc (trimP labels ret (whiskP rest r)) =
      Except.mapError (trimX labels ret) (Except.map (wcfg rest) (enc r)) := by
  rcases r with ⟨f, ((vs | ⟨n, vs⟩ | vs | _ | a) | ⟨a, args, n⟩)⟩ <;> rfl

theorem enc_trim (labels : List Nat) (ret : Nat) (r : ResP) :
    enc (trimP labels ret r) = Except.mapError (trimX labels ret) (enc r) := by
  rcases r with ⟨f, ((vs | ⟨n, vs⟩ | vs | _ | a) | ⟨a, args, n⟩)⟩ <;> rfl

theorem denK_whisker {tags : List TagInst} {F : List (FuncInst H)} {env : Env}
    {es : List BExpr} {o : Option Nat} {f : Frame} {stk : List Val}
    (hp : stackPureL es = true)
    (hc : Interp.chkE (Interp.ehExt tags) F env.mi env.nl env.ret env.labels (some stk.length) es =
      some o)
    (hf : f.module = env.mi) (rest : List Val) :
    trimK env.labels env.ret (denK (H := H) es (wcfg rest ⟨(f, stk)⟩)) =
      trimK env.labels env.ret (wcfg rest <$> denK es ⟨(f, stk)⟩) := by
  apply ExceptT.ext
  change Except.mapError (trimX env.labels env.ret) <$> (enc <$> denListXP es f (stk ++ rest)) =
    Except.mapError (trimX env.labels env.ret) <$> (wcfg rest <$> denK es ⟨(f, stk)⟩).run
  rw [ExceptT.run_map]
  change _ = Except.mapError (trimX env.labels env.ret) <$>
    (Except.map (wcfg rest) <$> (enc <$> denListXP es f stk))
  have hw := denListXP_whisker (H := H) hp hc hf rest
  unfold obsP at hw
  have hL : Except.mapError (trimX env.labels env.ret) <$> (enc <$> denListXP es f (stk ++ rest)) =
      enc <$> (denListXP (H := H) es f (stk ++ rest) >>= fun r => pure (trimP env.labels env.ret r)) := by
    rw [map_bind, Functor.map_map, ← bind_pure_comp]
    congr 1
    funext r
    rw [map_pure, enc_trim]
  rw [hL, hw, map_bind, Functor.map_map, Functor.map_map, ← bind_pure_comp]
  congr 1
  funext r
  rw [map_pure, enc_trim_whisk]

theorem denK_whisker_ops {tags : List TagInst} {F : List (FuncInst H)} {env : Env}
    {es : List BExpr} {o : Option Nat} {f : Frame} {stk : List Val}
    (hp : stackPureL es = true)
    (hc : Interp.chkE (Interp.ehExt tags) F env.mi env.nl env.ret env.labels (some stk.length) es =
      some o)
    (hf : f.module = env.mi) (rest : List Val) :
    trimK env.labels env.ret
        ((kOps H).comp ((kOps H).pure appK) (denK es)
          ((⟨rest⟩ : ULift.{1} (List Val)), (⟨(f, stk)⟩ : Cfg))) =
      trimK env.labels env.ret
        ((kOps H).comp ((kOps H).whisker (ULift.{1} (List Val)) (denK es)) ((kOps H).pure appK)
          ((⟨rest⟩ : ULift.{1} (List Val)), (⟨(f, stk)⟩ : Cfg))) := by
  have h1 : (kOps H).comp ((kOps H).pure appK) (denK es)
      ((⟨rest⟩ : ULift.{1} (List Val)), (⟨(f, stk)⟩ : Cfg)) =
      denK es (wcfg rest ⟨(f, stk)⟩) := pure_bind _ _
  have h2 : (kOps H).comp ((kOps H).whisker (ULift.{1} (List Val)) (denK es)) ((kOps H).pure appK)
      ((⟨rest⟩ : ULift.{1} (List Val)), (⟨(f, stk)⟩ : Cfg)) =
      wcfg rest <$> denK es (⟨(f, stk)⟩ : Cfg) := by
    show ((fun b : Cfg => (((⟨rest⟩ : ULift.{1} (List Val)), b) : ULift.{1} (List Val) × Cfg)) <$>
        denK (H := H) es (⟨(f, stk)⟩ : Cfg)) >>= (fun a => (pure (appK a) : PX H Cfg)) = _
    rw [bind_pure_comp, Functor.map_map]
    rfl
  rw [h1, h2]
  exact denK_whisker hp hc hf rest

/-! ## Centrality -/

theorem rwhiskK_pure {A : Type 1} {k : Cfg → PX H Cfg} {φ : Cfg → Cfg} (h : k = (kOps H).pure φ) :
    (rwhiskK k : Cfg × A → PX H (Cfg × A)) = (kOps H).pure (Prod.map φ (id : A → A)) := by
  funext p
  rw [h]
  change (fun c : Cfg => ((c, p.2) : Cfg × A)) <$> (pure (φ p.1) : PX H Cfg) =
    (pure (φ p.1, p.2) : PX H (Cfg × A))
  rw [map_pure]

end Silmaril.Proofs.Wasm.Abstract.TypedFunctor
