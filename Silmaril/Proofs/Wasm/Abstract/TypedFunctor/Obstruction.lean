module

public import Silmaril.Proofs.Wasm.Abstract.TypedFunctor.Basic
public import Silmaril.Proofs.Wasm.Abstract.BodyTrace.Iter

/-! Proofs for `Silmaril.Wasm.Abstract.TypedFunctor`: the stack tensor in the exit monad is
#529's, and it fails for checked code with a call. -/

public section

namespace Silmaril.Proofs.Wasm.Abstract.TypedFunctor

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
open Silmaril.Wasm.Abstract.ExposeP Silmaril.Wasm.Abstract.ExposePStruct
open Silmaril.Wasm.Abstract.TypedFunctor
open Silmaril.Wasm.Abstract.CallXP (POut EvalOXP)
open Silmaril.Wasm.Interp

variable {H : Type}

/-! ## The two sides of the stack tensor -/

theorem whisk_lhs (es : List BExpr) (rest : List Val) (c : Cfg) :
    (kOps H).comp ((kOps H).pure appK) (denK es) ((⟨rest⟩ : ULift.{1} (List Val)), c) =
      denK es (wcfg rest c) := pure_bind _ _

theorem whisk_rhs (es : List BExpr) (rest : List Val) (c : Cfg) :
    (kOps H).comp ((kOps H).whisker (ULift.{1} (List Val)) (denK es)) ((kOps H).pure appK)
      ((⟨rest⟩ : ULift.{1} (List Val)), c) = wcfg rest <$> denK es c := by
  show ((fun b : Cfg => (((⟨rest⟩ : ULift.{1} (List Val)), b) : ULift.{1} (List Val) × Cfg)) <$>
      denK (H := H) es c) >>= (fun a => (pure (appK a) : PX H Cfg)) = _
  rw [bind_pure_comp, Functor.map_map]
  rfl

theorem dec_trimX (labels : List Nat) (ret : Nat) (r : ResP) :
    dec (Except.mapError (trimX labels ret) (enc r)) = trimP labels ret r := by
  rw [← enc_trim, dec_enc]

theorem dec_trimX_whisk (labels : List Nat) (ret : Nat) (rest : List Val) (r : ResP) :
    dec (Except.mapError (trimX labels ret) (Except.map (wcfg rest) (enc r))) =
      trimP labels ret (whiskP rest r) := by
  rw [← enc_trim_whisk, dec_enc]

/-- **The stack tensor in the exit monad is #529's**, on all code. -/
theorem whiskK_iff (labels : List Nat) (ret : Nat) (es : List BExpr) (f : Frame)
    (stk rest : List Val) :
    trimK labels ret ((kOps H).comp ((kOps H).pure appK) (denK es)
        ((⟨rest⟩ : ULift.{1} (List Val)), (⟨(f, stk)⟩ : Cfg))) =
      trimK labels ret ((kOps H).comp ((kOps H).whisker (ULift.{1} (List Val)) (denK es))
        ((kOps H).pure appK) ((⟨rest⟩ : ULift.{1} (List Val)), (⟨(f, stk)⟩ : Cfg))) ↔
    obsP labels ret (denListXP (H := H) es f (stk ++ rest)) =
      denListXP es f stk >>= fun r => pure (trimP labels ret (whiskP rest r)) := by
  rw [whisk_lhs, whisk_rhs]
  have hl : (trimK labels ret (denK (H := H) es (wcfg rest ⟨(f, stk)⟩))).run =
      enc <$> obsP labels ret (denListXP (H := H) es f (stk ++ rest)) := by
    change Except.mapError (trimX labels ret) <$> (enc <$> denListXP es f (stk ++ rest)) = _
    unfold obsP
    rw [map_bind, Functor.map_map, ← bind_pure_comp]
    congr 1
    funext r
    rw [map_pure, enc_trim]
  have hr : (trimK labels ret (wcfg rest <$> denK (H := H) es ⟨(f, stk)⟩)).run =
      enc <$> (denListXP (H := H) es f stk >>= fun r => pure (trimP labels ret (whiskP rest r))) := by
    change Except.mapError (trimX labels ret) <$> (wcfg rest <$> denK es ⟨(f, stk)⟩).run = _
    rw [ExceptT.run_map]
    change Except.mapError (trimX labels ret) <$>
      (Except.map (wcfg rest) <$> (enc <$> denListXP es f stk)) = _
    rw [map_bind, Functor.map_map, Functor.map_map, ← bind_pure_comp]
    congr 1
    funext r
    rw [map_pure, enc_trim_whisk]
  constructor
  · intro h
    have h' := congrArg (fun x => dec <$> ExceptT.run x) h
    simp only [hl, hr, Functor.map_map] at h'
    simpa only [dec_enc, id_map'] using h'
  · intro h
    apply ExceptT.ext
    rw [hl, hr, h]

/-! ## A checked call breaks the tensor -/

namespace Ex

/-- The function type `[] → [i32]`. -/
def d₁ : Validation.DefType :=
  .defn (.group (.cons (.sub true .nil (.func .nil (.cons (.num (.int .i32)) .nil))) .nil)) 0

/-- A host function of type `[] → [i32]`. -/
def fi₁ : FuncInst Unit := ⟨d₁, {}, .host ()⟩

theorem storeChk₁ : StoreChkE (ehExt ([] : List TagInst)) [fi₁] := by
  intro a fi fn ps rs ha hc _
  rcases a with _ | a
  · simp at ha
    subst ha
    cases hc
  · simp at ha

/-- The store context: no tags, one host function of type `[] → [i32]`. -/
def Γ₁ : Ctx Unit := ⟨[], [fi₁], storeChk₁⟩

def mi₁ : ModuleInst := { funcs := [0] }

/-- The interface: no locals, no labels, no results, the empty stack. -/
def I₁ : Iface := ⟨⟨mi₁, 0, 0, []⟩, 0⟩

/-- `call 0; drop`. -/
def es₁ : List BExpr := [.op (.call ⟨0⟩) [], .op .drop []]

theorem mor₁ : Mor Γ₁ I₁ (some 0) es₁ := by
  show chkIn Γ₁ I₁.env (some I₁.h) es₁ = some (some 0)
  decide +kernel

def s₁ : Store Unit := { funcs := [fi₁] }

def f₁ : Frame := { module := mi₁ }

def v₁ : Val := ofInt .i32 0

/-- The oracle: every call returns no values. -/
def C₁ : Abstract.CallRel Unit := fun s _ _ out => out = (s, .normal [])

/-- With one passive value below, the answer short of the callee's result makes `drop` pop the
passive value: the run falls through with the empty stack. -/
theorem run₁ : EvalOXP C₁ s₁ f₁ [v₁] es₁ (s₁, f₁, .flow (.normal [])) :=
  .callOk (stk₁ := [v₁]) (a := 0) (fi := fi₁) (ps := []) (rs := [.num (.int .i32)]) (vs := [])
    .nil rfl rfl rfl rfl (.opOk (fun _ h => by cases h) .nil rfl .nil)

theorem run_bind_pure {X Y : Type 1} (x : M (CallSig Unit) Unit X) (g : X → Y) (s : St Unit) :
    ((x >>= fun r => pure (g r)).run s).run =
      ((x.run s).run >>= fun y => pure (Except.map (fun p => (g p.1, p.2)) y)) := by
  rw [bind_pure_comp, StateT.run_map, ExceptT.run_map, map_eq_bind_pure_comp]
  rfl

theorem not_whisker₁ :
    ¬ (obsP I₁.env.labels I₁.env.ret (denListXP (H := Unit) es₁ f₁ ([] ++ [v₁])) =
      denListXP es₁ f₁ [] >>= fun r => pure (trimP I₁.env.labels I₁.env.ret (whiskP [v₁] r))) := by
  intro heq
  obtain ⟨cs, hl⟩ := (Abstract.FunctorP.evalOXP_iff_log (fun h => by cases h)).1 run₁
  have hp := ((Abstract.FunctorP.evalLXP_iff (fun h => by cases h)).1 hl).2
  have hp' := BodyTrace.path_map
    (d := fun y => Except.map (fun p => (trimP I₁.env.labels I₁.env.ret p.1, p.2)) y) hp
  rw [← run_bind_pure] at hp'
  change Abstract.BodyTrace.Path
    (((obsP I₁.env.labels I₁.env.ret (denListXP (H := Unit) es₁ f₁ ([] ++ [v₁]))).run ⟨s₁⟩).run)
      cs _ at hp'
  rw [heq, run_bind_pure] at hp'
  obtain ⟨r', -, he⟩ := BodyTrace.path_map_inv hp'
  rcases r' with ((_ | ⟨⟨⟨f, ((vs | ⟨n, vs⟩ | vs | _ | a) | ⟨a, args, n⟩)⟩⟩, st⟩)) | _ <;>
    simp [BodyTrace.mapEnd, Except.map, trimP, whiskP] at he

theorem exists_not_whisker :
    ∃ (Γ : Ctx Unit) (I : Iface) (es : List BExpr) (f : Frame) (stk rest : List Val),
      Mor Γ I (some I.h) es ∧ stackPureL es = false ∧ f.module = I.env.mi ∧ stk.length = I.h ∧
        ¬ (trimK I.env.labels I.env.ret ((kOps Unit).comp ((kOps Unit).pure appK) (denK es)
            ((⟨rest⟩ : ULift.{1} (List Val)), (⟨(f, stk)⟩ : Cfg))) =
          trimK I.env.labels I.env.ret
            ((kOps Unit).comp ((kOps Unit).whisker (ULift.{1} (List Val)) (denK es))
              ((kOps Unit).pure appK) ((⟨rest⟩ : ULift.{1} (List Val)), (⟨(f, stk)⟩ : Cfg)))) :=
  ⟨Γ₁, I₁, es₁, f₁, [], [v₁], mor₁, by decide +kernel, rfl, rfl,
    fun h => not_whisker₁ ((whiskK_iff _ _ _ _ _ _).1 h)⟩

end Ex

end Silmaril.Proofs.Wasm.Abstract.TypedFunctor
