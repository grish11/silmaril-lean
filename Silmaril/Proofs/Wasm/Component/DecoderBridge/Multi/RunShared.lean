module

public import Silmaril.Wasm.Component.DecoderBridge.MultiX.Defs
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.GapMachine
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.ExportX
public import Silmaril.Proofs.Wasm.Component.Reference.SplitInit

/-!
# A node's run in the shared core store (`Task.coreRunShared`)

The IR runs an exported function of node `j` alone, from the store its start function left. The
reference machine runs the relocated function in the shared core store: the node's store relocated
along the gap `g` (`Gap.rel`), followed by the objects `U` of later nodes.

* `OwnOk O t`: what `O` owns exists in `t` and is good (the store half of
  `Linking.Split.PartRel`); it is transported to the gap image (`Own.gap`, `OwnOk.gap`), and gives
  the identity `PartRel` of a store with the store extended by `U` (`OwnOk.partRel_app`);
* `steps_part`: host-free runs along `Linking.Split.step_sim` (fresh structures and arrays may be
  renamed: in the shared store they land past `U`);
* `RunInv`, `startRun_inv`: the start run (with its import calls) keeps a split invariant whose
  ownership covers every function of the store;
* `runShared`: the run in the shared store, then the interpreter run (`runCI_complete`, typed by
  the shared store's typing and the callee's type, read off the IR run's first step);
* **`coreRunShared`**: `Task.coreRunShared`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel noHost step_sim Ren.id)
open Silmaril.Proofs.Wasm.Component.Reference (SplitGood Store.app ownOf StoreGood Store.mapH
  FuncInst.mapH)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-! ## Owned objects of a store -/

/-- **What `O` owns exists in `t` and is good** (the store half of `PartRel`). -/
structure OwnOk (O : Own) (t : Store H) : Prop where
  fn : ∀ a, O.fn a → ∃ fi, t.funcs[a]? = some fi ∧ ∀ c, fi.code = .wasm c → O.ModGood fi.module
  gl : ∀ a, O.gl a → ∃ g, t.globals[a]? = some g ∧ O.GoodVal g.value
  st : ∀ a, O.st a → ∃ si, t.structs[a]? = some si ∧ ∀ fv ∈ si.fields, O.GoodFV fv
  ar : ∀ a, O.ar a → ∃ ai, t.arrays[a]? = some ai ∧ ∀ fv ∈ ai.fields, O.GoodFV fv

theorem ownOk_of_partRel {ρ : Ren} {O : Own} {p σ : Store H} (h : PartRel ρ O p σ) : OwnOk O p where
  fn a ha := by
    obtain ⟨fi, h1, fi', _, _, h4⟩ := h.fn a ha
    exact ⟨fi, h1, fun c hc => (h4 c hc).2⟩
  gl a ha := by
    obtain ⟨g, h1, -, h3⟩ := h.gl a ha
    exact ⟨g, h1, h3⟩
  st a ha := by
    obtain ⟨si, h1, -, h3⟩ := h.st a ha
    exact ⟨si, h1, h3⟩
  ar a ha := by
    obtain ⟨ai, h1, -, h3⟩ := h.ar a ha
    exact ⟨ai, h1, h3⟩

theorem getElem?_app_left {α : Type} {l l' : List α} {a : Nat} {x : α} (h : l[a]? = some x) :
    (l ++ l')[a]? = some x := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

/-- **A store with good owned objects is related to itself extended by `U`**, by the identity. -/
theorem OwnOk.partRel_app {O : Own} {t : Store H} (h : OwnOk O t) (U : Store H) :
    PartRel Ren.id O t (Store.app t U) where
  fn a ha := by
    obtain ⟨fi, h1, h2⟩ := h.fn a ha
    exact ⟨fi, h1, fi, getElem?_app_left h1, rfl, fun c hc => ⟨rfl, h2 c hc⟩⟩
  gl a ha := by
    obtain ⟨g, h1, h2⟩ := h.gl a ha
    exact ⟨g, h1, by simpa [Store.app] using getElem?_app_left (l' := U.globals) h1, h2⟩
  st a ha := by
    obtain ⟨si, h1, h2⟩ := h.st a ha
    exact ⟨si, h1, by simpa [Store.app] using getElem?_app_left (l' := U.structs) h1, h2⟩
  ar a ha := by
    obtain ⟨ai, h1, h2⟩ := h.ar a ha
    exact ⟨ai, h1, by simpa [Store.app] using getElem?_app_left (l' := U.arrays) h1, h2⟩
  stInj _ _ _ _ h := h
  arInj _ _ _ _ h := h

section MapH

variable {H' : Type} (f : H → H')

theorem OwnOk.mapH {O : Own} {t : Store H} (h : OwnOk O t) : OwnOk O (Store.mapH f t) where
  fn a ha := by
    obtain ⟨fi, h1, h2⟩ := h.fn a ha
    refine ⟨FuncInst.mapH f fi, ?_, fun c hc => h2 c ?_⟩
    · simp [Store.mapH, h1]
    · exact (Silmaril.Proofs.Wasm.Component.Reference.FuncCode.mapH_eq_wasm f).mp hc
  gl := h.gl
  st := h.st
  ar := h.ar

end MapH

/-! ## The gap image of an ownership -/

/-- The image of an ownership along the gap `g`. -/
def Own.gap (g : Gap H) (O : Own) : Own :=
  ⟨fun a' => ∃ a, O.st a ∧ a' = g.pre.structs.length + a,
    fun a' => ∃ a, O.ar a ∧ a' = g.pre.arrays.length + a,
    fun a' => ∃ a, O.fn a ∧ a' = g.fnMap a,
    fun a' => ∃ a, O.gl a ∧ a' = g.pre.globals.length + a⟩

section Gap

variable (g : Gap H) {O : Own}

theorem goodRef_gap : ∀ {r : Ref}, O.GoodRef r → (Own.gap g O).GoodRef (g.sh.ref r)
  | .i31 _, _ => trivial
  | .null, _ => trivial
  | .struct a, h => ⟨a, h, rfl⟩
  | .array a, h => ⟨a, h, rfl⟩
  | .func a, h => ⟨a, h, rfl⟩
  | .exn _, h => h.elim
  | .host _, h => h.elim
  | .extern r, h => goodRef_gap (r := r) h

theorem goodVal_gap {v : Val} (h : O.GoodVal v) : (Own.gap g O).GoodVal (g.sh.val v) := by
  cases v with
  | ref r => exact goodRef_gap g h
  | num => trivial
  | vec => trivial

theorem goodFV_gap {fv : FieldVal} (h : O.GoodFV fv) : (Own.gap g O).GoodFV (g.sh.fval fv) := by
  cases fv with
  | val v => exact goodVal_gap g h
  | pack => trivial

theorem modGood_gap {m : ModuleInst} (h : O.ModGood m) : (Own.gap g O).ModGood (g.sh.minst m) where
  tags := by simp [GShift.minst, h.tags]
  mems := by simp [GShift.minst, h.mems]
  tables := by simp [GShift.minst, h.tables]
  elems := by simp [GShift.minst, h.elems]
  datas := by simp [GShift.minst, h.datas]
  globals x hx := by
    simp only [GShift.minst_globals, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, h.globals y hy, rfl⟩
  funcs x hx := by
    simp only [GShift.minst_funcs, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, h.funcs y hy, rfl⟩

/-- **Owned objects along the gap.** -/
theorem OwnOk.gap {t : Store H} (hP : g.PreOk t.funcs) (h : OwnOk O t) :
    OwnOk (Own.gap g O) (g.rel t) where
  fn a' ha' := by
    obtain ⟨a, ha, rfl⟩ := ha'
    obtain ⟨fi, h1, h2⟩ := h.fn a ha
    exact ⟨g.sh.finst fi, funcs_gap_of g hP h1, fun c hc => modGood_gap g (h2 c hc)⟩
  gl a' ha' := by
    obtain ⟨a, ha, rfl⟩ := ha'
    obtain ⟨gi, h1, h2⟩ := h.gl a ha
    refine ⟨g.sh.ginst gi, ?_, goodVal_gap g h2⟩
    rw [rel_globals, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.getElem?_map, h1]
    rfl
  st a' ha' := by
    obtain ⟨a, ha, rfl⟩ := ha'
    obtain ⟨si, h1, h2⟩ := h.st a ha
    refine ⟨g.sh.sinst si, by rw [structs_gap, h1]; rfl, fun fv hfv => ?_⟩
    simp only [GShift.sinst, List.mem_map] at hfv
    obtain ⟨fv₀, hfv₀, rfl⟩ := hfv
    exact goodFV_gap g (h2 fv₀ hfv₀)
  ar a' ha' := by
    obtain ⟨a, ha, rfl⟩ := ha'
    obtain ⟨ai, h1, h2⟩ := h.ar a ha
    refine ⟨g.sh.ainst ai, by rw [arrays_gap, h1]; rfl, fun fv hfv => ?_⟩
    simp only [GShift.ainst, List.mem_map] at hfv
    obtain ⟨fv₀, hfv₀, rfl⟩ := hfv
    exact goodFV_gap g (h2 fv₀ hfv₀)

end Gap

/-! ## Invocations and runs -/

/-- **The invocation of an owned function, without arguments, is a good thread.** -/
theorem invoke_good_of {O : Own} {t : Store H} {a : Nat} (ha : O.fn a) :
    O.FrameGood (invoke t a []).frame ∧ O.CodeGood (invoke t a []).code := by
  refine ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, nofun, nofun⟩, nofun⟩, ?_⟩
  refine O.codeGood_append.mpr ⟨O.codeGood_vals.mpr nofun, ?_⟩
  exact Silmaril.Proofs.Wasm.Game.Linking.Split.Own.CodeGood.cons_ref ha (by simp [Own.CodeGood])

/-- **Host-free runs in the shared store, along `Linking.Split.step_sim`.** -/
theorem steps_part {P : Profile} {c c' : Config H}
    (h : Relation.ReflTransGen (Step P noHost) c c') {ρ : Ren} {O : Own} {σ : Store H}
    (hR : PartRel ρ O c.store σ) (hf : O.FrameGood c.frame) (hc : O.CodeGood c.code) :
    ∃ (ρ' : Ren) (O' : Own) (σ' : Store H),
      Relation.ReflTransGen (Step P noHost) ⟨σ, ρ.frame c.frame, ρ.code c.code⟩
        ⟨σ', ρ'.frame c'.frame, ρ'.code c'.code⟩ ∧
      PartRel ρ' O' c'.store σ' ∧ O'.FrameGood c'.frame ∧ O'.CodeGood c'.code := by
  induction h with
  | refl => exact ⟨ρ, O, σ, .refl, hR, hf, hc⟩
  | tail _ hst ih =>
    obtain ⟨ρ₁, O₁, σ₁, hrun, hR₁, hf₁, hc₁⟩ := ih
    obtain ⟨ρ₂, O₂, σ₂, hs, hR₂, hf₂, hc₂, -⟩ := step_sim hst hR₁ hf₁ hc₁
    exact ⟨ρ₂, O₂, σ₂, hrun.tail hs, hR₂, hf₂, hc₂⟩

/-! ## The start run keeps a split invariant -/

/-- **A split configuration whose ownership covers every function of its store.** -/
def RunInv (c : Config H) : Prop :=
  ∃ (ρ : Ren) (O : Own) (σ : Store H), PartRel ρ O c.store σ ∧ O.FrameGood c.frame ∧
    O.CodeGood c.code ∧ ∀ a, a < c.store.funcs.length → O.fn a

theorem RunInv.step {P : Profile} {c c' : Config H} (h : Step P noHost c c') (hg : RunInv c) :
    RunInv c' := by
  obtain ⟨ρ, O, σ, hR, hf, hc, hfn⟩ := hg
  obtain ⟨ρ', O', σ', -, hR', hf', hc', hG, -⟩ := step_sim h hR hf hc
  have hfs := (Silmaril.Wasm.SingleThreaded.Step.framesLocal h).1
  refine ⟨ρ', O', σ', hR', hf', hc', fun a ha => ?_⟩
  rw [hG.fn]
  exact hfn a (by rw [← hfs]; exact ha)

theorem RunInv.steps {P : Profile} {c c' : Config H}
    (h : Relation.ReflTransGen (Step P noHost) c c') (hg : RunInv c) : RunInv c' := by
  induction h with
  | refl => exact hg
  | tail _ hst ih => exact RunInv.step hst ih

/-- **Resuming with a result of good code keeps the invariant.** -/
theorem RunInv.resume {s : Store H} {t : Silmaril.Wasm.SingleThreaded.Thread}
    (hg : RunInv (t.config s)) {r : Silmaril.Wasm.SingleThreaded.CallResult}
    (hr : ∀ O : Own, O.CodeGood r.toAdmin) :
    RunInv ((Silmaril.Wasm.SingleThreaded.resume s t r).config s) := by
  cases hd : Silmaril.Wasm.SingleThreaded.decompose? s (t.config s).code with
  | none =>
    unfold Silmaril.Wasm.SingleThreaded.resume
    simp only [hd]
    exact hg
  | some q =>
    obtain ⟨E, a, h, args⟩ := q
    obtain ⟨ρ, O, σ, hR, hf, hc, hfn⟩ := hg
    obtain ⟨-, yy, -, -, -, -, -, -, -, hX⟩ := Silmaril.Wasm.SingleThreaded.decompose?_sound hd
    unfold Silmaril.Wasm.SingleThreaded.resume
    simp only [hd]
    refine ⟨ρ, O, σ, ?_, hf, ?_, ?_⟩
    · simpa [Silmaril.Wasm.SingleThreaded.Thread.config_store] using hR
    · exact Silmaril.Proofs.Wasm.Game.Linking.Split.Own.CodeGood.fill E
        (xs := vals args ++ [.ref (.func a), yy]) (by rw [← hX]; exact hc) (hr O)
    · simpa [Silmaril.Wasm.SingleThreaded.Thread.config_store] using hfn

theorem codeGood_toCR (O : Own) (r : Silmaril.Wasm.Component.Engine.CallResult) :
    O.CodeGood (Silmaril.Wasm.Component.Engine.Core3.toCR r).toAdmin := by
  cases r with
  | values vs =>
    refine O.codeGood_vals.mpr fun v hv => ?_
    simp only [List.mem_map] at hv
    obtain ⟨w, -, rfl⟩ := hv
    trivial
  | trap => simp [Silmaril.Wasm.Component.Engine.Core3.toCR,
      Silmaril.Wasm.SingleThreaded.CallResult.toAdmin, Own.CodeGood]

open Silmaril.Wasm.Component Silmaril.Wasm.Component.DecoderBridge in
/-- **The IR's start run (with its import calls) keeps the invariant.** -/
theorem startRun_inv {imps : CoreIface} {c c' : irEng.Config Nat}
    {ys : List (Σ _ : (sigN imps.length).Op, Option Payload)}
    (h : Param.StartRunI irEng imps c ys c') (hg : RunInv (c.2.config c.1)) :
    RunInv (c'.2.config c'.1) := by
  induction h with
  | nil run =>
    unfold Engine.CoreEngine.Steps at run
    rw [internalP_eqN] at run
    exact RunInv.steps (FirstCore.steps_of_internal run) hg
  | call run callout hh r rest ih =>
    unfold Engine.CoreEngine.Steps at run
    rw [internalP_eqN] at run
    have h₁ := RunInv.steps (FirstCore.steps_of_internal run) hg
    exact ih (RunInv.resume h₁ (fun O => codeGood_toCR O _))

/-! ## The node's store after its start run -/

section Node

open Silmaril.Wasm.Component Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp (irStore)
open Silmaril.Proofs.Wasm.Component.Reference (storeGood_once splitGood_invoke invoke_good
  instantiateOnce?_noStart)

/-- **The store a node's start function leaves is split**: some ownership owns every function and
its owned objects are good. -/
theorem nodeEnd_own {n : Nat} {cm : Binary.CoreMod} {args : List Impl} {x : NodeRun}
    (hx : NodeEnd n cm args x) (hsplit : splitMod (Binary.coreModule cm) = true)
    (hfun : (Binary.coreModule cm).imports.all
      (fun i => match i.type with | .func _ => true | _ => false) = true) :
    ∃ O : Own, OwnOk O x.store ∧ ∀ a, a < x.store.funcs.length → O.fn a := by
  obtain ⟨-, hp, ys, -, hstart⟩ := hx
  obtain ⟨mtI, f', st₀, -, -, hi, -, hst₀⟩ :=
    Silmaril.Wasm.Component.Engine.Core3.Typed.prepareE?_inv hp
  have hi' : instantiateOnce? (irStore (CoreModule.imports cm).length)
      { Binary.coreModule cm with start := none }
      (Silmaril.Wasm.Link.GC.Preparation.imports (List.range (CoreModule.imports cm).length)) =
      some (x.inst.store, f', none) := by
    rw [instantiateOnce?_noStart,
      show Silmaril.Wasm.Link.GC.Preparation.imports (List.range (CoreModule.imports cm).length) =
        (List.range (CoreModule.imports cm).length).map ExternAddr.func from rfl, hi]
    rfl
  have hprof : Silmaril.Wasm.Link.GC.inProfile { Binary.coreModule cm with start := none } = true := by
    simp only [splitMod, Bool.and_eq_true, List.isEmpty_iff] at hsplit
    simp [Silmaril.Wasm.Link.GC.inProfile, hsplit.1.1.1.1, hsplit.1.1.1.2, hsplit.1.1.2,
      hsplit.1.2, hsplit.2]
    exact List.all_eq_true.mp hfun
  obtain ⟨hgood, hmodg⟩ := storeGood_once hprof hi'
    (fun fi hfi c hc => by
      simp only [irStore, List.mem_map, List.mem_range] at hfi
      obtain ⟨i, -, rfl⟩ := hfi
      cases hc)
    rfl rfl rfl (fun a ha => by simpa [irStore] using ha)
  rcases hstart with ⟨-, -, hxs⟩ | ⟨f, c', vs, hfs, hrun, -, hxs⟩
  · rw [hxs]
    exact ⟨ownOf x.inst.store, ownOk_of_partRel hgood.partRel, fun a ha => ha⟩
  · obtain ⟨y, -, hy⟩ := hst₀ f hfs
    have hfa : (show Nat from f) < x.inst.store.funcs.length := hmodg.funcs f (List.mem_of_getElem? hy)
    have h₀ : RunInv ((Silmaril.Wasm.SingleThreaded.Thread.invoke f []).config x.inst.store) :=
      ⟨Ren.id, ownOf x.inst.store, x.inst.store, hgood.partRel, (invoke_good hfa (fun _ h => by cases h)).1,
        (invoke_good hfa (fun _ h => by cases h)).2, fun a ha => ha⟩
    obtain ⟨ρ, O, σ, hR, -, -, hfn⟩ := startRun_inv hrun h₀
    have e : (c'.2.config c'.1).store = x.store := by
      rw [hxs]; exact Silmaril.Wasm.SingleThreaded.Thread.config_store _ _
    rw [e] at hR hfn
    exact ⟨O, ownOk_of_partRel hR, hfn⟩

theorem nodeSplit_all : ∀ {ps : List (Binary.CoreMod × List Impl)}
    {qs : List (Silmaril.Wasm.Module × List Impl)},
    List.Forall₂ NodeW (coreNodes ps) qs →
    (qs.all fun p => splitMod p.1 &&
      p.1.imports.all (fun i => match i.type with | .func _ => true | _ => false)) = true →
    ∀ p ∈ ps, splitMod (Binary.coreModule p.1) = true ∧ (Binary.coreModule p.1).imports.all
      (fun i => match i.type with | .func _ => true | _ => false) = true
  | [], _, _, _ => fun _ h => by cases h
  | p :: ps, q :: qs, .cons hW hF, hall => by
    simp only [List.all_cons, Bool.and_eq_true] at hall
    intro p' hp'
    rcases List.mem_cons.mp hp' with rfl | hp'
    · obtain ⟨cm, he, hd, -⟩ := hW
      injection he with he₁ he₂
      subst he₁
      have hmod : Binary.coreModule p'.1 = q.1 := by
        unfold Binary.coreModule
        rw [hd]
        rfl
      rw [hmod]
      exact hall.1
    · exact nodeSplit_all hF hall.2 p' hp'

/-- **In the fragment, every node's module is in the split fragment and imports only functions.** -/
theorem nodeSplit_frag {b : ByteArray} {c : Comp Binary.CoreMod} {r : Conformance.RefComponent}
    {ps : List (Binary.CoreMod × List Impl)} (hc : Binary.parseComponent b = .ok c)
    (hr : Conformance.decodeRef b = .ok r) (hf : MultiImpFrag r) (hn : c.nodes = coreNodes ps) :
    ∀ p ∈ ps, splitMod (Binary.coreModule p.1) = true ∧ (Binary.coreModule p.1).imports.all
      (fun i => match i.type with | .func _ => true | _ => false) = true := by
  obtain ⟨-, hw, -, -⟩ := multiImpFrag_inv hf
  obtain ⟨R, hR, hsn⟩ := multiImpFrag_split hf
  obtain ⟨R', hR', -, -, hN⟩ := relW_of_decode hc hr (inFrag_of_hostWired hw)
  rw [hR] at hR'
  cases hR'
  rw [hn] at hN
  exact nodeSplit_all hN hsn

end Node

/-! ## The run in the shared store -/

section Helpers

open Silmaril.Wasm.SingleThreaded (status runC internalC)

/-- An interpreter run is a run of interpreter steps. -/
theorem steps_of_runC {stepC : Config H → Option (Config H)} :
    ∀ (n : Nat) {s s' : Store H} {t t' : Silmaril.Wasm.SingleThreaded.Thread}
      {st : Silmaril.Wasm.SingleThreaded.Status H},
      runC stepC n s t = (s', t', st) →
      Relation.ReflTransGen (fun p q => internalC stepC p = some q) (s, t) (s', t')
  | 0, s, s', t, t', st, h => by
    simp only [runC, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    exact .refl
  | n + 1, s, s', t, t', st, h => by
    simp only [runC] at h
    split at h
    · split at h
      · rename_i s₁ t₁ hi
        exact .head hi (steps_of_runC n h)
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, -⟩ := h
        exact .refl
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      exact .refl

theorem status_of_vals {o : Silmaril.Wasm.SingleThreaded.GrowOracle} {s : Store H}
    {t : Silmaril.Wasm.SingleThreaded.Thread} {ws : List Val} (h : (t.config s).code = vals ws) :
    status o s t = .returned (.values ws) := by
  have hex : ∃ vs, (t.config s).code = vals vs := ⟨_, h⟩
  unfold status
  dsimp only
  rw [dite_eq_left hex, Silmaril.Wasm.SingleThreaded.vals_injective (hex.choose_spec.symm.trans h)]

theorem toAdmin_ne_callRefType (v : Val) (d : DefType) : v.toAdmin ≠ .callRefType d := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin]

theorem invoke_code_ne_vals (s : Store H) (a : Nat) (ws : List Val) :
    (invoke s a []).code ≠ vals ws := by
  intro h
  have hm : Admin.callRefType ((s.funcs[a]?.map FuncInst.type).getD default) ∈ vals ws := by
    rw [← h]
    simp [invoke]
  simp only [vals, List.mem_map] at hm
  obtain ⟨v, -, hv⟩ := hm
  exact toAdmin_ne_callRefType v _ hv

theorem toFlat?_ren (ρ : Ren) (δ : GShift) (v : Val) :
    Silmaril.Wasm.SingleThreaded.toFlat? (ρ.val (δ.val v)) =
      Silmaril.Wasm.SingleThreaded.toFlat? v := by
  cases v <;> rfl

theorem mapM_toFlat?_ren (ρ : Ren) (δ : GShift) :
    ∀ vs : List Val, ((vs.map δ.val).map ρ.val).mapM Silmaril.Wasm.SingleThreaded.toFlat? =
      vs.mapM Silmaril.Wasm.SingleThreaded.toFlat?
  | [] => rfl
  | v :: vs => by
    simp only [List.map_cons, List.mapM_cons, toFlat?_ren, mapM_toFlat?_ren ρ δ vs]

end Helpers

section Shared

open Silmaril.Wasm.Component Silmaril.Wasm.Component.DecoderBridge Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp (gL)
open Silmaril.Wasm.SingleThreaded (Internal status neverFail profile runC internalC)

local notation "CH" => Silmaril.Wasm.Component.Runtime.CanonHost
  (Silmaril.Wasm.Component.Engine.core3 Silmaril.Wasm.SingleThreaded.neverFail)

/-- **A node's run in the shared store**: a host-free run of an IR function from a split store
returning values is an interpreter run of the relocated function in the store relocated along
the gap and extended by `U` (typed), returning the same values. -/
theorem runShared {x : Store Nat} {O : Own} (hok : OwnOk O x)
    (hfn : ∀ a, a < x.funcs.length → O.fn a) (g : Gap CH) (U : Store CH)
    (hP : g.PreOk (Store.mapH gL x).funcs) (hS : StoreOk (Store.app (g.rel (Store.mapH gL x)) U))
    {a : Nat} {c' : irEng.Config Nat} {ys : List FlatValue}
    (hrun : Engine.CoreEngine.Steps irEng (x, irEng.invoke a []) c')
    (hst : irEng.status c'.1 c'.2 = .returned (.values ys)) :
    ∃ y : (core3 neverFail).Config CH,
      Engine.CoreEngine.Steps (core3 neverFail)
        (Store.app (g.rel (Store.mapH gL x)) U, (core3 neverFail).invoke (g.fnMap a) []) y ∧
      (core3 neverFail).status y.1 y.2 = .returned (.values ys) := by
  obtain ⟨s₀, t₀⟩ := c'
  unfold Engine.CoreEngine.Steps at hrun
  rw [internalP_eqN] at hrun
  obtain ⟨s₁, hs₁⟩ : ∃ s₁ : Store Nat, s₁ = s₀ := ⟨s₀, rfl⟩
  subst hs₁
  obtain ⟨t₁, ht₁⟩ : ∃ t₁ : Silmaril.Wasm.SingleThreaded.Thread, t₁ = t₀ := ⟨t₀, rfl⟩
  subst ht₁
  have hrun' : Relation.ReflTransGen (Internal neverFail)
      (x, Silmaril.Wasm.SingleThreaded.Thread.invoke a []) (s₁, t₁) := hrun
  -- the IR's end: values
  obtain ⟨r', hr'⟩ := FirstImp.flatStatus_returned hst
  have hend' : flatStatus (Silmaril.Wasm.Game.statusP (profile neverFail) s₁ t₁) =
      .returned (.values ys) := hst
  rw [hr'] at hend'
  obtain ⟨vs, rfl, hvs⟩ : ∃ vs, r' = .values vs ∧
      vs.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some ys := by
    rcases r' with vs | _
    · simp only [flatStatus] at hend'
      cases hm : vs.mapM Silmaril.Wasm.SingleThreaded.toFlat? with
      | none => rw [hm] at hend'; cases hend'
      | some fvs' =>
        rw [hm] at hend'
        cases hend'
        exact ⟨vs, rfl, hm⟩
    · simp only [flatStatus] at hend'
      cases hend'
  have hs' : status neverFail s₁ t₁ = .returned (.values vs) :=
    (FirstImp.statusP_profile s₁ t₁).symm.trans hr'
  -- the first step: the callee and its type
  obtain ⟨fi, ps, rs, hfi, hexp, hps⟩ : ∃ (fi : FuncInst Nat) (ps rs : Ty (.list .val)),
      x.funcs[a]? = some fi ∧ Expand fi.type (.func ps rs) ∧ ps.toList = [] := by
    rcases Relation.ReflTransGen.cases_head hrun' with he | ⟨y, hy, -⟩
    · exfalso
      cases he
      exact invoke_code_ne_vals x a vs (Silmaril.Wasm.SingleThreaded.status_returned_values hs')
    · obtain ⟨s₂, t₂⟩ := y
      obtain ⟨f₂, code₂, -, hs⟩ := hy
      obtain ⟨pre, args, fi, ps, rs, code, hv, hfi, hexp, hn, -, -⟩ :=
        Silmaril.Proofs.Wasm.Game.invoke_step_shape hs
      have hargs : args = [] := (List.append_eq_nil_iff.mp hv.symm).2
      subst hargs
      refine ⟨fi, ps, rs, hfi, hexp, ?_⟩
      exact List.eq_nil_of_length_eq_zero hn.symm
  have ha : a < x.funcs.length := (List.getElem?_eq_some_iff.mp hfi).1
  have hOa := hfn a ha
  -- the run with renamed host code, along the gap
  have h₁ : Relation.ReflTransGen (Step (profile neverFail) noHost)
      (invoke (Store.mapH gL x) a []) (t₁.config (Store.mapH gL s₁)) :=
    FirstCore.steps_of_internal (internal_mapH hrun')
  have hg₀ : SplitGood (invoke (Store.mapH gL x) a []) :=
    ⟨Ren.id, O, _, (hok.mapH gL).partRel_app {}, (invoke_good_of hOa).1, (invoke_good_of hOa).2⟩
  have hinj := fnMap_injective g (PreOk.le_pre g hP)
  obtain ⟨h₂, -, -⟩ := steps_gap g h₁ hg₀ hP hinj
  rw [← invoke_gap g hP a] at h₂
  -- into the store extended by `U`
  have hO₁ := (hok.mapH gL).gap g hP
  have hgood₁ := invoke_good_of (O := Own.gap g O) (t := g.rel (Store.mapH gL x))
    (a := g.sh.fn a) ⟨a, hOa, rfl⟩
  obtain ⟨ρ', O', σ', h₃, -, -, -⟩ := steps_part h₂ (hO₁.partRel_app U) hgood₁.1 hgood₁.2
  have hfi₁ : (g.rel (Store.mapH gL x)).funcs[g.sh.fn a]? =
      some (g.sh.finst (FuncInst.mapH gL fi)) :=
    funcs_gap_of g hP (by simp [Store.mapH, hfi])
  have hfi₂ : (Store.app (g.rel (Store.mapH gL x)) U).funcs[g.sh.fn a]? =
      some (g.sh.finst (FuncInst.mapH gL fi)) := getElem?_app_left hfi₁
  have e₀ : (⟨Store.app (g.rel (Store.mapH gL x)) U,
      Ren.id.frame (invoke (g.rel (Store.mapH gL x)) (g.sh.fn a) []).frame,
      Ren.id.code (invoke (g.rel (Store.mapH gL x)) (g.sh.fn a) []).code⟩ : Config CH) =
      invoke (Store.app (g.rel (Store.mapH gL x)) U) (g.sh.fn a) [] := by
    simp only [invoke]
    rw [hfi₁, hfi₂]
    simp [Ren.frame, vals]
  rw [e₀] at h₃
  -- the end: values
  have hcode : (t₁.config (Store.mapH gL s₁)).code = vals vs := by
    rw [FirstImp.code_config_mapHG]
    exact Silmaril.Wasm.SingleThreaded.status_returned_values hs'
  obtain ⟨t', hr, ht'⟩ := FirstCore.internal_of_steps (o := neverFail)
    (t := Silmaril.Wasm.SingleThreaded.Thread.invoke (g.sh.fn a) []) h₃
  have hcode' : (t'.config σ').code = vals ((vs.map g.sh.val).map ρ'.val) := by
    rw [ht']
    show ρ'.code (g.sh.code (t₁.config (Store.mapH gL s₁)).code) = _
    rw [hcode, GShift.code_vals, Ren.code_vals]
  have hstat := status_of_vals (o := neverFail) hcode'
  -- typing of the shared store
  obtain ⟨-, ps', rs', -, -, hok₀⟩ := Silmaril.Wasm.Execution.Core.invoke_ok hS
    ⟨_, ps, rs, hfi₂, hexp, by rw [hps]; exact .nil⟩
  have hok₁ : ConfigOk ((Silmaril.Wasm.SingleThreaded.Thread.invoke (g.sh.fn a) []).config
      (Store.app (g.rel (Store.mapH gL x)) U)) rs'.toList := hok₀
  obtain ⟨n, hn⟩ := FirstCore.runCI_complete (I := fun c => ConfigOk c rs'.toList)
    Silmaril.Wasm.SingleThreaded.Exec.typedInv' hok₁ hr (by rw [hstat]; nofun)
  obtain ⟨-, hok', -⟩ := Silmaril.Wasm.SingleThreaded.Exec.runCI_sound_typed n _ _ hok₁ hn
  refine ⟨(σ', t'), steps_of_runC n hn, ?_⟩
  show Silmaril.Wasm.Component.Engine.Core3.statusE neverFail σ' t' = _
  rw [FirstImp.statusE_flat, Silmaril.Wasm.SingleThreaded.Exec.statusI_eq_typed hok', hstat]
  simp only [flatStatus, mapM_toFlat?_ren, hvs]

end Shared

/-! ## `Task.coreRunShared` -/

open Silmaril.Wasm.Component Silmaril.Wasm.Component.DecoderBridge in
/-- **`Task.coreRunShared`.** -/
theorem coreRunShared : Task.coreRunShared := by
  intro b c r ps xs j p x g U nm a c' ys hpc hr hf _ hnodes hxs hpj hxj hP hS _ hrun hst
  obtain ⟨x', hx', hend⟩ := forall₂_getElem? hxs hpj
  rw [hxj] at hx'
  cases hx'
  obtain ⟨hsplit, hfun⟩ := nodeSplit_frag hpc hr hf hnodes p (List.mem_of_getElem? hpj)
  obtain ⟨O, hok, hfn⟩ := nodeEnd_own hend hsplit hfun
  exact runShared hok hfn g U hP hS hrun hst

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi
