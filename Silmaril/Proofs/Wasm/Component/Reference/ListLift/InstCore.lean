module

public import Silmaril.Proofs.Wasm.Component.Reference.ListLift.Phases
public import Silmaril.Proofs.Wasm.Component.Reference.InstRun

/-!
# The core instance of `ListComp.toRef`

The `core instance (instantiate 0)` definition of `ListComp.toRef` instantiates the module in the
empty core store of `core3P P`. For a component instantiated as `ListComp.Inst` says:

* the initialiser runs of instantiation allocate no memory (`evalConst?_mems`,
  `evalGlobals?_mems`, `evalExprs?_mems`, `evalExprss?_mems`), so the memories of an instance
  built in the empty store are at the addresses `0, 1, …` (`instantiateOnce?_memExports`);
* `lookup_memExport`: the core export named `memName` (memory `memIdx`) is memory address
  `memIdx`;
* `lookup_funcName`: the core export named by a function export name `n` is the function
  address `c.coreAddr I n`;
* `coreFactsL`: the facts the instantiation run needs, over `core3P P`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.ListLift

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.ListLift
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-! ## Initialiser runs allocate no memory -/

theorem structNew?_mems {s s' : Store H} {f : Frame} {vs vs' : List Execution.Core.Val}
    {x : TypeIdx} (h : structNew? s f vs x = some (s', vs')) : s'.mems = s.mems := by
  unfold structNew? at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨d, -, fs, -, ⟨pre, args⟩, -, h⟩ := h
  split at h
  · cases h; rfl
  · cases h

theorem arrayNewFixed?_mems {s s' : Store H} {f : Frame} {vs vs' : List Execution.Core.Val}
    {x : TypeIdx} {n : Fin (2 ^ 32)} (h : arrayNewFixed? s f vs x n = some (s', vs')) :
    s'.mems = s.mems := by
  unfold arrayNewFixed? at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨d, -, ft, -, ⟨pre, args⟩, -, h⟩ := h
  split at h
  · cases h; rfl
  · cases h

/-- Constant instructions keep the memories. -/
theorem constInstr?_mems {s s' : Store H} {f : Frame} {vs vs' : List Execution.Core.Val}
    {i : Instr} (h : constInstr? s f vs i = some (s', vs')) : s'.mems = s.mems := by
  cases i <;> simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  all_goals try first
    | (obtain ⟨rfl, -⟩ := h; rfl)
    | (obtain ⟨_, -, h⟩ := h; try first | (obtain ⟨rfl, -⟩ := h; rfl))
  case refI31 => obtain ⟨_, -, h⟩ := h; cases h; rfl
  case structNew => exact structNew?_mems h
  case structNewDefault => obtain ⟨_, -, _, -, h⟩ := h; exact structNew?_mems h
  case arrayNew => obtain ⟨_, -, h⟩ := h; exact arrayNewFixed?_mems h
  case arrayNewDefault =>
    obtain ⟨_, -, _, -, _, -, _, -, h⟩ := h; exact arrayNewFixed?_mems h
  case arrayNewFixed => exact arrayNewFixed?_mems h
  case externConvertAny =>
    split at h
    · split at h <;> (cases h; rfl)
    · cases h
  case anyConvertExtern =>
    split at h
    · cases h; rfl
    · cases h; rfl
    · cases h
  case intBinOp =>
    split at h
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨_, -, _, -, _, -, h⟩ := h
      split at h
      · cases h; rfl
      · cases h
    · cases h

/-- Constant expressions keep the memories. -/
theorem constExpr?_mems {s s' : Store H} {f : Frame} {e : Expr} {vs : List Execution.Core.Val}
    (h : constExpr? s f e = some (s', vs)) : s'.mems = s.mems := by
  unfold constExpr? at h
  suffices ∀ (es : Expr) (st : Store H × List Execution.Core.Val)
      (r : Store H × List Execution.Core.Val),
      es.foldlM (fun (st : Store H × List Execution.Core.Val) i => constInstr? st.1 f st.2 i) st =
        some r → r.1.mems = st.1.mems from this e (s, []) (s', vs) h
  intro es
  induction es with
  | nil =>
    intro st r h
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | cons i es ih =>
    intro st r h
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨st₁, h₁, h₂⟩ := h
    exact (ih st₁ r h₂).trans (constInstr?_mems (s' := st₁.1) (vs' := st₁.2) h₁)

/-- Constant evaluation keeps the memories. -/
theorem evalConst?_mems {s s' : Store H} {f : Frame} {e : Expr} {v : Execution.Core.Val}
    (h : evalConst? s f e = some (s', v)) : s'.mems = s.mems := by
  unfold evalConst? at h
  split at h
  · rename_i s'' w hw
    cases h
    exact constExpr?_mems hw
  · cases h

/-- `$evalglobals` keeps the memories. -/
theorem evalGlobals?_mems :
    ∀ {s : Store H} {f : Frame} {gts : List Validation.CGlobalType} {es : List Expr}
      {s₁ : Store H} {f₁ : Frame} {vs : List Execution.Core.Val},
      evalGlobals? evalConst? s f gts es = some (s₁, f₁, vs) → s₁.mems = s.mems
  | s, f, [], [], s₁, f₁, vs, h => by
    simp only [evalGlobals?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  | s, f, g :: gs, e :: es, s₁, f₁, vs, h => by
    simp only [evalGlobals?] at h
    split at h
    · cases h
    · rename_i s' v he
      split at h
      · cases h
      · rename_i s'' f'' vs' hr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have h₁ := evalGlobals?_mems hr
        have h₂ := evalConst?_mems he
        exact h₁.trans h₂
  | s, f, [], _ :: _, s₁, f₁, vs, h => by simp [evalGlobals?] at h
  | s, f, _ :: _, [], s₁, f₁, vs, h => by simp [evalGlobals?] at h

/-- `$evalexprs` keeps the memories. -/
theorem evalExprs?_mems :
    ∀ {s : Store H} {f : Frame} {es : List Expr} {s' : Store H} {f' : Frame} {rs : List Ref},
      evalExprs? evalConst? s f es = some (s', f', rs) → s'.mems = s.mems
  | s, f, [], s', f', rs, h => by
    simp only [evalExprs?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  | s, f, e :: es, s', f', rs, h => by
    simp only [evalExprs?] at h
    split at h
    · rename_i s₁ r he
      split at h
      · cases h
      · rename_i s'' f'' rs' hr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact (evalExprs?_mems hr).trans (evalConst?_mems he)
    · cases h

/-- `$evalexprss` keeps the memories. -/
theorem evalExprss?_mems :
    ∀ {s : Store H} {f : Frame} {ess : List (List Expr)} {s' : Store H} {f' : Frame}
      {rss : List (List Ref)},
      evalExprss? evalConst? s f ess = some (s', f', rss) → s'.mems = s.mems
  | s, f, [], s', f', rss, h => by
    simp only [evalExprss?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  | s, f, es :: ess, s', f', rss, h => by
    simp only [evalExprss?] at h
    split at h
    · cases h
    · rename_i s₁ f₁ rs he
      split at h
      · cases h
      · rename_i s'' f'' rss' hr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact (evalExprss?_mems hr).trans (evalExprs?_mems he)

/-! ## The memories of an instance -/

/-- The exports of the module instance built by `prepare?` are allocated from the module's
exports, against memories after the imported ones at the next addresses of the store. -/
theorem prepare?_memExports {s : Store H} {m : Module} {xas : List ExternAddr} {c : Config H}
    {st : Option FuncIdx} (hp : prepare? evalConst? s m xas = some (c, st)) :
    ∃ ei : ModuleInst,
      List.Forall₂ (fun e x => allocExport? ei e = some x) m.exports c.frame.module.exports ∧
      ei.mems = ExternAddr.mems xas ++ List.range' s.mems.length m.memories.length := by
  unfold prepare? at hp
  split at hp
  · split at hp
    · cases hp
    rename_i s₁ f₁ valsG hG
    split at hp
    · cases hp
    rename_i s₂ f₂ refsT hT
    split at hp
    · cases hp
    rename_i s₃ f₃ refsE hE
    split at hp
    · cases hp
    rename_i s₄ mi hM
    obtain ⟨tagTypes, funcTypes, xi, -, -, hX, hmi, -⟩ := allocModule?_inv hM
    have hc : c.frame.module = mi := by rw [← (Prod.mk.inj (Option.some.inj hp)).1]
    have h₃ : s₃.mems = s.mems :=
      ((evalExprss?_mems hE).trans (evalExprs?_mems hT)).trans (evalGlobals?_mems hG)
    rw [hc, hmi]
    refine ⟨_, mapM_forall₂ hX, ?_⟩
    rw [h₃]
  · cases hp

/-- **The memories of an instance built in the empty store are at the addresses `0, 1, …`.** -/
theorem instantiateOnce?_memExports {m : Module} {s' : Store H} {f' : Frame}
    {st : Option FuncIdx} (h : instantiateOnce? ({} : Store H) m [] = some (s', f', st)) :
    ∃ ei : ModuleInst,
      List.Forall₂ (fun e x => allocExport? ei e = some x) m.exports f'.module.exports ∧
      ei.mems = List.range' 0 m.memories.length := by
  unfold instantiateOnce? at h
  split at h
  · cases h
  · rename_i s₁ f₁ vs hg
    obtain ⟨c, hp, hf⟩ := prepareDirect?_frame h
    obtain ⟨ei, hX, hm⟩ := prepare?_memExports hp
    have h₁ : s₁.mems = [] := evalGlobals?_mems hg
    refine ⟨ei, hf ▸ hX, ?_⟩
    rw [hm, h₁, ExternAddr.mems_append, ExternAddr.mems_globalAddrs]
    rfl

/-! ## Looking up exports by name -/

/-- The lookup of the name of an allocated export finds its address. -/
theorem lookup_allocExport {ei : ModuleInst} :
    ∀ {es : List Silmaril.Wasm.Export} {L : List ExportInst},
      List.Forall₂ (fun e x => allocExport? ei e = some x) es L → (es.map (·.name)).Nodup →
      ∀ e ∈ es, ∃ x, allocExport? ei e = some x ∧
        (L.map fun x => (x.name, x.addr)).lookup e.name = some x.addr
  | [], [], .nil, _, _, he => by cases he
  | e₀ :: es, x₀ :: L, .cons h₀ hs, hnd, e, he => by
    rw [List.map_cons] at hnd
    have hnd' := List.nodup_cons.1 hnd
    have hn₀ : x₀.name = e₀.name := (allocExport?_name h₀).1
    rcases List.mem_cons.1 he with rfl | he
    · refine ⟨x₀, h₀, ?_⟩
      rw [List.map_cons, List.lookup_cons, hn₀, beq_self_eq_true]
    · obtain ⟨x, hx, hl⟩ := lookup_allocExport hs hnd'.2 e he
      have hne : e.name ≠ x₀.name := by
        rw [hn₀]
        intro heq
        exact hnd'.1 (heq ▸ List.mem_map.2 ⟨e, he, rfl⟩)
      have hbeq : (e.name == x₀.name) = false := by simpa only [beq_eq_false_iff_ne] using hne
      refine ⟨x, hx, ?_⟩
      rw [List.map_cons, List.lookup_cons, hbeq]
      exact hl

theorem mem_fst_of_lookup {β : Type} : ∀ {l : List (String × β)} {n : String} {b : β},
    l.lookup n = some b → n ∈ l.map Prod.fst
  | [], _, _, h => by cases h
  | p :: l, n, b, h => by
    rw [List.lookup_cons] at h
    cases hb : n == p.1
    · rw [hb] at h
      exact List.mem_cons_of_mem _ (mem_fst_of_lookup h)
    · rw [List.map_cons, beq_iff_eq.1 hb]
      exact List.mem_cons_self

/-- The lookup of the name of a function export finds its address (`funcPairs` lookup). -/
theorem lookup_funcPairs_lookup : ∀ {L : List ExportInst} {n : String} {a : Nat},
    (L.map (·.name)).Nodup → (funcPairs L).lookup n = some a →
      (L.map fun x => (x.name, x.addr)).lookup n = some (.func a)
  | [], _, _, _, h => by simp [funcPairs] at h
  | x :: L, n, a, hnd, h => by
    have hnd' : x.name ∉ L.map (·.name) ∧ (L.map (·.name)).Nodup := List.nodup_cons.1 hnd
    cases hx : x.addr with
    | func a₀ =>
      rw [funcPairs_cons_func L hx, List.lookup_cons] at h
      rw [List.map_cons, List.lookup_cons]
      cases hb : n == x.name
      · rw [hb] at h
        exact lookup_funcPairs_lookup hnd'.2 h
      · rw [hb] at h
        rw [hx, Option.some.inj h]
    | _ =>
      rw [funcPairs_cons_other L (fun a e => by rw [hx] at e; cases e)] at h
      have hmem : n ∈ (funcPairs L).map Prod.fst := by
        obtain ⟨b, hb⟩ : ∃ b, (funcPairs L).lookup n = some b := ⟨a, h⟩
        exact mem_fst_of_lookup hb
      have hn : n ∈ L.map (·.name) := by
        obtain ⟨⟨n', b⟩, hp, rfl⟩ := List.mem_map.1 hmem
        exact mem_names_of_funcPairs hp
      have hne : n ≠ x.name := fun e => hnd'.1 (e ▸ hn)
      have hbeq : (n == x.name) = false := by simpa only [beq_eq_false_iff_ne] using hne
      rw [List.map_cons, List.lookup_cons, hbeq]
      exact lookup_funcPairs_lookup hnd'.2 h

theorem zip_map_fst_snd {α β : Type} : ∀ l : List (α × β), (l.map Prod.fst).zip (l.map Prod.snd) = l
  | [] => rfl
  | p :: l => by rw [List.map_cons, List.map_cons, List.zip_cons_cons, zip_map_fst_snd l]

theorem lookup_isSome_of_mem {β : Type} : ∀ {l : List (String × β)} {n : String},
    n ∈ l.map Prod.fst → ∃ b, l.lookup n = some b
  | [], _, h => by cases h
  | p :: l, n, h => by
    rw [List.lookup_cons]
    cases hb : n == p.1
    · rcases List.mem_cons.1 h with e | h
      · rw [e, beq_self_eq_true] at hb
        cases hb
      · exact lookup_isSome_of_mem h
    · exact ⟨_, rfl⟩

/-! ## The instance of a `ListComp` -/

/-- The module of a `ListComp.Inst` component instantiates in the empty store of any host type,
without imports or start function, to the instance store up to the host type. -/
theorem inst_onceL (g : H → Nat) {m : Module} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hI : ∃ mt, Silmaril.Wasm.Game.IsInstance m mt I) (himp : I.imports = []) :
    ∃ (mt : Validation.CModuleType) (cs : Store H) (f' : Frame),
      Validation.validate? m = some mt ∧ mt.imports = [] ∧
      instantiateOnce? ({} : Store H) m [] = some (cs, f', none) ∧
      Store.mapH g cs = I.store ∧ Silmaril.Wasm.Game.exportFuncAddrs f'.module = I.addrs := by
  obtain ⟨mt, hIs⟩ := hI
  have hfn : Validation.CExternType.funcs mt.imports = [] :=
    List.forall₂_nil_right_iff.1 (himp ▸ hIs.importTypes)
  have hmt : mt.imports = [] := nil_of_funcs_nil hIs.funcImports hfn
  obtain ⟨f, hf, haddr⟩ := hIs.instantiated
  have hf₀ : instantiateOnce? (Silmaril.Wasm.Game.importStore []) m [] =
      some (I.store, f, none) := by
    rw [← hf, hmt]
    rfl
  have hf' : mapS g (instantiateOnce? ({} : Store H) m []) = some (I.store, f, none) := by
    rw [← instantiateOnce?_importStore g, hf₀]
  obtain ⟨cs, ho, hs⟩ := mapS_eq_some hf'
  exact ⟨mt, cs, f, hIs.valid, hmt, ho, hs, haddr⟩

/-- **The core export named `memName` is memory address `memIdx`.** -/
theorem lookup_memExport {c : ListComp} {I : Silmaril.Wasm.Game.ScalarInstance}
    {mt : Validation.CModuleType} {f' : Frame} {cs : Store H} (hi : c.Inst I)
    (hv : Validation.validate? c.mod = some mt)
    (ho : instantiateOnce? ({} : Store H) c.mod [] = some (cs, f', none)) :
    (f'.module.exports.map fun x => (x.name, x.addr)).lookup c.memName = some (.mem c.memIdx) := by
  obtain ⟨ei, hX, hm⟩ := instantiateOnce?_memExports ho
  have hnd : (c.mod.exports.map (·.name)).Nodup := by
    obtain ⟨⟩ := Validation.validate?_sound hv
    assumption
  obtain ⟨e, he, hname, i, hidx, hi'⟩ := hi.memExport
  obtain ⟨x, hx, hl⟩ := lookup_allocExport hX hnd e he
  rw [← hname, hl]
  unfold allocExport? at hx
  rw [hidx, hm] at hx
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hx
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 hb
  have ha0 : a = c.memIdx := by
    have h0 : (List.range' 0 c.mod.memories.length)[c.memIdx]? = some a := hi' ▸ ha
    by_cases hlt : c.memIdx < c.mod.memories.length
    · rw [List.getElem?_range' hlt] at h0
      simpa using h0.symm
    · rw [List.getElem?_eq_none (by simpa using hlt)] at h0
      cases h0
  rw [ha0]

/-- **The core export named by a function export name `n` is the function `c.coreAddr I n`.** -/
theorem lookup_funcName {c : ListComp} {I : Silmaril.Wasm.Game.ScalarInstance}
    {mt : Validation.CModuleType} {f' : Frame} {cs : Store H}
    (hv : Validation.validate? c.mod = some mt)
    (ho : instantiateOnce? ({} : Store H) c.mod [] = some (cs, f', none))
    (ha : Silmaril.Wasm.Game.exportFuncAddrs f'.module = I.addrs) {n : String}
    (hn : n ∈ funcExportNames c.mod) :
    (f'.module.exports.map fun x => (x.name, x.addr)).lookup n =
      some (.func (c.coreAddr I n)) := by
  obtain ⟨ei, hX⟩ := instantiateOnce?_exports ho
  obtain ⟨hnames, hfn⟩ := allocExports_names hX
  have hnd : (f'.module.exports.map (·.name)).Nodup := by
    rw [hnames]
    obtain ⟨⟩ := Validation.validate?_sound hv
    assumption
  have hfst : (funcPairs f'.module.exports).map Prod.fst = funcExportNames c.mod := hfn
  have hsnd : (funcPairs f'.module.exports).map Prod.snd = I.addrs := by
    rw [← ha, funcPairs_snd]
    rfl
  have hz : (funcExportNames c.mod).zip I.addrs = funcPairs f'.module.exports := by
    rw [← hfst, ← hsnd, zip_map_fst_snd]
  obtain ⟨a, hla⟩ := lookup_isSome_of_mem (l := funcPairs f'.module.exports) (hfst ▸ hn)
  have hca : c.coreAddr I n = a := by
    unfold ListComp.coreAddr
    rw [hz, hla]
    rfl
  rw [hca]
  exact lookup_funcPairs_lookup hnd hla

/-! ## The core facts over `core3P P` -/

section Engine

open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Instantiate

variable {Pf : Profile}

/-- The core facts of `ListComp.Inst`, over `core3P Pf`. -/
structure CoreFactsL (c : ListComp) (I : Silmaril.Wasm.Game.ScalarInstance)
    (cs : (core3P Pf).Store (CanonHost (core3P Pf))) (ci : (core3P Pf).Inst) : Prop where
  store : Store.mapH (fun _ => 0) cs = I.store
  imports : (core3P Pf).importTypes c.mod = []
  prepare : (core3P Pf).prepare? ((core3P Pf).empty _) c.mod [] = some (cs, ci, none)
  mem : lookupExport? ((core3P Pf).exports ci) c.memName = some (.mem c.memIdx)
  func : ∀ n ∈ funcExportNames c.mod,
    lookupExport? ((core3P Pf).exports ci) n = some (.func (c.coreAddr I n))

/-- **The core facts hold** for a `ListComp.Inst` component. -/
theorem coreFactsL {c : ListComp} {I : Silmaril.Wasm.Game.ScalarInstance} (hi : c.Inst I) :
    ∃ cs ci, CoreFactsL (Pf := Pf) c I cs ci := by
  obtain ⟨mt, cs, f', hv, hmt, ho, hs, ha⟩ := inst_onceL
    (H := CanonHost (core3P Pf)) (fun _ => 0) hi.inst hi.noImports
  refine ⟨cs, f'.module, ⟨hs, importTypes_core3P Pf hv hmt, prepare_core3P Pf hv hmt ho, ?_,
    fun n hn => ?_⟩⟩
  · rw [exports_core3P]
    exact lookup_memExport hi hv ho
  · rw [exports_core3P]
    exact lookup_funcName hv ho ha hn

end Engine

end Silmaril.Proofs.Wasm.Component.Reference.ListLift
