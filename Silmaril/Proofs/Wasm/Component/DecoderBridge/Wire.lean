module

public import Silmaril.Wasm.Component.DecoderBridge.Wire.Defs
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Lower
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.ToRef
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Bridge

/-!
# The two readings of a component binary: the wiring correspondence (proofs)

`relW_of_lower`: if `Binary.lower a = .ok c`, `Conformance.toRef a = .ok r` and `InFrag r`, then
`RelW c r`. The proof runs the lowering state (`Binary.Lower.St`) and the symbolic reading
(`DecoderBridge.RSt`) side by side, section by section and item by item, under the invariant
`Corr` (the modules decode to the same modules with the same interface, the types, functions,
core functions and exports are equal, core instances agree on bases and exports, and the
nodes are related by `NodeW`):

* items: `corr_import`, `corr_instantiate` (the `for` loop over the module's imports is
  `forIn_push`; argument lookup `find?` is `List.lookup`, `find?_lookup`), `corr_inline`,
  `corr_alias`, `corr_canon`, `corr_export`, `corr_type` (`refFuncTy_funcTy`: a function type of
  the fragment is lowered to the same IR function type), `corr_coreModule` (`coreMod_eq`:
  `Binary.Lower.coreMod` is the core decoder followed by `coreIface`);
* sections: `corr_section`, `corr_sections`; sections outside the fragment produce definitions
  the reading rejects (`foldlM_rejected`);
* the import pass `Binary.Lower.importsPass`, a separate loop over the sections, computes the
  reading's imports (`importsPass_ok`, invariant `PInv`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Binary Silmaril.Wasm.Component.Binary.Lower
open Silmaril.Wasm.Component.Conformance Silmaril.Wasm.Component.DecoderBridge

theorem coreMod_eq (bs : ByteArray) : coreMod bs = match Silmaril.Wasm.Binary.Core.decode? bs with
    | none => throw "embedded core module rejected by silmaril's core decoder (outside its fragment)"
    | some m => (fun t => (⟨bs, t.1, t.2.1, t.2.2⟩ : CoreMod)) <$> coreIface m := by
  unfold coreMod coreIface
  cases Silmaril.Wasm.Binary.Core.decode? bs with
  | none => rfl
  | some m =>
    simp only [map_bind, map_pure]
    rfl

/-- A core module of the lowering state and of the symbolic reading. -/
def ModW (cm : CoreMod) (m : Silmaril.Wasm.Module) : Prop :=
  Silmaril.Wasm.Binary.Core.decode? cm.bytes = some m ∧
    coreIface m = .ok (cm.importNames, CoreModule.imports cm, CoreModule.exports cm)

theorem coreMod_modW {bs : ByteArray} {cm : CoreMod} {m : Silmaril.Wasm.Module}
    (h : coreMod bs = .ok cm) (hd : Silmaril.Wasm.Binary.Core.decode? bs = some m) :
    ModW cm m := by
  rw [coreMod_eq, hd] at h
  simp only at h
  cases hi : coreIface m with
  | error e => rw [hi] at h; cases h
  | ok t =>
    rw [hi] at h; cases h
    exact ⟨hd, by rw [hi]; rfl⟩

/-- A core instance of the lowering state and of the symbolic reading. -/
def CIW : CoreInst → RCI → Prop
  | .node b cm, .node b' e => b = b' ∧ CoreModule.exports cm = e
  | .inline es, .inline es' => es = es'
  | _, _ => False

/-- **The correspondence between the lowering state and the symbolic reading.** -/
structure Corr (s : St) (R : RSt) : Prop where
  mods : List.Forall₂ ModW s.modules.toList R.mods
  types : s.types.toList = R.types.map TypeEntry.func
  funcs : s.funcs.toList = R.funcs
  coreFuncs : s.coreFuncs.toList = R.coreFuncs
  coreInsts : List.Forall₂ CIW s.coreInsts.toList R.coreInsts
  next : s.nextImport = R.imports.length
  env : s.env = R.env
  nodes : List.Forall₂ NodeW s.nodes.toList R.nodes
  exports : s.exports.toList = R.exports

theorem types_get {s : St} {R : RSt} (h : Corr s R) {t : Nat} {ft : FuncTy}
    (ht : R.types[t]? = some ft) : s.types[t]? = some (.func ft) := by
  have := congrArg (·[t]?) h.types
  simp only [Array.getElem?_toList, List.getElem?_map, ht, Option.map_some] at this
  exact this

theorem list_get {α} {xs : Array α} {ys : List α} (h : xs.toList = ys) {i : Nat} :
    xs[i]? = ys[i]? := by
  rw [← h, Array.getElem?_toList]

/-- Unfold a run of the lowering monad. -/
macro "lsimp" " at " h:ident : tactic => `(tactic| simp [StateT.run, bind, StateT.bind, get,
  getThe, MonadStateOf.get, StateT.get, set, StateT.set, modify, modifyGet, MonadStateOf.modifyGet,
  StateT.modifyGet, pure, Except.pure, Except.bind, StateT.pure, throw, throwThe,
  MonadExceptOf.throw, StateT.lift, liftM, monadLift, MonadLift.monadLift] at $h:ident)

theorem corr_import {s s' : St} {R R' : RSt} {i : Import} (hc : Corr s R)
    (h : (import_ i).run s = .ok ((), s'))
    (hr : refStep R (.import_ (ToRef.externName i.name) (ToRef.externDesc i.desc)) = some R') :
    Corr s' R' := by
  rcases i with ⟨n, d⟩
  cases d with
  | func t =>
    simp only [ToRef.externDesc, refStep, bind, Option.bind] at hr
    split at hr
    · cases hr
    · rename_i ft hft
      cases hr
      have hs := types_get hc hft
      simp only [import_, lookupFuncTy, addImport] at h
      lsimp at h
      simp only [hs] at h
      cases h
      exact { hc with
        funcs := by simp [hc.funcs, hc.next]
        next := by simp [hc.next] }
  | _ => simp [ToRef.externDesc, refStep] at hr


/-- A `for` loop of the lowering monad that keeps the state and pushes one value per item. -/
theorem forIn_push {α β : Type} {F : α → Array β → M (ForInStep (Array β))} {P : α → β → Prop}
    {Q : α → Prop}
    (hF : ∀ x acc st r, Q x → F x acc st = .ok r → r.2 = st ∧ ∃ v, r.1 = .yield (acc.push v) ∧ P x v) :
    ∀ (xs : List α) (acc : Array β) (st : St) (W : Array β) (st' : St), (∀ x ∈ xs, Q x) →
      forIn xs acc F st = .ok (W, st') →
      st' = st ∧ ∃ ws, W.toList = acc.toList ++ ws ∧ List.Forall₂ P xs ws
  | [], acc, st, W, st', _, h => by
    simp only [List.forIn_nil] at h
    cases h; exact ⟨rfl, [], by simp, .nil⟩
  | x :: xs, acc, st, W, st', hq, h => by
    simp only [List.forIn_cons] at h
    lsimp at h
    split at h
    · cases h
    · rename_i r hr
      obtain ⟨h2, v, h1, hp⟩ := hF x acc st r (hq x (by simp)) hr
      rw [h1] at h
      simp only at h
      obtain ⟨hs, ws, hw, hws⟩ :=
        forIn_push hF xs (acc.push v) r.2 W st' (fun y hy => hq y (by simp [hy])) h
      refine ⟨hs.trans h2, v :: ws, by simp [hw], .cons hp hws⟩

theorem find?_lookup {β : Type} (k : String) : ∀ (l : List (String × β)),
    (l.find? (·.1 == k)).map (·.2) = l.lookup k
  | [] => rfl
  | (a, b) :: l => by
    by_cases h : a = k
    · subst h; simp [List.lookup]
    · have h' : (k == a) = false := by simp; exact fun e => h e.symm
      simp [List.lookup, h', h, find?_lookup k l]

theorem coreExportImpl_rci {inst : CoreInst} {ci : RCI} (hw : CIW inst ci) {n : String}
    {im im' : Impl} (h : coreExportImpl inst n = .ok im) (h' : rciImpl ci n = some im') :
    im = im' := by
  cases inst <;> cases ci <;> simp only [CIW] at hw
  · obtain ⟨rfl, rfl⟩ := hw
    simp only [coreExportImpl] at h
    simp only [rciImpl] at h'
    split at h
    · rename_i j hj
      cases h
      rw [hj] at h'
      cases h'; rfl
    · cases h
  · subst hw
    simp only [coreExportImpl] at h
    simp only [rciImpl, ← find?_lookup] at h'
    split at h
    · rename_i p hp
      cases h
      rw [hp] at h'
      cases h'; rfl
    · cases h

theorem corr_coreModule {s s' : St} {R R' : RSt} {bs : ByteArray} {m : Silmaril.Wasm.Module}
    (hc : Corr s R) (h : (section_ (.coreModule bs)).run s = .ok ((), s'))
    (hm : ToRef.coreModule bs = .ok m) (hr : refStep R (.coreModule m) = some R') :
    Corr s' R' := by
  simp only [refStep, Option.some.injEq] at hr
  subst hr
  have hd : Silmaril.Wasm.Binary.Core.decode? bs = some m := by
    unfold ToRef.coreModule at hm
    split at hm
    · cases hm; assumption
    · cases hm
  obtain ⟨cm, s1, h1, h⟩ := run_bind_ok h
  cases hb : coreMod bs with
  | error e =>
    simp [hb, liftM, monadLift, MonadLift.monadLift, StateT.lift, StateT.run, bind, Except.bind] at h1
  | ok cm' =>
    simp [hb, liftM, monadLift, MonadLift.monadLift, StateT.lift, StateT.run, bind, Except.bind,
      pure, Except.pure] at h1
    obtain ⟨rfl, rfl⟩ := h1
    lsimp at h
    cases h
    exact { hc with mods := by simpa using List.rel_append hc.mods (.cons (coreMod_modW hb hd) .nil) }

theorem forall₂_mapM_eq {α β : Type} {P : α → β → Prop} {g : α → Option β}
    (hP : ∀ x v w, P x v → g x = some w → v = w) :
    ∀ {xs : List α} {vs ws : List β}, List.Forall₂ P xs vs → xs.mapM g = some ws → vs = ws
  | [], _, _, .nil, h => by simp at h; exact h.symm
  | x :: xs, v :: vs, ws, .cons hp hr, h => by
    rw [List.mapM_cons] at h
    cases hw : g x with
    | none => simp [hw] at h
    | some w =>
      cases hws : xs.mapM g with
      | none => simp [hw, hws] at h
      | some ws' =>
        simp [hw, hws] at h; subst h
        rw [hP x v w hp hw, forall₂_mapM_eq hP hr hws]

theorem forall₂_getElem?' {α β : Type} {R : α → β → Prop} {l1 : List α} {l2 : List β}
    (h : List.Forall₂ R l1 l2) {i : Nat} {y : β} (hy : l2[i]? = some y) :
    ∃ x, l1[i]? = some x ∧ R x y := by
  induction h generalizing i with
  | nil => simp at hy
  | cons hr _ ih =>
    cases i with
    | zero => simp at hy; subst hy; exact ⟨_, rfl, hr⟩
    | succ i => exact ih (by simpa using hy)

theorem corr_instantiate {s s' : St} {R R' : RSt} {mi : Nat} {args : List (String × Nat)}
    (hc : Corr s R) (h : (coreInstance (.instantiate mi args)).run s = .ok ((), s'))
    (hr : refStep R (.coreInstance (.instantiate mi args)) = some R') : Corr s' R' := by
  simp only [refStep, bind, Option.bind] at hr
  split at hr
  · cases hr
  rename_i m hm
  obtain ⟨cm, hcm, hmw⟩ := forall₂_getElem?' hc.mods hm
  have hi := hmw.2
  simp only [hi, Except.toOption] at hr
  split at hr
  · cases hr
  rename_i w hw
  simp only [Option.some.injEq] at hr
  subst hr
  simp only [coreInstance] at h
  lsimp at h
  have hg : get? s.modules mi "core module" s = .ok (cm, s) := by
    simp [get?, Array.getElem?_toList ▸ hcm, pure, StateT.pure, Except.pure]
  rw [hg] at h
  simp only at h
  split at h
  · cases h
  rename_i W hW
  cases h
  obtain ⟨-, ws, hws, hP⟩ := forIn_push (Q := fun _ => True)
    (P := fun (x : String × String) v => ∃ j inst, (args.find? (·.1 == x.1)).map (·.2) = some j ∧
      s.coreInsts[j]? = some inst ∧ coreExportImpl inst x.2 = .ok v)
    (fun x acc st r _ hr => by
      cases hj : List.find? (fun x_1 => x_1.1 == x.1) args with
      | none => simp only [hj] at hr; lsimp at hr
      | some p =>
        obtain ⟨_, j⟩ := p
        simp only [hj] at hr
        lsimp at hr
        simp only [get?] at hr
        cases hinst : s.coreInsts[j]? with
        | none => simp only [hinst] at hr; lsimp at hr
        | some inst =>
          simp only [hinst] at hr
          lsimp at hr
          cases he : coreExportImpl inst x.2 with
          | error e => simp [he] at hr
          | ok v =>
            simp [he] at hr
            subst hr
            exact ⟨rfl, v, rfl, j, inst, by simp, hinst, he⟩)
    cm.importNames #[] s W.1 W.2 (fun _ _ => trivial) hW
  have hwe : ws = w := by
    refine forall₂_mapM_eq (fun x v w hp hg => ?_) hP hw
    obtain ⟨j, inst, hj, hinst, he⟩ := hp
    rw [find?_lookup] at hj
    simp only [hj] at hg
    split at hg
    · cases hg
    rename_i ci hci
    obtain ⟨inst', hinst', hcw⟩ := forall₂_getElem?' hc.coreInsts hci
    rw [Array.getElem?_toList] at hinst'
    rw [hinst] at hinst'
    cases hinst'
    exact coreExportImpl_rci hcw he hg
  subst hwe
  simp at hws
  exact { hc with
    coreInsts := by simpa using List.rel_append hc.coreInsts (.cons (by simp [CIW, hc.env]) .nil)
    env := by simp [hc.env]
    nodes := by
      simpa [hws] using List.rel_append hc.nodes (.cons (show NodeW (.core cm ws) (m, ws) from ⟨cm, rfl, hmw.1, hmw.2⟩) .nil) }

theorem mapM_some_mem {α β : Type} {g : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM g = some ys → ∀ x ∈ xs, ∃ y, g x = some y
  | [], _, _, _, hx => by simp at hx
  | x :: xs, ys, h, y, hy => by
    rw [List.mapM_cons] at h
    cases hw : g x with
    | none => simp [hw] at h
    | some w =>
      cases hws : xs.mapM g with
      | none => simp [hw, hws] at h
      | some ws' =>
        rcases List.mem_cons.1 hy with rfl | hy
        · exact ⟨w, hw⟩
        · exact mapM_some_mem hws y hy

theorem coreSort_func {c : Binary.CoreSort} (h : ToRef.coreSort c = .func) : c = .func := by
  cases c <;> first | rfl | cases h

theorem corr_inline {s s' : St} {R R' : RSt} {es : List (String × Binary.CoreSortIdx)}
    (hc : Corr s R) (h : (coreInstance (.exports es)).run s = .ok ((), s'))
    (hr : refStep R (.coreInstance (ToRef.coreInstanceExpr (.exports es))) = some R') :
    Corr s' R' := by
  simp only [ToRef.coreInstanceExpr, refStep, bind, Option.bind] at hr
  split at hr
  · cases hr
  rename_i es' hes
  simp only [Option.some.injEq] at hr
  subst hr
  rw [List.mapM_map] at hes
  have hq : ∀ x ∈ es, x.2.sort = .func := by
    intro x hx
    obtain ⟨y, hy⟩ := mapM_some_mem hes x hx
    simp only [Function.comp, ToRef.coreSortIdx] at hy
    by_cases hs : ToRef.coreSort x.2.sort = .func
    · exact coreSort_func hs
    · simp [hs] at hy
  simp only [coreInstance] at h
  lsimp at h
  split at h
  · cases h
  rename_i W hW
  cases h
  obtain ⟨-, ws, hws, hP⟩ := forIn_push (Q := fun (x : String × Binary.CoreSortIdx) => x.2.sort = .func)
    (P := fun (x : String × Binary.CoreSortIdx) v => v.1 = x.1 ∧ s.coreFuncs[x.2.idx]? = some v.2)
    (fun x acc st r hq hr => by
      obtain ⟨n, ⟨srt, i⟩⟩ := x
      simp only at hq
      subst hq
      simp only at hr
      lsimp at hr
      simp only [get?] at hr
      cases hi : s.coreFuncs[i]? with
      | none => simp only [hi] at hr; lsimp at hr
      | some v =>
        simp only [hi] at hr
        lsimp at hr
        subst hr
        exact ⟨rfl, (n, v), rfl, rfl, rfl⟩)
    es #[] s W.1 W.2 hq hW
  have hwe : ws = es' := by
    refine forall₂_mapM_eq (fun x v w hp hg => ?_) hP hes
    obtain ⟨h1, h2⟩ := hp
    simp only [Function.comp, ToRef.coreSortIdx] at hg
    by_cases hs : ToRef.coreSort x.2.sort = .func
    · rw [list_get hc.coreFuncs] at h2
      simp only [hs, ite_true, h2, Option.map_some, Option.some.injEq] at hg
      subst hg
      rw [← h1]
    · simp [hs] at hg
  subst hwe
  simp at hws
  exact { hc with
    coreInsts := by simpa [hws] using List.rel_append hc.coreInsts (.cons (by simp [CIW]) .nil) }

theorem corr_alias {s s' : St} {R R' : RSt} {a : Binary.Alias} {a' : Syntax.Alias}
    (hc : Corr s R) (h : (alias_ a).run s = .ok ((), s')) (ha : ToRef.aliasDef a = .ok a')
    (hr : refStep R (.alias a') = some R') : Corr s' R' := by
  rcases a with ⟨srt, tgt⟩
  cases tgt with
  | «export» i n => simp [ToRef.aliasDef] at ha; subst ha; simp [refStep] at hr
  | outer c i => simp [ToRef.aliasDef] at ha; subst ha; simp [refStep] at hr
  | coreExport i n =>
    cases srt with
    | core cs =>
      simp only [ToRef.aliasDef, Except.ok.injEq] at ha
      subst ha
      cases hcs : ToRef.coreSort cs with
      | func =>
        have := coreSort_func hcs
        subst this
        rw [hcs] at hr
        simp only [refStep, bind, Option.bind] at hr
        cases hci : R.coreInsts[i]? with
        | none => simp [hci] at hr
        | some ci =>
          cases him : rciImpl ci n with
          | none => simp [hci, him] at hr
          | some im =>
            simp only [hci, him, Option.some.injEq] at hr
            subst hr
            obtain ⟨inst, hinst, hw⟩ := forall₂_getElem?' hc.coreInsts hci
            rw [Array.getElem?_toList] at hinst
            simp only [alias_] at h
            lsimp at h
            simp only [get?, hinst] at h
            lsimp at h
            cases he : coreExportImpl inst n with
            | error e => simp [he] at h
            | ok im' =>
              simp [he] at h
              subst h
              have := coreExportImpl_rci hw he him
              subst this
              exact { hc with coreFuncs := by simp [hc.coreFuncs] }
      | _ => rw [hcs] at hr; simp [refStep] at hr
    | _ => simp [ToRef.aliasDef] at ha

theorem corr_canon {s s' : St} {R R' : RSt} {c : Binary.Canon}
    (hc : Corr s R) (h : (canon c).run s = .ok ((), s'))
    (hr : refStep R (.canon (ToRef.canon c)) = some R') : Corr s' R' := by
  cases c with
  | lift f opts t =>
    cases opts with
    | cons o os => simp [ToRef.canon, refStep] at hr
    | nil =>
      simp only [ToRef.canon, List.map_nil, refStep, bind, Option.bind] at hr
      cases hf : R.coreFuncs[f]? with
      | none => simp [hf] at hr
      | some im =>
        cases ht : R.types[t]? with
        | none => simp [hf, ht] at hr
        | some ft =>
          simp only [hf, ht, Option.some.injEq] at hr
          subst hr
          have hf' : s.coreFuncs[f]? = some im := by rw [list_get hc.coreFuncs]; exact hf
          have ht' := types_get hc ht
          simp only [canon, lookupFuncTy] at h
          lsimp at h
          simp only [get?, hf'] at h
          lsimp at h
          simp only [ht'] at h
          lsimp at h
          subst h
          exact { hc with funcs := by simp [hc.funcs] }
  | lower f opts =>
    cases opts with
    | cons o os => simp [ToRef.canon, refStep] at hr
    | nil =>
      simp only [ToRef.canon, List.map_nil, refStep, bind, Option.bind] at hr
      cases hf : R.funcs[f]? with
      | none => simp [hf] at hr
      | some p =>
        obtain ⟨im, ft⟩ := p
        by_cases hch : im.chain = []
        · simp only [hf, hch, ne_eq, not_true_eq_false, ite_false, Option.some.injEq] at hr
          subst hr
          have hf' : s.funcs[f]? = some (im, ft) := by rw [list_get hc.funcs]; exact hf
          simp only [canon] at h
          lsimp at h
          simp only [get?, hf'] at h
          lsimp at h
          subst h
          exact { hc with coreFuncs := by simp [hc.coreFuncs, hch] }
        · simp [hf, hch] at hr
  | resourceNew t => simp [ToRef.canon, refStep] at hr
  | resourceDrop t => simp [ToRef.canon, refStep] at hr
  | resourceRep t => simp [ToRef.canon, refStep] at hr

theorem sort_func {c : Binary.ItemSort} (h : ToRef.sort c = .func) : c = .func := by
  cases c <;> first | rfl | cases h

theorem corr_export {s s' : St} {R R' : RSt} {e : Binary.Export}
    (hc : Corr s R) (h : (export_ e).run s = .ok ((), s'))
    (hr : refStep R (.export_ (ToRef.externName e.name) (ToRef.sortIdx e.item)
      (e.desc.map ToRef.externDesc)) = some R') : Corr s' R' := by
  rcases e with ⟨n, ⟨srt, i⟩, d⟩
  cases d with
  | some d => simp [refStep] at hr
  | none =>
    simp only [ToRef.sortIdx, Option.map_none] at hr
    cases hs : ToRef.sort srt with
    | func =>
      have := sort_func hs
      subst this
      rw [hs] at hr
      simp only [refStep, bind, Option.bind] at hr
      cases hf : R.funcs[i]? with
      | none => simp [hf] at hr
      | some p =>
        obtain ⟨im, ft⟩ := p
        simp only [hf, Option.some.injEq] at hr
        subst hr
        have hf' : s.funcs[i]? = some (im, ft) := by rw [list_get hc.funcs]; exact hf
        simp only [export_] at h
        lsimp at h
        simp only [get?, hf'] at h
        lsimp at h
        subst h
        exact { hc with
          funcs := by simp [hc.funcs]
          exports := by simp [hc.exports, ToRef.externName] }
    | _ => rw [hs] at hr; simp [refStep] at hr

theorem refPrim_prim {p : Binary.PrimValType} {v : ValTy} (h : refPrim (ToRef.prim p) = some v) :
    primTy p = .ok v := by
  cases p <;> simp [ToRef.prim, refPrim] at h <;> subst h <;> rfl

theorem refVT_valTy (types : Array TypeEntry) {t : Binary.ValType} {v : ValTy}
    (h : refVT (ToRef.valType t) = some v) : valTy types t = .ok v := by
  cases t with
  | prim p => exact refPrim_prim h
  | idx i => simp [ToRef.valType, refVT] at h

theorem mapM_opt_ex {α β : Type} {g : α → Option β} {f : α → Except String β}
    (hgf : ∀ x y, g x = some y → f x = .ok y) :
    ∀ {xs : List α} {ys : List β}, xs.mapM g = some ys → xs.mapM f = .ok ys
  | [], ys, h => by simp at h; subst h; rfl
  | x :: xs, ys, h => by
    rw [List.mapM_cons] at h
    cases hw : g x with
    | none => simp [hw] at h
    | some w =>
      cases hws : xs.mapM g with
      | none => simp [hw, hws] at h
      | some ws' =>
        simp [hw, hws] at h; subst h
        rw [List.mapM_cons, hgf x w hw, mapM_opt_ex hgf hws]; rfl

theorem refFuncTy_funcTy (types : Array TypeEntry) {f : Binary.FuncType} {ft : FuncTy}
    (h : refFuncTy (ToRef.funcType f) = some ft) : funcTy types f = .ok ft := by
  rcases f with ⟨ps, res, asy⟩
  simp only [refFuncTy, ToRef.funcType] at h
  cases asy with
  | true => simp at h
  | false =>
    simp only [Bool.false_eq_true, ite_false, bind, Option.bind, List.mapM_map] at h
    cases hps : List.mapM (fun p => refVT (ToRef.valType p.2)) ps with
    | none =>
      rw [show ((fun p => refVT p.2) ∘ fun p : String × Binary.ValType => (p.1, ToRef.valType p.2)) =
        (fun p => refVT (ToRef.valType p.2)) from rfl, hps] at h
      simp at h
    | some vs =>
      rw [show ((fun p => refVT p.2) ∘ fun p : String × Binary.ValType => (p.1, ToRef.valType p.2)) =
        (fun p => refVT (ToRef.valType p.2)) from rfl, hps] at h
      have hps' : ps.mapM (fun p => valTy types p.2) = .ok vs :=
        mapM_opt_ex (fun x y hy => refVT_valTy types hy) hps
      simp only [funcTy, hps', bind, Except.bind, Bool.false_eq_true, ite_false]
      cases res with
      | none =>
        simp only [Option.map_none] at h
        simp only [pure, Except.pure]
        split at h
        · simp at h
        · split at h
          · simp at h
          · simp at h; subst h
            simp [*]
      | some t =>
        simp only [Option.map_some] at h
        cases ht : refVT (ToRef.valType t) with
        | none => simp [ht] at h
        | some v =>
          simp only [ht, Option.map_some] at h
          simp only [refVT_valTy types ht, pure, Except.pure]
          split at h
          · simp at h
          · split at h
            · simp at h
            · simp at h; subst h
              simp [*]

theorem defType_func {t : Binary.DefType} {f : Syntax.FuncType} (h : ToRef.defType t = .ok (.func f)) :
    ∃ g, t = .func g ∧ f = ToRef.funcType g := by
  cases t with
  | val d => simp [ToRef.defType] at h
  | func g => simp [ToRef.defType] at h; exact ⟨g, rfl, h.symm⟩
  | component ds =>
    simp only [ToRef.defType] at h
    cases hd : ToRef.componentDecls ds <;> simp [hd, Functor.map, Except.map] at h
  | «instance» ds =>
    simp only [ToRef.defType] at h
    cases hd : ToRef.instanceDecls ds <;> simp [hd, Functor.map, Except.map] at h
  | resource rep dtor =>
    simp only [ToRef.defType] at h
    cases hr : ToRef.addrType rep <;> simp [hr, bind, Except.bind, pure, Except.pure] at h

theorem corr_type {s s' : St} {R R' : RSt} {t : Binary.DefType} {d : Syntax.DefType}
    (hc : Corr s R) (h : (modify fun s : St => { s with types := s.types.push (typeEntry s.types t) } : M PUnit).run s = .ok ((), s'))
    (ht : ToRef.defType t = .ok d) (hr : refStep R (.type d) = some R') : Corr s' R' := by
  cases d with
  | func f =>
    obtain ⟨g, rfl, rfl⟩ := defType_func ht
    simp only [refStep, bind, Option.bind] at hr
    cases hf : refFuncTy (ToRef.funcType g) with
    | none => simp [hf] at hr
    | some ft =>
      simp only [hf, Option.some.injEq] at hr
      subst hr
      lsimp at h
      subst h
      exact { hc with types := by simp [hc.types, typeEntry, refFuncTy_funcTy s.types hf] }
  | _ => simp [refStep] at hr

/-! ## Sections -/

theorem forM_corr {α : Type} {f : α → M PUnit} {D : α → RDef → Prop}
    (hstep : ∀ x d s s' R R', D x d → Corr s R → (f x).run s = .ok ((), s') →
      refStep R d = some R' → Corr s' R') :
    ∀ {xs : List α} {ds : List RDef} {s s' : St} {R R' : RSt}, List.Forall₂ D xs ds → Corr s R →
      (xs.forM f).run s = .ok ((), s') → ds.foldlM refStep R = some R' → Corr s' R'
  | [], [], s, s', R, R', .nil, hc, h, hr => by
    cases h; simp at hr; subst hr; exact hc
  | x :: xs, d :: ds, s, s', R, R', .cons hd hds, hc, h, hr => by
    obtain ⟨s1, h1, h2⟩ := forM_run_cons h
    simp only [List.foldlM_cons, bind, Option.bind] at hr
    cases hR : refStep R d with
    | none => simp [hR] at hr
    | some R1 =>
      simp only [hR] at hr
      exact forM_corr hstep hds (hstep x d s s1 R R1 hd hc h1 hR) h2 hr

theorem mapM_forall₂ {α β ε : Type} {f : α → Except ε β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys → List.Forall₂ (fun x y => f x = .ok y) xs ys
  | [], ys, h => by simp [List.mapM_nil, pure, Except.pure] at h; subst h; exact .nil
  | x :: xs, ys, h => by
    simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · rename_i y hy
      split at h
      · cases h
      · rename_i ys' hys
        cases h
        exact .cons hy (mapM_forall₂ hys)

theorem forall₂_map_self {α β : Type} (g : α → β) :
    ∀ xs : List α, List.Forall₂ (fun x d => d = g x) xs (xs.map g)
  | [] => .nil
  | _ :: xs => .cons rfl (forall₂_map_self g xs)

/-- Definitions outside the fragment: the reading of a list of them succeeds only if it is
empty. -/
theorem foldlM_rejected {ds : List RDef} {R R' : RSt} (hd : ∀ d ∈ ds, ∀ R, refStep R d = none)
    (h : ds.foldlM refStep R = some R') : ds = [] ∧ R' = R := by
  cases ds with
  | nil => simp at h; exact ⟨rfl, h.symm⟩
  | cons d ds =>
    simp only [List.foldlM_cons, bind, Option.bind, hd d (by simp) R] at h
    cases h

theorem forM_nil_run {α : Type} {f : α → M PUnit} {s s' : St}
    (h : (([] : List α).forM f).run s = .ok ((), s')) : s' = s := by
  cases h; rfl

theorem corr_section {sec : Binary.Section} {ds : List RDef} {s s' : St} {R R' : RSt}
    (hc : Corr s R) (h : (section_ sec).run s = .ok ((), s')) (ht : ToRef.section_ sec = .ok ds)
    (hr : ds.foldlM refStep R = some R') : Corr s' R' := by
  cases sec with
  | custom n d =>
    simp only [ToRef.section_] at ht; cases ht
    simp at hr; subst hr; cases h; exact hc
  | coreModule bs =>
    simp only [ToRef.section_, bind, Except.bind, pure, Except.pure] at ht
    split at ht
    · cases ht
    · rename_i m hm
      cases ht
      simp only [List.foldlM_cons, List.foldlM_nil, bind, Option.bind] at hr
      cases hR : refStep R (.coreModule m) with
      | none => simp [hR] at hr
      | some R1 =>
        simp only [hR] at hr
        cases hr
        exact corr_coreModule hc h hm hR
  | coreInstances xs =>
    simp only [ToRef.section_, Except.ok.injEq] at ht
    subst ht
    refine forM_corr (D := fun x d => d = .coreInstance (ToRef.coreInstanceExpr x))
      (fun x d s s' R R' hd hc h hr => ?_) (forall₂_map_self _ xs) hc h hr
    subst hd
    cases x with
    | instantiate mi args => exact corr_instantiate hc h hr
    | exports es => exact corr_inline hc h hr
  | coreTypes xs =>
    simp only [ToRef.section_] at ht
    obtain ⟨rfl, rfl⟩ := foldlM_rejected (fun d hd R => by
      obtain ⟨x, -, hx⟩ := mapM_ok ht d hd
      cases hy : ToRef.coreType x <;> simp [hy, Functor.map, Except.map] at hx
      subst hx; rfl) hr
    cases h; exact hc
  | component c => cases h
  | instances xs =>
    simp only [ToRef.section_, Except.ok.injEq] at ht
    subst ht
    obtain ⟨hn, rfl⟩ := foldlM_rejected (fun d hd R => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hd; rfl) hr
    simp only [List.map_eq_nil_iff] at hn
    subst hn
    have := forM_nil_run (f := instance_) h
    subst this; exact hc
  | aliases xs =>
    simp only [ToRef.section_] at ht
    refine forM_corr (D := fun x d => ∃ a', ToRef.aliasDef x = .ok a' ∧ d = .alias a')
      (fun x d s s' R R' hd hc h hr => ?_) ((mapM_forall₂ ht).imp fun x d hd => ?_) hc h hr
    · obtain ⟨a', ha, rfl⟩ := hd
      exact corr_alias hc h ha hr
    · cases ha : ToRef.aliasDef x <;> simp [ha, Functor.map, Except.map] at hd
      exact ⟨_, rfl, hd.symm⟩
  | types xs =>
    simp only [ToRef.section_] at ht
    simp only [section_] at h
    refine forM_corr (D := fun x d => ∃ t', ToRef.defType x = .ok t' ∧ d = .type t')
      (fun x d s s' R R' hd hc h hr => ?_) ((mapM_forall₂ ht).imp fun x d hd => ?_) hc h hr
    · obtain ⟨t', ha, rfl⟩ := hd
      exact corr_type hc h ha hr
    · cases ha : ToRef.defType x <;> simp [ha, Functor.map, Except.map] at hd
      exact ⟨_, rfl, hd.symm⟩
  | canons xs =>
    simp only [ToRef.section_, Except.ok.injEq] at ht
    subst ht
    refine forM_corr (D := fun x d => d = .canon (ToRef.canon x))
      (fun x d s s' R R' hd hc h hr => ?_) (forall₂_map_self _ xs) hc h hr
    subst hd
    exact corr_canon hc h hr
  | start st => cases h
  | imports xs =>
    simp only [ToRef.section_, Except.ok.injEq] at ht
    subst ht
    refine forM_corr (D := fun x d => d = .import_ (ToRef.externName x.name) (ToRef.externDesc x.desc))
      (fun x d s s' R R' hd hc h hr => ?_) (forall₂_map_self _ xs) hc h hr
    subst hd
    exact corr_import hc h hr
  | exports xs =>
    simp only [ToRef.section_, Except.ok.injEq] at ht
    subst ht
    refine forM_corr (D := fun x d => d = .export_ (ToRef.externName x.name) (ToRef.sortIdx x.item)
        (x.desc.map ToRef.externDesc))
      (fun x d s s' R R' hd hc h hr => ?_) (forall₂_map_self _ xs) hc h hr
    subst hd
    exact corr_export hc h hr
  | values xs => cases h

theorem corr_sections : ∀ {ss : List Binary.Section} {ds : List RDef} {s s' : St} {R R' : RSt},
    Corr s R → (ss.forM section_).run s = .ok ((), s') → ToRef.sections ss = .ok ds →
    ds.foldlM refStep R = some R' → Corr s' R'
  | [], ds, s, s', R, R', hc, h, ht, hr => by
    simp only [ToRef.sections] at ht; cases ht
    cases h; simp at hr; subst hr; exact hc
  | sec :: ss, ds, s, s', R, R', hc, h, ht, hr => by
    obtain ⟨s1, h1, h2⟩ := forM_run_cons h
    simp only [ToRef.sections, bind, Except.bind, pure, Except.pure] at ht
    split at ht
    · cases ht
    · rename_i d1 hd1
      split at ht
      · cases ht
      · rename_i d2 hd2
        cases ht
        rw [List.foldlM_append] at hr
        simp only [bind, Option.bind] at hr
        cases hR : d1.foldlM refStep R with
        | none => simp [hR] at hr
        | some R1 =>
          simp only [hR] at hr
          exact corr_sections (corr_section hc h1 hd1 hR) h2 hd2 hr

/-! ## The import pass -/

/-- A definition that adds neither a type nor an import. -/
def Keeps (d : RDef) : Prop := (∀ f, d ≠ .type f) ∧ ∀ n e, d ≠ .import_ n e

theorem refStep_keeps {R R' : RSt} {d : RDef} (hk : Keeps d) (h : refStep R d = some R') :
    R'.types = R.types ∧ R'.imports = R.imports := by
  obtain ⟨h1, h2⟩ := hk
  unfold refStep at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · exact absurd rfl (h1 _)
  · exact absurd rfl (h2 _ _)
  all_goals first
    | cases h
    | (simp only [bind, Option.bind_eq_some_iff] at h; aesop)

theorem foldlM_keeps : ∀ {ds : List RDef} {R R' : RSt}, (∀ d ∈ ds, Keeps d) →
    ds.foldlM refStep R = some R' → R'.types = R.types ∧ R'.imports = R.imports
  | [], R, R', _, h => by simp at h; subst h; exact ⟨rfl, rfl⟩
  | d :: ds, R, R', hk, h => by
    simp only [List.foldlM_cons, bind, Option.bind] at h
    cases hR : refStep R d with
    | none => simp [hR] at h
    | some R1 =>
      simp only [hR] at h
      obtain ⟨a1, b1⟩ := refStep_keeps (hk d (by simp)) hR
      obtain ⟨a2, b2⟩ := foldlM_keeps (fun d hd => hk d (by simp [hd])) h
      exact ⟨a2.trans a1, b2.trans b1⟩

/-- The invariant of the import pass: its types and imports are those of the reading. -/
def PInv (acc : Array TypeEntry × Iface) (R : RSt) : Prop :=
  acc.1.toList = R.types.map TypeEntry.func ∧ acc.2 = R.imports

theorem pass_types {xs : List Binary.DefType} {ds : List RDef}
    (hd : List.Forall₂ (fun x d => ∃ t', ToRef.defType x = .ok t' ∧ d = .type t') xs ds) :
    ∀ {acc : Array TypeEntry × Iface} {R R' : RSt} {res : Array TypeEntry},
      PInv acc R → ds.foldlM refStep R = some R' →
      forIn xs acc.1 (fun t s => (pure (ForInStep.yield (s.push (typeEntry s t))) :
        Except String (ForInStep (Array TypeEntry)))) = .ok res →
      PInv (res, acc.2) R' := by
  induction hd with
  | nil =>
    intro acc R R' res hi hr h
    simp at hr; subst hr
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at h; subst h
    exact hi
  | cons hx _ ih =>
    rename_i x d xs ds
    intro acc R R' res hi hr h
    obtain ⟨t', ht, rfl⟩ := hx
    simp only [List.foldlM_cons, bind, Option.bind] at hr
    cases hR : refStep R (.type t') with
    | none => simp [hR] at hr
    | some R1 =>
      simp only [hR] at hr
      cases t' with
      | func f =>
        obtain ⟨g, rfl, rfl⟩ := defType_func ht
        simp only [refStep, bind, Option.bind] at hR
        cases hf : refFuncTy (ToRef.funcType g) with
        | none => simp [hf] at hR
        | some ft =>
          simp only [hf, Option.some.injEq] at hR
          subst hR
          simp only [List.forIn_cons, pure, Except.pure, bind, Except.bind] at h
          refine ih (acc := (acc.1.push (typeEntry acc.1 (.func g)), acc.2)) ?_ hr h
          exact ⟨by simp [hi.1, typeEntry, refFuncTy_funcTy acc.1 hf], hi.2⟩
      | _ => simp [refStep] at hR

theorem pass_imports {xs : List Binary.Import} :
    ∀ {acc : Array TypeEntry × Iface} {R R' : RSt} {res : Array TypeEntry × Iface},
      PInv acc R →
      (xs.map fun x => (.import_ (ToRef.externName x.name) (ToRef.externDesc x.desc) : RDef)).foldlM
        refStep R = some R' →
      forIn xs (acc.1, acc.2) (fun i s => do
        let l ← importIface s.1 i
        match i.desc with
        | .type (.eq t) => pure (ForInStep.yield (s.1.push (s.1[t]?.getD (TypeEntry.other "bad type import")), s.2 ++ l))
        | .type .subResource => pure (ForInStep.yield (s.1.push (TypeEntry.other "resources"), s.2 ++ l))
        | _ => pure (ForInStep.yield (s.1, s.2 ++ l))) = .ok res →
      PInv res R' := by
  induction xs with
  | nil =>
    intro acc R R' res hi hr h
    simp at hr; subst hr
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at h; subst h
    exact hi
  | cons x xs ih =>
    intro acc R R' res hi hr h
    simp only [List.map_cons, List.foldlM_cons, bind, Option.bind] at hr
    rcases x with ⟨n, d⟩
    cases d with
    | func t =>
      cases hR : refStep R (.import_ (ToRef.externName n) (ToRef.externDesc (.func t))) with
      | none => simp [hR] at hr
      | some R1 =>
        simp only [hR] at hr
        simp only [ToRef.externDesc, refStep, bind, Option.bind] at hR
        cases hft : R.types[t]? with
        | none => simp [hft] at hR
        | some ft =>
          simp only [hft, Option.some.injEq] at hR
          subst hR
          have ht : acc.1[t]? = some (.func ft) := by
            rw [← Array.getElem?_toList, hi.1]; simp [hft]
          simp only [List.forIn_cons, importIface, ht, pure, Except.pure, bind, Except.bind] at h
          refine ih (acc := (acc.1, acc.2 ++ [(n.name, ft)])) ?_ hr h
          exact ⟨hi.1, by simp [hi.2, ToRef.externName]⟩
    | _ =>
      simp [ToRef.externDesc, refStep] at hr

theorem foldlM_each : ∀ {ds : List RDef} {R R' : RSt}, ds.foldlM refStep R = some R' →
    ∀ d ∈ ds, ∃ R1 R2, refStep R1 d = some R2
  | [], _, _, _, d, hd => by simp at hd
  | d :: ds, R, R', h, e, he => by
    simp only [List.foldlM_cons, bind, Option.bind] at h
    cases hR : refStep R d with
    | none => simp [hR] at h
    | some R1 =>
      simp only [hR] at h
      rcases List.mem_cons.1 he with rfl | he
      · exact ⟨R, R1, hR⟩
      · exact foldlM_each h e he

theorem forIn_skip {α β : Type} {P : α → Prop} [DecidablePred P] {g : α → β → β} :
    ∀ {xs : List α} {a res : β}, (∀ x ∈ xs, ¬ P x) →
      forIn xs a (fun x s => if P x then (pure (ForInStep.yield (g x s)) : Except String _)
        else pure (ForInStep.yield s)) = .ok res → res = a
  | [], a, res, _, h => by simp [pure, Except.pure] at h; exact h.symm
  | x :: xs, a, res, hx, h => by
    simp only [List.forIn_cons, hx x (by simp), ite_false, pure, Except.pure, bind, Except.bind] at h
    exact forIn_skip (fun y hy => hx y (by simp [hy])) h

theorem keeps_coreModule (m : Silmaril.Wasm.Module) : Keeps (.coreModule m) :=
  ⟨fun _ h => (by cases h), fun _ _ h => (by cases h)⟩

theorem pass_sections {F : Binary.Section → Array TypeEntry × Iface →
      Except String (ForInStep (Array TypeEntry × Iface))}
    (hF : ∀ sec acc ds R R' res, PInv acc R → ToRef.section_ sec = .ok ds →
      ds.foldlM refStep R = some R' → F sec acc = .ok res → ∃ acc', res = .yield acc' ∧ PInv acc' R') :
    ∀ {ss : List Binary.Section} {acc : Array TypeEntry × Iface} {ds : List RDef} {R R' : RSt}
      {res : Array TypeEntry × Iface}, PInv acc R → ToRef.sections ss = .ok ds →
      ds.foldlM refStep R = some R' → forIn ss acc F = .ok res → PInv res R'
  | [], acc, ds, R, R', res, hi, ht, hr, h => by
    simp only [ToRef.sections] at ht; cases ht
    simp at hr; subst hr
    simp [pure, Except.pure] at h; subst h; exact hi
  | sec :: ss, acc, ds, R, R', res, hi, ht, hr, h => by
    simp only [ToRef.sections, bind, Except.bind, pure, Except.pure] at ht
    split at ht
    · cases ht
    · rename_i d1 hd1
      split at ht
      · cases ht
      · rename_i d2 hd2
        cases ht
        rw [List.foldlM_append] at hr
        simp only [bind, Option.bind] at hr
        cases hR : d1.foldlM refStep R with
        | none => simp [hR] at hr
        | some R1 =>
          simp only [hR] at hr
          simp only [List.forIn_cons, bind, Except.bind] at h
          cases hf : F sec acc with
          | error e => simp [hf] at h
          | ok st =>
            obtain ⟨acc', rfl, hi'⟩ := hF sec acc d1 R R1 st hi hd1 hR hf
            simp only [hf] at h
            exact pass_sections hF hi' hd2 hr h

theorem forall₂_mem_left {α β : Type} {P : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ P xs ys → ∀ {x}, x ∈ xs → ∃ y ∈ ys, P x y
  | [], _, _, _, hx => by simp at hx
  | _ :: _, _ :: _, .cons hp hr, _, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨_, by simp, hp⟩
    · obtain ⟨y, hy, h⟩ := forall₂_mem_left hr hx
      exact ⟨y, by simp [hy], h⟩

/-- `Keeps` of a definition that is neither a type nor an import. -/
macro "keepsT" : tactic => `(tactic| exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h)⟩)

theorem keeps_all_pinv {acc : Array TypeEntry × Iface} {ds : List RDef} {R R' : RSt}
    (hk : ∀ d ∈ ds, Keeps d) (hi : PInv acc R) (hr : ds.foldlM refStep R = some R') :
    PInv acc R' := by
  obtain ⟨a, b⟩ := foldlM_keeps hk hr
  exact ⟨hi.1.trans (by rw [a]), hi.2.trans b.symm⟩

theorem importsPass_ok {ss : List Binary.Section} {imps : Iface} {ds : List RDef} {R R' : RSt}
    (h : importsPass ss = .ok imps) (ht : ToRef.sections ss = .ok ds)
    (hr : ds.foldlM refStep R = some R') (h0 : R.types = []) (h1 : R.imports = []) :
    imps = R'.imports := by
  unfold importsPass at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i res hres
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  refine (pass_sections (fun sec acc ds R R' res hi hts hr hf => ?_) ⟨by simp [h0], by simp [h1]⟩
    ht hr hres).2
  cases sec with
  | types xs =>
    dsimp only at hf
    split at hf
    · cases hf
    rename_i r1 hr1
    simp only [pure, Except.pure, Except.ok.injEq] at hf
    subst hf
    simp only [ToRef.section_] at hts
    refine ⟨_, rfl, pass_types ((mapM_forall₂ hts).imp fun x d hd => ?_) hi hr hr1⟩
    cases ha : ToRef.defType x <;> simp [ha, Functor.map, Except.map] at hd
    exact ⟨_, rfl, hd.symm⟩
  | imports xs =>
    dsimp only at hf
    split at hf
    · cases hf
    rename_i r1 hr1
    simp only [pure, Except.pure, Except.ok.injEq] at hf
    subst hf
    simp only [ToRef.section_, Except.ok.injEq] at hts
    subst hts
    exact ⟨_, rfl, pass_imports hi hr hr1⟩
  | aliases xs =>
    dsimp only at hf
    split at hf
    · cases hf
    rename_i r1 hr1
    simp only [pure, Except.pure, Except.ok.injEq] at hf
    subst hf
    simp only [ToRef.section_] at hts
    have hall := mapM_forall₂ hts
    have hsort : ∀ x ∈ xs, ¬ x.sort = .type := by
      intro x hx hs
      obtain ⟨d, hd, hxd⟩ := forall₂_mem_left hall hx
      obtain ⟨R1, R2, hR⟩ := foldlM_each hr d hd
      cases ha : ToRef.aliasDef x with
      | error e => simp [ha, Functor.map, Except.map] at hxd
      | ok a' =>
        simp [ha, Functor.map, Except.map] at hxd
        subst hxd
        rcases x with ⟨srt, tgt⟩
        simp only at hs
        subst hs
        cases tgt <;> simp [ToRef.aliasDef] at ha <;> subst ha <;> simp [refStep] at hR
    have := forIn_skip hsort hr1
    subst this
    refine ⟨_, rfl, keeps_all_pinv (fun d hd => ?_) hi hr⟩
    obtain ⟨x, -, hx⟩ := mapM_ok hts d hd
    cases ha : ToRef.aliasDef x <;> simp [ha, Functor.map, Except.map] at hx
    subst hx
    exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h)⟩
  | exports xs =>
    dsimp only at hf
    split at hf
    · cases hf
    rename_i r1 hr1
    simp only [pure, Except.pure, Except.ok.injEq] at hf
    subst hf
    simp only [ToRef.section_, Except.ok.injEq] at hts
    subst hts
    have hsort : ∀ x ∈ xs, ¬ x.item.sort = .type := by
      intro x hx hs
      obtain ⟨R1, R2, hR⟩ := foldlM_each hr _ (List.mem_map_of_mem hx)
      rcases x with ⟨n, ⟨srt, i⟩, d⟩
      simp only at hs
      subst hs
      cases d <;> simp [refStep, ToRef.sortIdx, ToRef.sort] at hR
    have := forIn_skip hsort hr1
    subst this
    refine ⟨_, rfl, keeps_all_pinv (fun d hd => ?_) hi hr⟩
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hd
    exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h)⟩
  | _ =>
    simp only [pure, Except.pure, Except.ok.injEq] at hf
    subst hf
    refine ⟨_, rfl, keeps_all_pinv (fun d hd => ?_) hi hr⟩
    first
      | (simp only [ToRef.section_, Except.ok.injEq] at hts; subst hts
         first
           | (obtain ⟨x, -, rfl⟩ := List.mem_map.1 hd; keepsT)
           | (simp at hd; subst hd; keepsT)
           | simp at hd)
      | (simp only [ToRef.section_] at hts
         obtain ⟨x, -, hx⟩ := mapM_ok hts d hd
         cases ha : ToRef.coreType x <;> simp [ha, Functor.map, Except.map] at hx
         subst hx; keepsT)
      | (simp only [ToRef.section_, bind, Except.bind, pure, Except.pure] at hts
         split at hts
         · cases hts
         · cases hts; simp at hd; subst hd; keepsT)

/-! ## The main theorem -/

theorem refStep_imports {R R' : RSt} {d : RDef} (h : refStep R d = some R') :
    R'.imports.length = R.imports.length + (if isFuncImport d then 1 else 0) := by
  unfold refStep at h
  split at h
  all_goals first
    | (cases h; done)
    | (cases h; simp [isFuncImport])
    | (simp only [bind, Option.bind_eq_some_iff] at h; aesop (add norm isFuncImport))

theorem foldlM_imports : ∀ {ds : List RDef} {R R' : RSt}, ds.foldlM refStep R = some R' →
    R'.imports.length = R.imports.length + (ds.filter isFuncImport).length
  | [], R, R', h => by simp at h; subst h; simp
  | d :: ds, R, R', h => by
    simp only [List.foldlM_cons, bind, Option.bind] at h
    cases hR : refStep R d with
    | none => simp [hR] at h
    | some R1 =>
      simp only [hR] at h
      rw [foldlM_imports h, refStep_imports hR, List.filter_cons]
      split <;> simp_all
      omega

theorem relW_of_lower {a : Binary.Ast} {c : Comp CoreMod} {r : RefComponent}
    (hl : lower a = .ok c) (ht : toRef a = .ok r) (hf : InFrag r) : RelW c r := by
  unfold InFrag inFrag at hf
  cases hR : refRead r with
  | none => simp [hR] at hf
  | some Rf =>
    unfold refRead at hR
    rcases a with ⟨ss⟩
    have ht' : ToRef.sections ss = .ok r := by simpa [toRef, ToRef.ast] using ht
    unfold lower at hl
    simp only [bind, Except.bind] at hl
    split at hl
    · cases hl
    rename_i imps himps
    split at hl
    · cases hl
    rename_i us hus
    split at hl
    · cases hl
    simp only [pure, Except.pure, Except.ok.injEq] at hl
    subst hl
    have him := importsPass_ok himps ht' hR rfl rfl
    have hcount := foldlM_imports hR
    simp only [List.length_nil, Nat.zero_add] at hcount
    have hc0 : Corr { env := imps.length } { env := (r.filter isFuncImport).length } :=
      { mods := .nil, types := rfl, funcs := rfl, coreFuncs := rfl, coreInsts := .nil,
        next := rfl, env := by rw [him, hcount], nodes := .nil, exports := rfl }
    have hc := corr_sections hc0 hus ht' hR
    exact ⟨Rf, by unfold refRead; exact hR, him, hc.exports, hc.nodes⟩

theorem relW_of_decode {b : ByteArray} {c : Comp CoreMod} {r : RefComponent}
    (hc : Binary.parseComponent b = .ok c) (hr : decodeRef b = .ok r) (hf : InFrag r) :
    RelW c r := by
  obtain ⟨a, -, hl, ht⟩ := decoders_factor hc hr
  exact relW_of_lower hl ht hf

end Silmaril.Proofs.Wasm.Component.DecoderBridge
