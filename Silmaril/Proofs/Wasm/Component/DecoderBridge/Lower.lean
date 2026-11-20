module

public import Silmaril.Wasm.Component.DecoderBridge.Defs

/-!
# The IR reading: what `Binary.lower` does with core modules and core instantiations

`lower_ok`: if `Binary.lower a = .ok c`, then the nodes of `c` are, in order, one core node per
top-level core `instantiate` of `a`, over the module that `Binary.Lower.coreMod` reads from the
bytes of the core module section at the instantiation's index; and no top-level import, alias or
export of `a` has the core module sort (`lower` rejects them).

The proof follows the state of `lower` through the sections. `KeepsTo v x`: a run of `x` from a
state whose modules and nodes are `v` ends in a state whose modules and nodes are `v`; every
section handler other than core modules and core instances keeps them (`keeps_tac`, by the
shape of the handler's `do` block). `coreMod_ok`: `coreMod bs` keeps the bytes `bs` and the core
decoder accepts them.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Binary Silmaril.Wasm.Component.Binary.Lower
open Silmaril.Wasm.Component.DecoderBridge

/-- The part of the lowering state the bridge follows: core modules and nodes. -/
def key (s : St) : Array CoreMod × Array (Node CoreMod) := (s.modules, s.nodes)

/-- A run of `x` from a state with `key = v` ends in a state with `key = v`. -/
def KeepsTo {α : Type} (v : Array CoreMod × Array (Node CoreMod)) (x : M α) : Prop :=
  ∀ s a s', x.run s = .ok (a, s') → key s = v → key s' = v

theorem keeps_pure {α} {v} (a : α) : KeepsTo v (pure a : M α) := by
  intro s b s' h hv; cases h; exact hv
theorem keeps_throw {α} {v} (e : String) : KeepsTo v (throw e : M α) := by
  intro s b s' h; cases h
theorem keeps_lift {α} {v} (e : Except String α) : KeepsTo v (liftM e : M α) := by
  intro s b s' h hv; cases e <;> cases h; exact hv
theorem keeps_monadLift {α} {v} (e : Except String α) : KeepsTo v (monadLift e : M α) := by
  intro s b s' h hv; cases e <;> cases h; exact hv
theorem keeps_bind {α β} {v} {x : M α} {f : α → M β} (hx : KeepsTo v x) (hf : ∀ a, KeepsTo v (f a)) :
    KeepsTo v (x >>= f) := by
  intro s b s' h hv
  simp only [StateT.run, bind, StateT.bind, Except.bind] at h
  split at h
  · cases h
  · rename_i p hp; exact hf p.1 p.2 b s' h (hx s p.1 p.2 hp hv)
theorem keeps_get_bind {β} {v} {f : St → M β} (hf : ∀ s, key s = v → KeepsTo v (f s)) :
    KeepsTo v (get >>= f) := by
  intro s b s' h hv
  exact hf s hv s b s' h hv
theorem keeps_set {v} (t : St) (ht : key t = v) : KeepsTo v (set t : M PUnit) := by
  intro s b s' h _; cases h; exact ht
theorem keeps_modify {v} (f : St → St) (hf : ∀ s, key (f s) = key s) : KeepsTo v (modify f : M PUnit) := by
  intro s b s' h hv; cases h; exact (hf s).trans hv
theorem keeps_get? {α} {v} (xs : Array α) (i : Nat) (w : String) : KeepsTo v (get? xs i w) := by
  unfold get?; split
  · exact keeps_pure _
  · exact keeps_throw _
theorem keeps_forIn {α β} {v} (xs : List α) (b : β) {f : α → β → M (ForInStep β)}
    (hf : ∀ a r, KeepsTo v (f a r)) : KeepsTo v (forIn xs b f) := by
  induction xs generalizing b with
  | nil => exact keeps_pure _
  | cons x xs ih =>
    simp only [List.forIn_cons]
    refine keeps_bind (hf x b) fun r => ?_
    cases r
    · exact keeps_pure _
    · exact ih _
theorem keeps_forM {α} {v} (xs : List α) {f : α → M PUnit}
    (hf : ∀ a, KeepsTo v (f a)) : KeepsTo v (xs.forM f) := by
  induction xs with
  | nil => exact keeps_pure _
  | cons x xs ih => exact keeps_bind (hf x) fun _ => ih

theorem keeps_lookupFuncTy {v} (i : Nat) : KeepsTo v (lookupFuncTy i) := by
  unfold lookupFuncTy
  apply keeps_get_bind; intro s _
  split <;> first | exact keeps_pure _ | exact keeps_throw _
theorem keeps_addImport {v} : KeepsTo v addImport := by
  unfold addImport
  apply keeps_get_bind; intro s hs
  exact keeps_bind (keeps_set _ hs) fun _ => keeps_pure _

/-- `KeepsTo v` of a handler, by the shape of its `do` block. -/
macro "keeps_tac" : tactic => `(tactic| repeat (first
  | with_reducible exact keeps_pure _ | with_reducible exact keeps_throw _
  | with_reducible exact keeps_lift _ | with_reducible exact keeps_monadLift _
  | with_reducible exact keeps_get? _ _ _ | with_reducible exact keeps_lookupFuncTy _
  | with_reducible exact keeps_addImport
  | (with_reducible apply keeps_set; simp only [key] at *; assumption)
  | (apply keeps_modify; intro _; rfl)
  | (with_reducible apply keeps_get_bind; intro _ _)
  | (with_reducible apply keeps_forIn; intro _ _)
  | (with_reducible apply keeps_forM; intro _)
  | (with_reducible apply keeps_bind <;> try intro)
  | split
  | (dsimp only)))

theorem k_canon (c : Canon) v : KeepsTo v (canon c) := by
  unfold canon; keeps_tac
theorem k_alias (c : Alias) v : KeepsTo v (alias_ c) := by
  unfold alias_; keeps_tac
theorem k_export (c : Binary.Export) v : KeepsTo v (export_ c) := by
  unfold export_; keeps_tac
theorem k_inst (c : InstanceExpr) v : KeepsTo v (instance_ c) := by
  unfold instance_; keeps_tac
theorem k_import (c : Import) v : KeepsTo v (import_ c) := by
  unfold import_; keeps_tac

theorem keeps_run {α} {x : M α} (hx : ∀ v, KeepsTo v x) {s a s'} (h : x.run s = .ok (a, s')) :
    s'.modules = s.modules ∧ s'.nodes = s.nodes := by
  have := hx (key s) s a s' h rfl
  simp only [key, Prod.mk.injEq] at this
  exact this

theorem k_coreInstance_exports (es : List (String × CoreSortIdx)) v :
    KeepsTo v (coreInstance (.exports es)) := by
  unfold coreInstance; keeps_tac

theorem run_bind_ok {α β} {x : M α} {f : α → M β} {s b s'} (h : (x >>= f).run s = .ok (b, s')) :
    ∃ a s1, x.run s = .ok (a, s1) ∧ (f a).run s1 = .ok (b, s') := by
  simp only [StateT.run, bind, StateT.bind, Except.bind] at h
  split at h
  · cases h
  · rename_i p hp; exact ⟨p.1, p.2, hp, h⟩

theorem run_get_bind {β} {f : St → M β} {s} : (get >>= f).run s = (f s).run s := rfl

theorem run_get? {α} {xs : Array α} {i w s a s'} (h : (get? xs i w).run s = .ok (a, s')) :
    xs[i]? = some a ∧ s' = s := by
  unfold get? at h
  split at h
  · rename_i x hx; cases h; exact ⟨hx, rfl⟩
  · cases h

theorem coreInstance_ok {x : CoreInstanceExpr} {s s'} (h : (coreInstance x).run s = .ok ((), s')) :
    s'.modules = s.modules ∧ ∃ ns, s'.nodes.toList = s.nodes.toList ++ ns ∧
      List.Forall₂ (fun n (e : InstExpr) =>
        ∃ m w, s.modules.toList[e.1]? = some m ∧ n = .core m w) ns
        (Option.toList (instExpr? x)) := by
  cases x with
  | instantiate mi args =>
    unfold coreInstance at h
    rw [run_get_bind] at h
    obtain ⟨m, s1, h1, h⟩ := run_bind_ok h
    obtain ⟨hm, rfl⟩ := run_get? h1
    obtain ⟨w, s2, -, h⟩ := run_bind_ok h
    cases h
    refine ⟨rfl, [.core m w.toList], by simp, ?_⟩
    simp only [instExpr?, Option.toList]
    exact .cons ⟨m, w.toList, by simpa using hm, rfl⟩ .nil
  | exports es =>
    obtain ⟨h1, h2⟩ := keeps_run (k_coreInstance_exports es) h
    exact ⟨h1, [], by simp [h2], by simp [instExpr?]⟩

theorem ex_bind_ok {ε α β} {x : Except ε α} {f : α → Except ε β} {b} (h : (x >>= f) = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem coreMod_ok {bs : ByteArray} {m : CoreMod} (h : coreMod bs = .ok m) :
    m.bytes = bs ∧ ∃ d, Silmaril.Wasm.Binary.Core.decode? bs = some d := by
  unfold coreMod at h
  cases hd : Silmaril.Wasm.Binary.Core.decode? bs with
  | none => simp [hd] at h
  | some d =>
    refine ⟨?_, d, rfl⟩
    simp only [hd] at h
    obtain ⟨_, -, h⟩ := ex_bind_ok h
    obtain ⟨_, -, h⟩ := ex_bind_ok h
    cases h; rfl

theorem import_ok {i : Import} {s a s'} (h : (import_ i).run s = .ok (a, s')) :
    (match i.desc with | .coreModule _ => false | _ => true) = true := by
  revert h
  unfold import_
  cases i.desc <;> simp
  intro h; cases h

theorem alias_ok {x : Alias} {s a s'} (h : (alias_ x).run s = .ok (a, s')) :
    (x.sort != .core .module) = true := by
  rcases x with ⟨srt, tgt⟩
  cases srt with
  | core cs =>
    cases cs <;> simp
    revert h; unfold alias_; cases tgt <;> simp [pure, Except.pure, StateT.run, bind, StateT.bind, get, getThe,
      MonadStateOf.get, StateT.get, Except.bind, throw, throwThe, MonadExceptOf.throw, StateT.lift]
  | _ => simp

theorem export_ok {x : Binary.Export} {s a s'} (h : (export_ x).run s = .ok (a, s')) :
    (x.item.sort != .core .module) = true := by
  rcases x with ⟨n, ⟨srt, idx⟩, d⟩
  cases srt with
  | core cs =>
    cases cs <;> simp
    revert h; unfold export_; simp [pure, Except.pure, StateT.run, bind, StateT.bind, get, getThe,
      MonadStateOf.get, StateT.get, Except.bind, throw, throwThe, MonadExceptOf.throw, StateT.lift]
  | _ => simp


/-- The node relation over the modules array. -/
def NRel (ms : Array CoreMod) (n : Node CoreMod) (e : InstExpr) : Prop :=
  ∃ m w, ms.toList[e.1]? = some m ∧ n = .core m w

theorem forM_run_cons {α} {x : α} {xs : List α} {f : α → M PUnit} {s s'}
    (h : ((x :: xs).forM f).run s = .ok ((), s')) :
    ∃ s1, (f x).run s = .ok ((), s1) ∧ (xs.forM f).run s1 = .ok ((), s') := by
  have e : (x :: xs).forM f = (f x >>= fun _ => xs.forM f) := rfl
  rw [e] at h
  obtain ⟨⟨⟩, s1, h1, h2⟩ := run_bind_ok h
  exact ⟨s1, h1, h2⟩

theorem forM_each {α} {xs : List α} {f : α → M PUnit} {s s'}
    (h : (xs.forM f).run s = .ok ((), s')) : ∀ x ∈ xs, ∃ s1 s2, (f x).run s1 = .ok ((), s2) := by
  induction xs generalizing s with
  | nil => simp
  | cons y ys ih =>
    obtain ⟨s1, h1, h2⟩ := forM_run_cons h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨_, _, h1⟩
    · exact ih h2 x hx

theorem coreInstances_ok {xs : List CoreInstanceExpr} {s s'}
    (h : (xs.forM coreInstance).run s = .ok ((), s')) :
    s'.modules = s.modules ∧ ∃ ns, s'.nodes.toList = s.nodes.toList ++ ns ∧
      List.Forall₂ (NRel s.modules) ns (xs.filterMap instExpr?) := by
  induction xs generalizing s with
  | nil => cases h; exact ⟨rfl, [], by simp, .nil⟩
  | cons x xs ih =>
    obtain ⟨s1, h1, h2⟩ := forM_run_cons h
    obtain ⟨hm1, ns1, hn1, hr1⟩ := coreInstance_ok h1
    obtain ⟨hm2, ns2, hn2, hr2⟩ := ih h2
    refine ⟨hm2.trans hm1, ns1 ++ ns2, by rw [hn2, hn1, List.append_assoc], ?_⟩
    rw [hm1] at hr2
    have : (x :: xs).filterMap instExpr? = (instExpr? x).toList ++ xs.filterMap instExpr? := by
      cases hx : instExpr? x <;> simp [hx]
    rw [this]
    exact List.rel_append hr1 hr2

theorem section_ok {sec : Section} {s s'} (h : (section_ sec).run s = .ok ((), s')) :
    ((∃ ms, s'.modules.toList = s.modules.toList ++ ms ∧
        List.Forall₂ (fun m bs => coreMod bs = .ok m) ms (modBytes [sec])) ∧
    (∃ ns, s'.nodes.toList = s.nodes.toList ++ ns ∧
        List.Forall₂ (NRel s.modules) ns (instExprs [sec]))) ∧
    noModuleSort [sec] = true := by
  have keep : s'.modules = s.modules → s'.nodes = s.nodes → modBytes [sec] = [] →
      instExprs [sec] = [] →
      (∃ ms, s'.modules.toList = s.modules.toList ++ ms ∧
        List.Forall₂ (fun m bs => coreMod bs = .ok m) ms (modBytes [sec])) ∧
      (∃ ns, s'.nodes.toList = s.nodes.toList ++ ns ∧
        List.Forall₂ (NRel s.modules) ns (instExprs [sec])) := by
    intro h1 h2 h3 h4
    exact ⟨⟨[], by simp [h1], by rw [h3]; exact .nil⟩, ⟨[], by simp [h2], by rw [h4]; exact .nil⟩⟩
  cases sec with
  | custom n d =>
    cases h
    exact ⟨keep rfl rfl rfl rfl, rfl⟩
  | coreModule b =>
    obtain ⟨m, s1, h1, h⟩ := run_bind_ok h
    cases hb : coreMod b with
    | error e =>
      simp [hb, liftM, monadLift, MonadLift.monadLift, StateT.lift, StateT.run, bind, Except.bind] at h1
    | ok m' =>
      simp [hb, liftM, monadLift, MonadLift.monadLift, StateT.lift, StateT.run, bind, Except.bind,
        pure, Except.pure] at h1
      obtain ⟨rfl, rfl⟩ := h1
      cases h
      exact ⟨⟨⟨[m'], by simp, by simpa [modBytes] using hb⟩, ⟨[], by simp, by simp [instExprs]⟩⟩, rfl⟩
  | coreInstances xs =>
    obtain ⟨hm, ns, hn, hr⟩ := coreInstances_ok (xs := xs) h
    refine ⟨⟨⟨[], by simp [hm], by simp [modBytes]⟩, ⟨ns, hn, by simpa [instExprs] using hr⟩⟩, rfl⟩
  | coreTypes xs => cases h; exact ⟨keep rfl rfl rfl rfl, rfl⟩
  | component c => cases h
  | instances xs =>
    obtain ⟨h1, h2⟩ := keeps_run (x := xs.forM instance_) (fun v => keeps_forM _ fun a => k_inst a v) h
    exact ⟨keep h1 h2 rfl rfl, rfl⟩
  | aliases xs =>
    obtain ⟨h1, h2⟩ := keeps_run (x := xs.forM alias_) (fun v => keeps_forM _ fun a => k_alias a v) h
    refine ⟨keep h1 h2 rfl rfl, ?_⟩
    have := forM_each (f := alias_) h
    simp only [noModuleSort, sectionNoModuleSort, List.all_cons, List.all_nil, Bool.and_true,
      List.all_eq_true]
    intro x hx
    obtain ⟨_, _, hx⟩ := this x hx
    exact alias_ok hx
  | types xs =>
    obtain ⟨h1, h2⟩ := keeps_run (x := section_ (.types xs))
      (fun v => by unfold section_; exact keeps_forM _ fun a => keeps_modify _ fun _ => rfl) h
    exact ⟨keep h1 h2 rfl rfl, rfl⟩
  | canons xs =>
    obtain ⟨h1, h2⟩ := keeps_run (x := xs.forM canon) (fun v => keeps_forM _ fun a => k_canon a v) h
    exact ⟨keep h1 h2 rfl rfl, rfl⟩
  | start st => cases h
  | imports xs =>
    obtain ⟨h1, h2⟩ := keeps_run (x := xs.forM import_) (fun v => keeps_forM _ fun a => k_import a v) h
    refine ⟨keep h1 h2 rfl rfl, ?_⟩
    have := forM_each (f := import_) h
    simp only [noModuleSort, sectionNoModuleSort, List.all_cons, List.all_nil, Bool.and_true,
      List.all_eq_true]
    intro x hx
    obtain ⟨_, _, hx⟩ := this x hx
    exact import_ok hx
  | exports xs =>
    obtain ⟨h1, h2⟩ := keeps_run (x := xs.forM export_) (fun v => keeps_forM _ fun a => k_export a v) h
    refine ⟨keep h1 h2 rfl rfl, ?_⟩
    have := forM_each (f := export_) h
    simp only [noModuleSort, sectionNoModuleSort, List.all_cons, List.all_nil, Bool.and_true,
      List.all_eq_true]
    intro x hx
    obtain ⟨_, _, hx⟩ := this x hx
    exact export_ok hx
  | values xs => cases h

theorem getElem?_append_of {α} {l1 l2 : List α} {i : Nat} {x : α} (h : l1[i]? = some x) :
    (l1 ++ l2)[i]? = some x := by
  induction l1 generalizing i with
  | nil => simp at h
  | cons y ys ih => cases i <;> simp_all

theorem modBytes_append (p q : List Section) : modBytes (p ++ q) = modBytes p ++ modBytes q := by
  induction p with
  | nil => rfl
  | cons x p ih => cases x <;> simp [modBytes, ih]

theorem instExprs_append (p q : List Section) : instExprs (p ++ q) = instExprs p ++ instExprs q := by
  induction p with
  | nil => rfl
  | cons x p ih => cases x <;> simp [instExprs, ih]

/-- The invariant of `lower` after the sections `p`: the modules are those of `p`'s core module
sections, the nodes those of `p`'s core instantiations, and `p` has no core-module-sort entry. -/
def LInv (p : List Section) (s : St) : Prop :=
  List.Forall₂ (fun m bs => coreMod bs = .ok m) s.modules.toList (modBytes p) ∧
  List.Forall₂ (NRel s.modules) s.nodes.toList (instExprs p) ∧ noModuleSort p = true

theorem sections_ok : ∀ (ss p : List Section) (s s' : St), LInv p s →
    (ss.forM section_).run s = .ok ((), s') → LInv (p ++ ss) s'
  | [], p, s, s', hi, h => by cases h; simpa using hi
  | sec :: ss, p, s, s', ⟨hm, hn, hs⟩, h => by
    obtain ⟨s1, h1, h2⟩ := forM_run_cons h
    obtain ⟨⟨⟨ms, hms, hmr⟩, ⟨ns, hns, hnr⟩⟩, hsec⟩ := section_ok h1
    have mono : ∀ n e, NRel s.modules n e → NRel s1.modules n e := by
      rintro n e ⟨m, w, h, rfl⟩
      exact ⟨m, w, by rw [hms]; exact getElem?_append_of h, rfl⟩
    have hi : LInv (p ++ [sec]) s1 := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hms, modBytes_append]; exact List.rel_append hm hmr
      · rw [hns, instExprs_append]
        exact List.rel_append (hn.imp mono) (hnr.imp mono)
      · simp only [noModuleSort, List.all_append] at hs hsec ⊢
        simp [hs, hsec]
    have := sections_ok ss (p ++ [sec]) s1 s' hi h2
    simpa using this

theorem forall₂_getElem? {α β} {R : α → β → Prop} : ∀ {l1 : List α} {l2 : List β} {i : Nat} {x : α},
    List.Forall₂ R l1 l2 → l1[i]? = some x → ∃ y, l2[i]? = some y ∧ R x y
  | [], _, _, _, .nil, h => by simp at h
  | _ :: _, _ :: _, 0, _, .cons hr _, h => by cases h; exact ⟨_, rfl, hr⟩
  | _ :: _, _ :: _, i + 1, _, .cons _ hl, h => forall₂_getElem? (i := i) hl h

theorem lower_ok {a : Ast} {c : Comp CoreMod} (h : lower a = .ok c) :
    List.Forall₂ (fun n e => ∃ bs m w, (modBytes a.sections)[e.1]? = some bs ∧
        coreMod bs = .ok m ∧ n = .core m w) c.nodes (instExprs a.sections) ∧
      noModuleSort a.sections = true := by
  unfold lower at h
  obtain ⟨imps, -, h⟩ := ex_bind_ok h
  obtain ⟨⟨u, s⟩, hs, h⟩ := ex_bind_ok h
  simp only at h
  split at h
  · cases h
  · cases h
    have hi := sections_ok a.sections [] _ s (by simp [LInv, modBytes, instExprs, noModuleSort]) hs
    obtain ⟨hm, hn, hns⟩ := hi
    simp only [List.nil_append] at hm hn hns
    refine ⟨?_, hns⟩
    simp only [Silmaril.Wasm.Component.Comp.nodes]
    refine hn.imp ?_
    rintro n e ⟨m, w, he, rfl⟩
    obtain ⟨bs, hb, hr⟩ := forall₂_getElem? hm he
    exact ⟨bs, m, w, hb, hr, rfl⟩

end Silmaril.Proofs.Wasm.Component.DecoderBridge
