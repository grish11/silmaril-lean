module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore.Read
public import Silmaril.Wasm.Component.DecoderBridge.FirstImp.Defs

/-!
# The wiring of the first node of the symbolic reading

`FirstCore.Read.refRead_first` reads the module of the first node of `refRead r`. Here its
wiring: before the first core instantiation (`preOk`), every component function is an import,
every core function is the `canon lower` of an import and every core instance is inline
(`PreW`), so every import of the first node is wired to `⟨[.lower ft], .call k⟩`, the lowering of
import `k` of type `ft` (`refRead_firstW`), one wiring per import name `coreIface` reads
(`coreIface_names_length`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp

open Silmaril.Wasm.Component Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Proofs.Wasm.Component.DecoderBridge (RDef)
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore

/-! ## The interface of a decoded module -/

theorem forIn_inv {α σ ε : Type} {F : α → σ → Except ε (ForInStep σ)} (inv : σ → Prop)
    (hF : ∀ x s r, F x s = .ok r → inv s → ∃ s', r = .yield s' ∧ inv s') :
    ∀ (xs : List α) (s W : σ), forIn xs s F = .ok W → inv s → inv W
  | [], s, W, h, hs => by
    simp only [List.forIn_nil] at h
    cases h
    exact hs
  | x :: xs, s, W, h, hs => by
    simp only [List.forIn_cons] at h
    cases hx : F x s with
    | error e => rw [hx] at h; cases h
    | ok r =>
      rw [hx] at h
      obtain ⟨s', rfl, hs'⟩ := hF x s r hx hs
      exact forIn_inv inv hF xs s' W h hs'

/-- `coreIface` reads one name per import. -/
theorem coreIface_names_length {m : Silmaril.Wasm.Module} {n : List (String × String)}
    {i e : CoreIface} (h : coreIface m = .ok (n, i, e)) : n.length = i.length := by
  unfold coreIface at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i v hv
    split at h
    · cases h
    · cases h
      have := forIn_inv (fun s : Array (String × String) × Array (String × CoreFuncTy) =>
          s.1.size = s.2.size) ?_ _ _ _ hv rfl
      · simpa using this
      · intro x s r hr hs
        rcases x with ⟨mn, nm, ty⟩
        cases ty with
        | func t =>
          simp only at hr
          split at hr
          · cases hr
          · cases hr
            exact ⟨_, rfl, by simp [hs]⟩
        | _ => cases hr

/-! ## The symbolic reading before the first core instantiation -/

/-- **The symbolic state before the first core instantiation**: component functions are imports,
core functions are lowerings of imports, core instances are inline. -/
structure PreW (R : RSt) : Prop where
  funcs : ∀ p ∈ R.funcs, ∃ k, p.1 = ⟨[], .call k⟩ ∧ (R.imports[k]?).map (·.2) = some p.2
  coreFuncs : ∀ im ∈ R.coreFuncs, ∃ k ft, im = ⟨[.lower ft], .call k⟩ ∧
    (R.imports[k]?).map (·.2) = some ft
  coreInsts : ∀ ci ∈ R.coreInsts, ∃ es, ci = .inline es ∧ ∀ e ∈ es, e.2 ∈ R.coreFuncs

theorem refStep_imports {R R' : RSt} {d : RDef} (h : refStep R d = some R') :
    R.imports <+: R'.imports := by
  unfold refStep at h
  split at h
  all_goals first
    | (cases h; exact List.prefix_refl _)
    | cases h
    | (simp only [bind, Option.bind_eq_some_iff] at h; aesop)

theorem foldlM_imports : ∀ {ds : List RDef} {R R' : RSt}, ds.foldlM refStep R = some R' →
    R.imports <+: R'.imports
  | [], R, R', h => by simp at h; subst h; exact List.prefix_refl _
  | d :: ds, R, R', h => by
    simp only [List.foldlM_cons, bind, Option.bind] at h
    cases hR : refStep R d with
    | none => simp [hR] at h
    | some R1 =>
      simp only [hR] at h
      exact (refStep_imports hR).trans (foldlM_imports h)

theorem getElem?_prefix {α : Type} {l l' : List α} (h : l <+: l') {k : Nat} {x : α}
    (hk : l[k]? = some x) : l'[k]? = some x := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hk).1, hk]

theorem map_getElem?_prefix {α β : Type} {l l' : List α} (h : l <+: l') {k : Nat} {f : α → β}
    {y : β} (hk : (l[k]?).map f = some y) : (l'[k]?).map f = some y := by
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hk
  rw [getElem?_prefix h hx]
  rfl

theorem PreW.mono_imports {R : RSt} (h : PreW R) {is : Iface} (hp : R.imports <+: is) :
    PreW { R with imports := is } :=
  ⟨fun p hp' => by
      obtain ⟨k, h1, h2⟩ := h.funcs p hp'
      exact ⟨k, h1, map_getElem?_prefix hp h2⟩,
    fun im him => by
      obtain ⟨k, ft, h1, h2⟩ := h.coreFuncs im him
      exact ⟨k, ft, h1, map_getElem?_prefix hp h2⟩,
    h.coreInsts⟩

theorem lookup_mem_snd {α β : Type} [BEq α] {l : List (α × β)} {a : α} {b : β}
    (h : l.lookup a = some b) : ∃ e ∈ l, e.2 = b := by
  induction l with
  | nil => cases h
  | cons p l ih =>
    rcases p with ⟨k, v⟩
    simp only [List.lookup] at h
    split at h
    · cases h; exact ⟨(k, b), List.mem_cons_self, rfl⟩
    · obtain ⟨e, he, rfl⟩ := ih h
      exact ⟨e, List.mem_cons_of_mem _ he, rfl⟩

theorem forall₂_mem_right {α β : Type} {Rel : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ Rel l l') {b : β} (hb : b ∈ l') : ∃ a ∈ l, Rel a b := by
  induction h with
  | nil => cases hb
  | cons hab _ ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨a, ha, hr⟩ := ih hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

theorem refStep_preW {R R' : RSt} {d : RDef} (hW : PreW R)
    (hd : (∃ m, d = .coreModule m) ∨ (∃ ft, d = .type (.func ft)) ∨
      (∃ n t, d = .import_ n (.func t)) ∨ (∃ g, d = .canon (.lower g [])) ∨
      (∃ items, d = .coreInstance (.exports items)))
    (h : refStep R d = some R') : PreW R' := by
  rcases hd with ⟨mo, rfl⟩ | ⟨ft, rfl⟩ | ⟨n, t, rfl⟩ | ⟨g, rfl⟩ | ⟨items, rfl⟩
  · simp only [refStep, Option.some.injEq] at h
    subst h
    exact ⟨hW.funcs, hW.coreFuncs, hW.coreInsts⟩
  · simp only [refStep, bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨_, -, rfl⟩ := h
    exact ⟨hW.funcs, hW.coreFuncs, hW.coreInsts⟩
  · simp only [refStep, bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ft, hft, rfl⟩ := h
    have hp : R.imports <+: R.imports ++ [(n.name, ft)] := List.prefix_append _ _
    refine ⟨fun p hp' => ?_, fun im him => ?_, hW.coreInsts⟩
    · rcases List.mem_append.mp hp' with hp' | hp'
      · obtain ⟨k, h1, h2⟩ := hW.funcs p hp'
        exact ⟨k, h1, map_getElem?_prefix hp h2⟩
      · rw [List.mem_singleton.mp hp']
        refine ⟨R.imports.length, rfl, ?_⟩
        simp
    · obtain ⟨k, ft', h1, h2⟩ := hW.coreFuncs im him
      exact ⟨k, ft', h1, map_getElem?_prefix hp h2⟩
  · simp only [refStep, bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨im, ft⟩, hg, h⟩ := h
    split at h
    · cases h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨k, hk, hft⟩ := hW.funcs _ (List.mem_of_getElem? hg)
      simp only at hk hft
      refine ⟨hW.funcs, fun im' him' => ?_, fun ci hci => ?_⟩
      · rcases List.mem_append.mp him' with him' | him'
        · exact hW.coreFuncs im' him'
        · rw [List.mem_singleton.mp him', hk]
          exact ⟨k, ft, rfl, hft⟩
      · obtain ⟨es, h1, h2⟩ := hW.coreInsts ci hci
        exact ⟨es, h1, fun e he => List.mem_append_left _ (h2 e he)⟩
  · simp only [refStep, bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨es, hes, rfl⟩ := h
    refine ⟨hW.funcs, hW.coreFuncs, fun ci hci => ?_⟩
    rcases List.mem_append.mp hci with hci | hci
    · exact hW.coreInsts ci hci
    · rw [List.mem_singleton.mp hci]
      refine ⟨es, rfl, fun e he => ?_⟩
      obtain ⟨l, hl, hle⟩ := forall₂_mem_right (List.mapM_eq_some_iff_forall₂.mp hes) he
      split at hle
      · obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hle
        exact List.mem_of_getElem? hx
      · cases hle

theorem foldlM_preW : ∀ {nf ncf : Nat} {ds : List RDef} {R R' : RSt}, preOk nf ncf ds = true →
    PreW R → ds.foldlM refStep R = some R' → PreW R'
  | _, _, [], R, R', _, hW, h => by simp at h; subst h; exact hW
  | nf, ncf, d :: ds, R, R', hp, hW, h => by
    simp only [List.foldlM_cons, bind, Option.bind] at h
    cases hR : refStep R d with
    | none => simp [hR] at h
    | some R1 =>
      simp only [hR] at h
      match d, hp with
      | .coreModule _, hp =>
        exact foldlM_preW (by simpa [preOk] using hp) (refStep_preW hW (.inl ⟨_, rfl⟩) hR) h
      | .type (.func _), hp =>
        simp only [preOk, Bool.and_eq_true] at hp
        exact foldlM_preW hp.2 (refStep_preW hW (.inr (.inl ⟨_, rfl⟩)) hR) h
      | .import_ _ (.func _), hp =>
        simp only [preOk] at hp
        exact foldlM_preW hp (refStep_preW hW (.inr (.inr (.inl ⟨_, _, rfl⟩))) hR) h
      | .canon (.lower _ []), hp =>
        simp only [preOk, Bool.and_eq_true] at hp
        exact foldlM_preW hp.2 (refStep_preW hW (.inr (.inr (.inr (.inl ⟨_, rfl⟩)))) hR) h
      | .coreInstance (.exports _), hp =>
        simp only [preOk, Bool.and_eq_true] at hp
        exact foldlM_preW hp.2 (refStep_preW hW (.inr (.inr (.inr (.inr ⟨_, rfl⟩)))) hR) h

/-- **The first node of the symbolic reading, with its wiring**: the module of the first core
instantiation, with one wiring per import name, each the lowering of an import. -/
theorem refRead_firstW {r : Conformance.RefComponent} {R : RSt} {pre post : List RDef} {mi : Nat}
    {cargs : List (String × Nat)} (hs : r = pre ++ .coreInstance (.instantiate mi cargs) :: post)
    (hp : preOk 0 0 pre = true) (hR : refRead r = some R) :
    ∃ m w names i e, (coreMods pre)[mi]? = some m ∧ R.nodes[0]? = some (m, w) ∧
      coreIface m = .ok (names, i, e) ∧ w.length = names.length ∧
      ∀ im ∈ w, ∃ k ft, im = ⟨[.lower ft], .call k⟩ ∧ (R.imports[k]?).map (·.2) = some ft := by
  unfold refRead at hR
  rw [hs, List.foldlM_append] at hR
  simp only [bind, Option.bind_eq_some_iff, List.foldlM_cons] at hR
  obtain ⟨R₁, h₁, R₂, h₂, hR⟩ := hR
  obtain ⟨hn₁, hm₁⟩ := foldlM_other (preOk_noInst hp) h₁
  have hW₁ : PreW R₁ := foldlM_preW hp ⟨by simp, by simp, by simp⟩ h₁
  have hi₂ := foldlM_imports hR
  have hpre := foldlM_prefix hR
  simp only [refStep, bind, Option.bind_eq_some_iff] at h₂
  obtain ⟨m, hm, ⟨names, i', exps⟩, hci, w, hw, h₂⟩ := h₂
  injection h₂ with h₂
  subst h₂
  rw [hm₁] at hm
  simp only [List.nil_append] at hm
  have hci' : coreIface m = .ok (names, i', exps) := by
    cases hc : coreIface m with
    | error e => rw [hc] at hci; cases hci
    | ok v => rw [hc] at hci; cases hci; rfl
  have hF := List.mapM_eq_some_iff_forall₂.mp hw
  refine ⟨m, w, names, i', exps, hm, ?_, hci', hF.length_eq.symm, fun im him => ?_⟩
  · simp only [hn₁, List.nil_append] at hpre
    obtain ⟨t, ht⟩ := hpre
    rw [← ht]
    simp
  · obtain ⟨q, -, hq⟩ := forall₂_mem_right hF him
    simp only [Option.bind_eq_some_iff] at hq
    obtain ⟨j, -, ci, hci₂, hrc⟩ := hq
    obtain ⟨es, rfl, hes⟩ := hW₁.coreInsts ci (List.mem_of_getElem? hci₂)
    obtain ⟨e, he, rfl⟩ := lookup_mem_snd (show es.lookup q.2 = some im from hrc)
    obtain ⟨k, ft, h1, h2⟩ := hW₁.coreFuncs _ (hes e he)
    exact ⟨k, ft, h1, map_getElem?_prefix hi₂ h2⟩

end Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp
