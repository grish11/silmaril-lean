module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq.Games
public import Silmaril.Proofs.Wasm.Component.Reference.ImpIR
public import Silmaril.Proofs.Wasm.Component.Reference.Adequacy.IRPlays

/-!
# Reading back the IR plays of a simple component with imports

`imp_readback`: rounds with lower calls of `c.toComp.denU (impSem P)` whose questions are typed
export calls `(j, .vals vs)` are, layer by layer (the export handler with the lift adapter, the
import mask, `splitH`, the pairing, the `canon lower` wiring `implsN`, `widenH`, `core3Sem`'s
import and export handlers), rounds of the core instance from its store: `RdI c I r u` says
that the instance round `r` answers the lowered core question of `u` after core import calls
corresponding (`ImpRel`) to `u`'s component import calls, and that `u`'s answer is the lift of
`r`'s. The converse of `seqI_den` (`SeqIRI`) at the untyped interface.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Wasm.SingleThreaded (ofFlat toFlat?)
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

/-! ## The handlers -/

theorem oneShot_maskH (e : Nat) : OneShot (maskH e) := by
  intro q
  simp only [maskH, Target.prog]
  split
  · exact .inr ⟨_, fun r => r, rfl⟩
  · exact .inl ⟨none, rfl⟩

theorem oneShot_implsN (e : Nat) (ims : List Impl) (t : Nat) : OneShot (implsN e ims t) :=
  fun q => oneShot_implsH e ims (q.1.val, q.2)

theorem oneShot_importH (m : NumInstance) : OneShot (importH m) :=
  fun _ => .inr ⟨_, fun r => payloadAnswer _ r, rfl⟩

theorem maskH_lt {e k : Nat} (hk : k < e) (p : Payload) :
    maskH e (k, p) = .call (k, p) fun r => .pure r := by
  simp [maskH, Target.prog, hk]

theorem widenH_lt {n k : Nat} (hk : k < n) (p : Payload) :
    widenH n (k, p) = .call (⟨k, hk⟩, p) fun r => .pure r := dite_eq_left hk

/-- A round shifted down by `e`. -/
def downBy {E : Sig.{0}} (e : Nat) (r : CRound E sigU) : CRound E sigU :=
  ⟨(r.q.1 - e, r.q.2), r.cs, r.a⟩

/-- `splitH e` on questions from `e` on: the right component, shifted down. -/
theorem hc_splitH_inv {E : Sig.{0}} {e : Nat} :
    ∀ {up : List (CRound E sigU)} {low : List (CRound E (sigU ⊕ₛ sigU))}, HC (splitH e) up low →
      (∀ r ∈ up, e ≤ r.q.1) → low = (up.map (downBy e)).map (CRound.inr (F₁ := sigU))
  | _, _, .nil, _ => rfl
  | _, _, .pure hq _, _ => by
    simp only [splitH] at hq
    split at hq <;> cases hq
  | _, _, .call (q := q) hq hk H, hge => by
    have hq' : e ≤ q.1 := hge _ List.mem_cons_self
    simp only [splitH, Nat.not_lt.mpr hq', ↓reduceIte] at hq
    cases hq
    cases hk
    rw [hc_splitH_inv H fun r hr => hge r (List.mem_cons_of_mem _ hr)]
    rfl

theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {a : List α} {b : List β}, List.Forall₂ R a b → ∀ x ∈ a, ∃ y, R x y
  | _, _, .nil, _, hx => nomatch hx
  | _, _, .cons h t, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨_, h⟩
    · exact forall₂_mem_left t x hx

theorem forall₂_and_right {α β : Type} {R : α → β → Prop} {Q : β → Prop} :
    ∀ {a : List α} {b : List β}, List.Forall₂ R a b → (∀ y ∈ b, Q y) →
      List.Forall₂ (fun x y => R x y ∧ Q y) a b
  | _, _, .nil, _ => .nil
  | _, _, .cons h t, hq =>
    .cons ⟨h, hq _ List.mem_cons_self⟩
      (forall₂_and_right t fun y hy => hq y (List.mem_cons_of_mem _ hy))

/-! ## The core export -/

/-- The operation of a typed call of core export `k` of a module with imports. -/
def opAtI {m : ImpModule} {I : SInst} (hI : m.IsInst I) {k : Nat} (hk : k < m.exports.length)
    {xs : List Flat} (hxs : xs.map (·.type) = m.exports[k].2.params) : I.F.Op :=
  ⟨Fin.cast (by rw [hI.2.2, List.length_map]) ⟨k, hk⟩,
    ⟨xs.map ofFlat, by
      have hj : I.exports.get (Fin.cast (by rw [hI.2.2, List.length_map]) ⟨k, hk⟩) =
          fnOf m.exports[k].2 := by
        simp only [List.get_eq_getElem, Fin.val_cast, hI.2.2, List.getElem_map]
      have hp : (I.exports.get (Fin.cast (by rw [hI.2.2, List.length_map]) ⟨k, hk⟩)).params =
          xs.map fun x => .num x.type := by
        rw [hj]
        show m.exports[k].2.params.map _ = _
        rw [← hxs, List.map_map]
        rfl
      exact hp ▸ forall₂_hasVal_ofFlat xs⟩⟩

/-! ## The levels -/

section Levels

variable (c : SimpleI)

/-- A typed export call. -/
def TopI (u : CRound sigU sigU) : Prop :=
  ∃ (j : Fin c.exports.length) (vs : List IVal), u.q = (j.val, .vals vs) ∧
    ValTy.checkList c.exports[j].ty.params vs = true

/-- The export handler's round. -/
def L3 (y u : CRound sigU sigU) : Prop :=
  ∃ (j : Fin c.exports.length) (vs : List IVal) (xs : List Flat),
    u.q = (j.val, .vals vs) ∧ checkLower c.exports[j].ty.params vs = some xs ∧
    y.q = (c.exports[j].core + c.imports.length, .flat xs) ∧ y.cs = u.cs ∧
    u.a = y.a.bind (Adapter.up (.lift c.exports[j].ty))

/-- The round below the import mask. -/
def L4 (y u : CRound sigU sigU) : Prop :=
  ∃ (j : Fin c.exports.length) (vs : List IVal) (xs : List Flat),
    u.q = (j.val, .vals vs) ∧ checkLower c.exports[j].ty.params vs = some xs ∧
    y.q = (c.exports[j].core + c.imports.length, .flat xs) ∧
    HRounds (maskH c.imports.length) y.cs u.cs ∧
    u.a = y.a.bind (Adapter.up (.lift c.exports[j].ty))

/-- The round of the module below the `canon lower` wiring. -/
def L6 (y : CRound (sigN (CoreModule.imports c.mod).length) sigU) (u : CRound sigU sigU) :
    Prop :=
  ∃ (j : Fin c.exports.length) (vs : List IVal) (xs : List Flat),
    u.q = (j.val, .vals vs) ∧ checkLower c.exports[j].ty.params vs = some xs ∧
    y.q = (c.exports[j].core, .flat xs) ∧
    (∃ cs₄, HRounds (implsN c.imports.length (SimpleI.lowerArgs c.imports)
      (CoreModule.imports c.mod).length) y.cs cs₄ ∧ HRounds (maskH c.imports.length) cs₄ u.cs) ∧
    u.a = y.a.bind (Adapter.up (.lift c.exports[j].ty))

/-- The round of the module's semantics. -/
def L7 (y : CRound (sigN (CoreModule.imports c.mod).length) (sigN (CoreModule.exports c.mod).length))
    (u : CRound sigU sigU) : Prop :=
  ∃ (j : Fin c.exports.length) (vs : List IVal) (xs : List Flat)
    (hk : c.exports[j].core < (CoreModule.exports c.mod).length),
    u.q = (j.val, .vals vs) ∧ checkLower c.exports[j].ty.params vs = some xs ∧
    y.q = (⟨c.exports[j].core, hk⟩, .flat xs) ∧
    (∃ cs₄, HRounds (implsN c.imports.length (SimpleI.lowerArgs c.imports)
      (CoreModule.imports c.mod).length) y.cs cs₄ ∧ HRounds (maskH c.imports.length) cs₄ u.cs) ∧
    u.a = y.a.bind (Adapter.up (.lift c.exports[j].ty))

/-- The round below `core3Sem`'s import handler. -/
def L8 {I : SInst} (hI : c.mod.IsInst I) (y : CRound I.E (sigN (CoreModule.exports c.mod).length))
    (u : CRound sigU sigU) : Prop :=
  ∃ (j : Fin c.exports.length) (vs : List IVal) (xs : List Flat)
    (hk : c.exports[j].core < (CoreModule.exports c.mod).length),
    u.q = (j.val, .vals vs) ∧ checkLower c.exports[j].ty.params vs = some xs ∧
    y.q = (⟨c.exports[j].core, hk⟩, .flat xs) ∧
    (∃ cs₆ cs₄, HRounds (importH (instNumI hI)) y.cs cs₆ ∧
      HRounds (implsN c.imports.length (SimpleI.lowerArgs c.imports)
        (CoreModule.imports c.mod).length) cs₆ cs₄ ∧ HRounds (maskH c.imports.length) cs₄ u.cs) ∧
    u.a = y.a.bind (Adapter.up (.lift c.exports[j].ty))

/-- **An export round of the importer read back**: the IR round `u` (at the untyped interface)
asks export `j` on `vs`; the instance round `r` answers the lowered core question after core
import calls corresponding (`ImpRel`) to the component import calls `dss` of `u`, and `u`'s
answer is the lift of `r`'s. -/
def RdI (I : SInst) (r : CRound I.E I.F) (u : CRound sigU sigU) : Prop :=
  ∃ (j : Fin c.exports.length) (vs : List IVal) (xs : List Flat)
    (dss : List (List (Round (sigN c.imports.length)))),
    u.q = (j.val, .vals vs) ∧ checkLower c.exports[j].ty.params vs = some xs ∧
    r.q.1.val = c.exports[j].core ∧ r.q.2.1 = xs.map ofFlat ∧
    List.Forall₂ (ImpRel c I) r.cs dss ∧ u.cs = dss.flatten.map Round.forget ∧
    u.a = (answerPayload r.a).bind (Adapter.up (.lift c.exports[j].ty))

end Levels

section Steps

variable {c : SimpleI} (hc : c.Good)
include hc

theorem core_lt (j : Fin c.exports.length) :
    c.exports[j].core < (CoreModule.exports c.mod).length :=
  (List.getElem?_eq_some_iff.mp (hc.core _ (List.getElem_mem j.isLt)).choose_spec).1

theorem exportsH_typed {j : Fin c.exports.length} {vs : List IVal}
    (hck : ValTy.checkList c.exports[j].ty.params vs = true) :
    exportsH (c.imports.length + c.mod.exports.length) c.toComp.exports (j.val, .vals vs) =
      .call (c.exports[j].core + c.imports.length,
          .flat (lowerArgs c.exports[j].ty.params vs))
        fun n => .pure (n.bind (Adapter.up (.lift c.exports[j].ty))) := by
  have hck' : ValTy.checkList c.exports[j.val].ty.params vs = true := hck
  rw [exportsH_toCompI c j.isLt vs (core_lt hc j), checkLower_of_check hck']
  rfl

theorem topI_nonpure {u : CRound sigU sigU} (ht : TopI c u) (a : Option Payload) :
    exportsH (c.imports.length + c.mod.exports.length) c.toComp.exports u.q ≠ .pure a := by
  obtain ⟨⟨n, p⟩, ucs, ua⟩ := u
  obtain ⟨j, vs, hq, hck⟩ := ht
  simp only [Prod.mk.injEq] at hq
  obtain ⟨rfl, rfl⟩ := hq
  rw [exportsH_typed hc hck]
  intro h
  cases h

theorem l3_of {u y : CRound sigU sigU} (ht : TopI c u)
    (h : HCR (exportsH (c.imports.length + c.mod.exports.length) c.toComp.exports) u y) :
    L3 c y u := by
  obtain ⟨⟨n, p⟩, ucs, ua⟩ := u
  obtain ⟨yq, ycs, ya⟩ := y
  obtain ⟨j, vs, hq, hck⟩ := ht
  simp only [Prod.mk.injEq] at hq
  obtain ⟨rfl, rfl⟩ := hq
  obtain ⟨k, hk, hcs, ha⟩ := h
  have hk' := (exportsH_typed hc hck).symm.trans hk
  cases hk'
  exact ⟨j, vs, _, rfl, checkLower_of_check hck, rfl, hcs, (Prog.pure.inj ha).symm⟩

omit hc in
theorem l4_of {x y u : CRound sigU sigU} (hb : HBR (maskH c.imports.length) x y)
    (h : L3 c y u) : L4 c x u := by
  obtain ⟨q, a, cs, cs', rfl, rfl, H⟩ := hb
  obtain ⟨j, vs, xs, hu, hl, hq, hcs, ha⟩ := h
  have hcs' : cs' = u.cs := hcs
  exact ⟨j, vs, xs, hu, hl, hq, hcs' ▸ H, ha⟩

omit hc in
theorem l4_ge {x u : CRound sigU sigU} (h : L4 c x u) : c.imports.length ≤ x.q.1 := by
  obtain ⟨j, vs, xs, -, -, hq, -⟩ := h
  rw [hq]
  exact Nat.le_add_left _ _

omit hc in
theorem l6_of {x : CRound (sigN (CoreModule.imports c.mod).length) sigU} {y u : CRound sigU sigU}
    (hb : HBR (implsN c.imports.length (SimpleI.lowerArgs c.imports)
      (CoreModule.imports c.mod).length) x (downBy c.imports.length y))
    (h : L4 c y u) : L6 c x u := by
  obtain ⟨yq, ycs, ya⟩ := y
  obtain ⟨j, vs, xs, hu, hl, hq, H₄, ha⟩ := h
  have hq' : yq = (c.exports[j].core + c.imports.length, .flat xs) := hq
  subst hq'
  obtain ⟨q, a, cs, cs', rfl, hy, H⟩ := hb
  cases hy
  refine ⟨j, vs, xs, hu, hl, ?_, ⟨ycs, H, H₄⟩, ha⟩
  show (c.exports[j].core + c.imports.length - c.imports.length, Payload.flat xs) = _
  rw [Nat.add_sub_cancel]

theorem l6_nonpure {x : CRound (sigN (CoreModule.imports c.mod).length) sigU}
    {u : CRound sigU sigU} (h : L6 c x u) (a : Option Payload) :
    widenH (CoreModule.exports c.mod).length x.q ≠ .pure a := by
  obtain ⟨xq, xcs, xa⟩ := x
  obtain ⟨j, vs, xs, -, -, hq, -⟩ := h
  have hq' : xq = (c.exports[j].core, .flat xs) := hq
  subst hq'
  show widenH _ (c.exports[j].core, Payload.flat xs) ≠ _
  rw [widenH_lt (core_lt hc j)]
  intro h
  cases h

theorem l7_of {x : CRound (sigN (CoreModule.imports c.mod).length) sigU}
    {y : CRound (sigN (CoreModule.imports c.mod).length) (sigN (CoreModule.exports c.mod).length)}
    {u : CRound sigU sigU} (hw : HCR (widenH (CoreModule.exports c.mod).length) x y)
    (h : L6 c x u) : L7 c y u := by
  obtain ⟨xq, xcs, xa⟩ := x
  obtain ⟨yq, ycs, ya⟩ := y
  obtain ⟨j, vs, xs, hu, hl, hq, hcalls, ha⟩ := h
  have hq' : xq = (c.exports[j].core, .flat xs) := hq
  subst hq'
  obtain ⟨k, hk, hcs, hka⟩ := hw
  have hk' := (widenH_lt (core_lt hc j) _).symm.trans hk
  cases hk'
  have hcs' : ycs = xcs := hcs
  have hya : ya = xa := Prog.pure.inj hka
  subst hcs' hya
  exact ⟨j, vs, xs, core_lt hc j, hu, hl, rfl, hcalls, ha⟩

end Steps

section Core

variable {c : SimpleI} (hc : c.Good) {I : SInst} (hI : c.mod.IsInst I)
include hc hI

omit hc in
theorem l8_of {x : CRound I.E (sigN (CoreModule.exports c.mod).length)}
    {y : CRound (sigN (CoreModule.imports c.mod).length) (sigN (CoreModule.exports c.mod).length)}
    {u : CRound sigU sigU} (hb : HBR (importH (instNumI hI)) x y) (h : L7 c y u) :
    L8 c hI x u := by
  obtain ⟨yq, ycs, ya⟩ := y
  obtain ⟨j, vs, xs, hlt, hu, hl, hq, ⟨cs₄, H₅, H₄⟩, ha⟩ := h
  have hq' : yq = (⟨c.exports[j].core, hlt⟩, .flat xs) := hq
  subst hq'
  obtain ⟨q, a, cs, cs', rfl, hy, H⟩ := hb
  cases hy
  exact ⟨j, vs, xs, hlt, hu, hl, rfl, ⟨ycs, cs₄, H, H₅, H₄⟩, ha⟩

omit hI in
theorem lowered_types' {j : Fin c.exports.length} {vs : List IVal} {xs : List Flat}
    (hl : checkLower c.exports[j].ty.params vs = some xs)
    (hlt : c.exports[j].core < (CoreModule.exports c.mod).length) :
    xs.map (·.type) = (c.mod.exports[c.exports[j].core]'hlt).2.params := by
  obtain ⟨nm, hcore⟩ := hc.core _ (List.getElem_mem j.isLt)
  obtain ⟨_, hget⟩ := List.getElem?_eq_some_iff.mp hcore
  obtain ⟨hck, rfl⟩ := checkLower_eq hl
  rw [show c.mod.exports[c.exports[j].core]'hlt = (nm, c.exports[j].ty.flat) from hget]
  exact lowerList_types _ _ hck

theorem l8_nonpure {x : CRound I.E (sigN (CoreModule.exports c.mod).length)}
    {u : CRound sigU sigU} (h : L8 c hI x u) (a : Option Payload) :
    exportH (instNumI hI) x.q ≠ .pure a := by
  obtain ⟨xq, xcs, xa⟩ := x
  obtain ⟨j, vs, xs, hlt, -, hl, hq, -⟩ := h
  have hq' : xq = (⟨c.exports[j].core, hlt⟩, .flat xs) := hq
  subst hq'
  show exportH (instNumI hI) (⟨c.exports[j].core, hlt⟩, Payload.flat xs) ≠ _
  rw [exportH_op hI hlt (opAtI hI hlt (lowered_types' hc hl hlt)) rfl rfl]
  intro h
  cases h

/-- The core import calls of an export call, through `core3Sem`'s import handler, the
`canon lower` wiring and the import mask, are related to the component import calls by
`ImpRel` (`imp_calls` in reverse). -/
theorem imp_calls_inv :
    ∀ (cs : List (Round I.E)) (cs₆ : List (Round (sigN (CoreModule.imports c.mod).length)))
      (cs₄ cs₂ : List (Round sigU)),
      HRounds (importH (instNumI hI)) cs cs₆ →
      HRounds (implsN c.imports.length (SimpleI.lowerArgs c.imports)
        (CoreModule.imports c.mod).length) cs₆ cs₄ →
      HRounds (maskH c.imports.length) cs₄ cs₂ →
      ∃ dss : List (List (Round (sigN c.imports.length))),
        List.Forall₂ (ImpRel c I) cs dss ∧ cs₂ = dss.flatten.map Round.forget
  | [], cs₆, cs₄, cs₂, H₁, H₂, H₃ => by
    cases H₁; cases H₂; cases H₃; exact ⟨[], .nil, rfl⟩
  | ⟨e, v⟩ :: cs, cs₆, cs₄, cs₂, H₁, H₂, H₃ => by
    rcases hrounds_cons_inv H₁ with ⟨hq, -⟩ | ⟨q₆, k₆, a₆, cs₆', rfl, hq, hk, H₁'⟩
    · cases hq
    cases hq
    have hv : payloadAnswer (I.imports.get e.1) a₆ = v := Prog.pure.inj hk
    have hlt₆ : e.1.val < (CoreModule.imports c.mod).length := by
      have hlen : I.imports.length = (CoreModule.imports c.mod).length := by
        rw [hI.2.1, List.length_map]
        rfl
      exact lt_of_lt_of_eq e.1.isLt hlen
    have hlt : e.1.val < c.imports.length := by
      have h₁ := hlt₆
      rw [show (CoreModule.imports c.mod) = c.mod.imports from rfl, hc.imports,
        List.length_map] at h₁
      exact h₁
    have hft : c.imports[e.1.val]? = some (c.imports[e.1.val].1, c.imports[e.1.val].2) :=
      List.getElem?_eq_getElem hlt
    cases hl : liftArgs c.imports[e.1.val].2.params (e.2.1.filterMap toFlat?) with
    | none =>
      have hn := implsN_lower_none (e := c.imports.length) hft hlt₆ hl
      rcases hrounds_cons_inv H₂ with ⟨hq₂, H₂'⟩ | ⟨q₄, k₄, a₄, cs₄', rfl, hq₂, hk₄, H₂'⟩
      · have ha₆ : none = a₆ := Prog.pure.inj (hn.symm.trans hq₂)
        obtain ⟨dss, hF, rfl⟩ := imp_calls_inv cs cs₆' cs₄ cs₂ H₁' H₂' H₃
        refine ⟨[] :: dss, .cons ⟨_, _, a₆, hft, hv, ?_⟩ hF, rfl⟩
        simp only [hl, and_true]
        exact ha₆.symm
      · exact absurd (hn.symm.trans hq₂) (by intro h; cases h)
    | some ws =>
      have hs := implsN_lower_some (e := c.imports.length) hft hlt₆ hlt hl
      rcases hrounds_cons_inv H₂ with ⟨hq₂, -⟩ | ⟨q₄, k₄, a₄, cs₄', rfl, hq₂, hk₄, H₂'⟩
      · exact absurd (hs.symm.trans hq₂) (by intro h; cases h)
      have hq₄ := hs.symm.trans hq₂
      cases hq₄
      have ha₆ : a₄.bind (Adapter.lower c.imports[e.1.val].2).up = a₆ := Prog.pure.inj hk₄
      rcases hrounds_cons_inv H₃ with ⟨hq₃, -⟩ | ⟨q₂, k₂, a₂, cs₂', rfl, hq₃, hk₂, H₃'⟩
      · rw [maskH_lt hlt] at hq₃
        cases hq₃
      rw [maskH_lt hlt] at hq₃
      cases hq₃
      have ha₄ : a₂ = a₄ := Prog.pure.inj hk₂
      obtain ⟨dss, hF, rfl⟩ := imp_calls_inv cs cs₆' cs₄' cs₂' H₁' H₂' H₃'
      refine ⟨[⟨(⟨e.1.val, hlt⟩, .vals ws), a₂⟩] :: dss, .cons ⟨_, _, a₆, hft, hv, ?_⟩ hF, rfl⟩
      simp only [hl]
      exact ⟨hlt, a₂, rfl, by rw [ha₄, ha₆]⟩

theorem rd_of {r : CRound I.E I.F} {x : CRound I.E (sigN (CoreModule.exports c.mod).length)}
    {u : CRound sigU sigU} (he : HCR (exportH (instNumI hI)) x r) (h : L8 c hI x u) :
    RdI c I r u := by
  obtain ⟨xq, xcs, xa⟩ := x
  obtain ⟨rq, rcs, ra⟩ := r
  obtain ⟨j, vs, xs, hlt, hu, hl, hq, ⟨cs₆, cs₄, H₆, H₅, H₄⟩, ha⟩ := h
  have hq' : xq = (⟨c.exports[j].core, hlt⟩, .flat xs) := hq
  subst hq'
  obtain ⟨k, hk, hcs, hka⟩ := he
  have hk' := (exportH_op hI hlt (opAtI hI hlt (lowered_types' hc hl hlt)) rfl rfl).symm.trans hk
  cases hk'
  have hcs' : rcs = xcs := hcs
  have hxa : answerPayload ra = xa := Prog.pure.inj hka
  subst hcs'
  obtain ⟨dss, hF, hcs₂⟩ := imp_calls_inv hc hI rcs cs₆ cs₄ u.cs H₆ H₅ H₄
  refine ⟨j, vs, xs, dss, hu, hl, rfl, rfl, hF, hcs₂, ?_⟩
  rw [ha, ← hxa]

end Core

/-! ## The read-back -/

/-- **The read-back of the importer's IR**: rounds with lower calls of
`c.toComp.denU (impSem P)` whose questions are typed export calls are, one by one, rounds of
the core instance from its store (`RdI`). -/
theorem imp_readback {P : Profile} {c : SimpleI} (hc : c.Good) {I : SInst}
    (hI : c.mod.IsInst I) {up : List (CRound sigU sigU)} (htop : ∀ u ∈ up, TopI c u)
    (h : cplay up ∈ c.toComp.denU (impSem P)) :
    ∃ ri : List (CRound I.E I.F), cplay ri ∈ I.strategy P I.store ∧
      List.Forall₂ (RdI c I) ri up := by
  rw [denU_toCompI] at h
  obtain ⟨l₃, H₃, h₃⟩ := hc_inv (oneShot_implsH _ _) h
  have G₃ : List.Forall₂ (L3 c) l₃ up :=
    (forall₂_and_right (forall₂_swap
      (hc_forall₂ H₃ fun u hu a => topI_nonpure hc (htop u hu) a)) htop).imp
      fun _ _ ⟨hr, ht⟩ => l3_of hc ht hr
  obtain ⟨u₄, H₄, h₄⟩ := hb_inv (oneShot_maskH _) h₃
  have G₄ : List.Forall₂ (L4 c) u₄ up :=
    (forall₂_comp (hb_forall₂ H₄) G₃).imp fun _ _ ⟨_, h₁, h₂⟩ => l4_of h₁ h₂
  obtain ⟨l₅, H₅, h₅⟩ := hc_inv (oneShot_splitH _) h₄
  have hge : ∀ r ∈ u₄, c.imports.length ≤ r.q.1 := fun r hr =>
    let ⟨_, h⟩ := forall₂_mem_left G₄ r hr
    l4_ge h
  rw [hc_splitH_inv H₅ hge] at h₅
  have h₅' := cplay_of_pair_inr h₅
  obtain ⟨u₆, H₆, h₆⟩ := hb_inv (oneShot_implsN _ _ _) h₅'
  have G₆ : List.Forall₂ (L6 c) u₆ up :=
    (forall₂_comp (forall₂_map_right (hb_forall₂ H₆)) G₄).imp
      fun _ _ ⟨_, h₁, h₂⟩ => l6_of h₁ h₂
  obtain ⟨l₇, H₇, h₇⟩ := hc_inv (oneShot_widenH _) h₆
  have G₇ : List.Forall₂ (L7 c) l₇ up :=
    (forall₂_comp (forall₂_swap (hc_forall₂ H₇ fun x hx a =>
      let ⟨_, h⟩ := forall₂_mem_left G₆ x hx
      l6_nonpure hc h a)) G₆).imp fun _ _ ⟨_, h₁, h₂⟩ => l7_of hc h₁ h₂
  rw [impSem_sem hI] at h₇
  obtain ⟨u₈, H₈, h₈⟩ := hb_inv (oneShot_importH _) h₇
  have G₈ : List.Forall₂ (L8 c hI) u₈ up :=
    (forall₂_comp (hb_forall₂ H₈) G₇).imp fun _ _ ⟨_, h₁, h₂⟩ => l8_of hI h₁ h₂
  obtain ⟨ri, H₉, h₉⟩ := hc_inv (oneShot_exportH _) h₈
  refine ⟨ri, h₉, ?_⟩
  exact (forall₂_comp (forall₂_swap (hc_forall₂ H₉ fun x hx a =>
      let ⟨_, h⟩ := forall₂_mem_left G₈ x hx
      l8_nonpure hc hI h a)) G₈).imp fun _ _ ⟨_, h₁, h₂⟩ => rd_of hc hI h₁ h₂

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq
