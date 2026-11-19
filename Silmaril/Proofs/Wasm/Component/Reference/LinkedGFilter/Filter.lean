module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionEquiv.Filter
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGSession.Main

/-!
# Ill-typed calls of a linked component with an abstract exporter

`LinkedSessionEquiv.Filter` for `LinkedG`: the linked export handler forwards every question to
the importer's node, whose export handler answers an ill-typed question by a trap at once without
lower calls (`nodeI_inv`, `nodeI_of`, generic in the importer and in what answers its imports).
The exporter only appears through its environment of lower calls, so it stays abstract (no
`ExpSpec.Adeq` is used):

* `den_topU`, `den_of_topU`: complete in-range rounds of `g.toComp.denU` are the rounds `cl` of
  the importer's node whose lower calls, all together and in order, are complete rounds of the
  exporter's environment;
* `den_invU`, `den_ofU`: in complete in-range rounds of `g.toComp.denU`, the ill-typed rounds
  answer a trap, the typed ones a trap or values, and removing or inserting the ill-typed rounds
  keeps a play;
* `typedI_iff`: the importer's typed questions are `ExpSpec.TypedQ` of `g.toExp Ii`;
* the header forms `linkedG_den_shape`, `linkedG_den_filter_iff`, `linkedG_den_answers`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGFilter

open Classical
open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionEquiv
open Silmaril.Proofs.Wasm.Component.Reference.LinkedG
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

variable {P : Profile} {g : LinkedG}

/-! ## The top layers -/

theorem hrounds_exportsG_shift (g : LinkedG) :
    ∀ M : List URound, (∀ m ∈ M, m.1.1 < g.imp.exports.length) →
      HRounds (exportsH (g.exp.comp.exports.length + g.imp.exports.length) g.toComp.exports)
        M (M.map (shiftG g))
  | [], _ => .nil
  | ⟨(j, p), R⟩ :: M, hlt => by
    have hj : j < g.imp.exports.length := hlt _ List.mem_cons_self
    show HRounds _ (⟨(j, p), R⟩ :: M) (⟨(g.exp.comp.exports.length + j, p), R⟩ :: M.map (shiftG g))
    exact .call (q := (j, p)) (q' := (g.exp.comp.exports.length + j, p))
      (k := fun n => .pure n) (exportsH_toCompG g hj p) rfl
      (hrounds_exportsG_shift g M fun m hm => hlt m (List.mem_cons_of_mem _ hm))

theorem map_downBy {n : Nat} : ∀ (cl : List (CRound sigU sigU)) (M : List URound),
    cl.map CRound.toRound = M.map (fun m => (⟨(n + m.1.1, m.1.2), m.2⟩ : Round sigU)) →
    (cl.map (downBy n)).map CRound.toRound = M
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | ⟨(q₁, q₂), cs, a⟩ :: cl, ⟨(j, p), b⟩ :: M, h => by
    simp only [List.map_cons, List.cons.injEq] at h ⊢
    refine ⟨?_, map_downBy cl M h.2⟩
    have h₁ := h.1
    simp only [CRound.toRound, Sigma.mk.injEq, Prod.mk.injEq] at h₁
    obtain ⟨⟨rfl, rfl⟩, ha⟩ := h₁
    cases ha
    simp [CRound.toRound, downBy]

/-- **The top layers read back**: complete in-range rounds of the linked denotation are rounds
of the importer's node whose lower calls, all together and in order, are complete rounds of the
exporter's environment. -/
theorem den_topU {M : List URound} (hlt : ∀ m ∈ M, m.1.1 < g.imp.exports.length)
    (h : twos M ∈ g.toComp.denU (impSem P)) :
    ∃ cl : List (CRound sigU sigU), cplay cl ∈ impNodeG (impSem P) g ∧
      twos (cl.flatMap (·.cs)) ∈ ext 0 (Strategy.ofHandler (maskH 0)) (expNodeG (impSem P) g) ∧
      cl.map CRound.toRound = M := by
  have hEnv : ∀ t ∈ envG (impSem P) g, NoInl t :=
    noInl_comp (noInl_comp (noInl_ofHandler_pure pure_maskH0))
  rw [denU_toCompG] at h
  obtain ⟨l₂, H₂, hl₂⟩ := hrounds_of_comp (oneShot_implsH _ _) hEnv h
  rw [hrounds_exportsG_inv g M l₂ hlt H₂] at hl₂
  have hσ : ∀ s ∈ ext 0 (Strategy.ofHandler (maskH 0)) (expNodeG (impSem P) g), NoInl s :=
    noInl_comp (noInl_ofHandler_pure pure_maskH0)
  obtain ⟨cl, hcl, hA, hmap⟩ := serve_inv hσ hl₂
  obtain ⟨low₁, H₁, hlow₁⟩ := hc_inv (oneShot_splitH _) hcl
  have hge : ∀ r ∈ cl, g.exp.comp.exports.length ≤ r.q.1 := by
    intro r hr
    have hm : CRound.toRound r ∈ M.map (shiftG g) := hmap ▸ List.mem_map_of_mem hr
    obtain ⟨x, -, hx⟩ := List.mem_map.mp hm
    have hq : r.q = (shiftG g x).1 := (congrArg Sigma.fst hx).symm
    rw [hq]
    exact Nat.le_add_right _ _
  rw [hc_splitH_inv H₁ hge] at hlow₁
  have hN := cplay_of_pair_inr hlow₁
  refine ⟨cl.map (downBy g.exp.comp.exports.length), hN, ?_, map_downBy cl M hmap⟩
  rw [List.flatMap_map]
  exact hA

/-- **The top layers built**: the converse of `den_topU`. -/
theorem den_of_topU {M : List URound} {cl : List (CRound sigU sigU)}
    (hlt : ∀ m ∈ M, m.1.1 < g.imp.exports.length)
    (hN : cplay cl ∈ impNodeG (impSem P) g)
    (hA : twos (cl.flatMap (·.cs)) ∈ ext 0 (Strategy.ofHandler (maskH 0)) (expNodeG (impSem P) g))
    (hm : cl.map CRound.toRound = M) : twos M ∈ g.toComp.denU (impSem P) := by
  have hP : cplay (cl.map (CRound.inr (F₁ := sigU))) ∈
      (Strategy.id sigU).pair (impNodeG (impSem P) g) := cplay_pair_inr hN
  let upR : CRound sigU sigU → CRound sigU sigU :=
    fun r => ⟨(g.exp.comp.exports.length + r.q.1, r.q.2), r.cs, r.a⟩
  have hS : cplay (cl.map upR) ∈ ((Strategy.id sigU).pair (impNodeG (impSem P) g)).comp
      (Strategy.ofHandler (splitH g.exp.comp.exports.length)) :=
    cplay_comp_ofHandler (HC.of_map upR (CRound.inr (F₁ := sigU)) cl fun _ _ =>
      .call (h := splitH _) (splitH_shift' _ _ _) rfl .nil) hP
  have hE : cplay ((cl.map upR).map (CRound.hide (E := sigU))) ∈ envG (impSem P) g := by
    refine cplay_comp_serve ?_ hS
    rw [List.flatMap_map]
    exact hA
  rw [LinkedSessionEquiv.cplay_hide] at hE
  have e : (cl.map upR).map CRound.toRound = M.map (shiftG g) := by
    rw [← hm, List.map_map, List.map_map]
    rfl
  rw [e] at hE
  rw [denU_toCompG]
  exact twos_comp_ofHandler (hrounds_exportsG_shift g M hlt) hE

/-! ## Ill-typed rounds -/

section Den

variable (t : Nat × Payload → Bool)

/-- **Ill-typed rounds read back**: in complete in-range rounds of the linked denotation, an
ill-typed question is answered by a trap, a typed one by a trap or values, and the typed rounds
alone are a play. -/
theorem den_invU (hi : g.imp.Good) (ht : ∀ q, t q = true ↔ TypedI g.imp q) {M : List URound}
    (hlt : ∀ m ∈ M, m.1.1 < g.imp.exports.length) (h : twos M ∈ g.toComp.denU (impSem P)) :
    (∀ x ∈ M, t x.1 = false → x.2 = none) ∧
    (∀ x ∈ M, t x.1 = true → x.2 = none ∨ ∃ ws, x.2 = some (.vals ws)) ∧
    twos (M.filter fun x => t x.1) ∈ g.toComp.denU (impSem P) := by
  obtain ⟨cl, hN, hA, hm⟩ := den_topU hlt h
  obtain ⟨hbad, hgood, hF⟩ := nodeI_inv hi t ht hN
  have mem : ∀ x ∈ M, ∃ r ∈ cl, r.q = x.1 ∧ r.a = x.2 := by
    intro x hx
    rw [← hm] at hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    exact ⟨r, hr, rfl, rfl⟩
  refine ⟨fun x hx hb => ?_, fun x hx hg => ?_, ?_⟩
  · obtain ⟨r, hr, hq, ha⟩ := mem x hx
    rw [← ha]
    exact (hbad r hr (by rw [hq]; exact hb)).2
  · obtain ⟨r, hr, hq, ha⟩ := mem x hx
    rw [← ha]
    exact hgood r hr (by rw [hq]; exact hg)
  · refine den_of_topU (fun m hm' => hlt m (List.mem_filter.mp hm').1) hF ?_ ?_
    · rw [flatMap_filter_nil cl fun r hr hb => (hbad r hr hb).1]
      exact hA
    · rw [← hm, List.filter_map]
      rfl

/-- **Ill-typed rounds inserted**: answered by a trap, into a play of the typed rounds. -/
theorem den_ofU (hi : g.imp.Good) (ht : ∀ q, t q = true ↔ TypedI g.imp q) {M : List URound}
    (hlt : ∀ m ∈ M, m.1.1 < g.imp.exports.length)
    (hbad : ∀ x ∈ M, t x.1 = false → x.2 = none)
    (h : twos (M.filter fun x => t x.1) ∈ g.toComp.denU (impSem P)) :
    twos M ∈ g.toComp.denU (impSem P) := by
  obtain ⟨cl', hN, hA, hm⟩ := den_topU (fun m hm' => hlt m (List.mem_filter.mp hm').1) h
  obtain ⟨cl, F', e, hmem⟩ := forall₂_unfilter (R := fun c x => CRound.toRound c = x)
    (p := fun r : CRound sigU sigU => t r.q) (p' := fun x : Round sigU => t x.1)
    (fun x => ⟨x.1, [], x.2⟩) (fun c x hcx => by subst hcx; rfl) M cl'
    (fun _ _ _ => rfl) (forall₂_of_map_eq' hm)
  have hcl : cl.map CRound.toRound = M := forall₂_map_eq F'
  have hbad' : ∀ r ∈ cl, t r.q = false → r.cs = [] ∧ r.a = none := by
    intro r hr hb
    obtain ⟨x, hx, rfl⟩ := hmem r hr hb
    exact ⟨rfl, hbad x hx hb⟩
  have hN' := nodeI_of hi t ht hbad' (by rw [e]; exact hN)
  refine den_of_topU hlt hN' ?_ hcl
  rw [← flatMap_filter_nil cl fun r hr hb => (hbad' r hr hb).1, e]
  exact hA

end Den

/-! ## Typed questions -/

theorem typedI_iff (Ii : SInst) (q : Nat × Payload) :
    TypedI g.imp q ↔ (g.toExp Ii).TypedQ q := by
  constructor
  · rintro ⟨j, vs, rfl, hck⟩
    exact LinkedGSession.typedQ_of_check hck
  · exact LinkedGSession.typedQ_imp

theorem decide_iff (Ii : SInst) (q : Nat × Payload) :
    decide ((g.toExp Ii).TypedQ q) = true ↔ TypedI g.imp q := by
  rw [decide_eq_true_iff, typedI_iff Ii]

theorem forget_lt (L : List (Round (sigN g.toComp.exports.length))) :
    ∀ m ∈ L.map Round.forget, m.1.1 < g.imp.exports.length := by
  intro m hm
  obtain ⟨y, -, rfl⟩ := List.mem_map.mp hm
  rw [← LinkedG.exports_length_toComp]
  exact y.1.1.isLt

/-- **Ill-typed calls of `g.toExp Ii`, at the untyped interface**: complete in-range rounds are a
play of `g.toComp.denU` exactly when the ill-typed ones answer a trap and the typed ones alone are
a play. -/
theorem filterU_iff (hi : g.imp.Good) (Ii : SInst) {M : List URound}
    (hlt : ∀ m ∈ M, m.1.1 < g.imp.exports.length) :
    twos M ∈ g.toComp.denU (impSem P) ↔
      (∀ x ∈ M, ¬ (g.toExp Ii).TypedQ x.1 → x.2 = none) ∧
      twos (M.filter fun x => decide ((g.toExp Ii).TypedQ x.1)) ∈ g.toComp.denU (impSem P) := by
  constructor
  · intro h
    obtain ⟨hbad, -, hF⟩ := den_invU _ hi (decide_iff Ii) hlt h
    exact ⟨fun x hx hn => hbad x hx (decide_eq_false hn), hF⟩
  · rintro ⟨hbad, hF⟩
    exact den_ofU _ hi (decide_iff Ii) hlt
      (fun x hx hb => hbad x hx (of_decide_eq_false hb)) hF

/-! ## The header forms -/

theorem den_iffG (L : List (Round (sigN g.toComp.exports.length))) :
    exportRounds L ∈ g.toComp.den (impSem P) ↔
      twos (L.map Round.forget) ∈ g.toComp.denU (impSem P) := by
  rw [exportRounds_eq]
  exact den_iff (impSem P) (c := g.toComp) rfl L

theorem linkedG_den_shape (P : Profile) (g : LinkedG)
    {p : List (Move (sigN 0) (sigN g.toComp.exports.length))} (hp : p ∈ g.toComp.den (impSem P)) :
    (∃ L, p = exportRounds L) ∨ ∃ L q, p = exportRounds L ++ [.inr (.ask q)] := by
  rcases shape_of_legal ((g.toComp.den (impSem P)).legal hp) (noInl_sigN_nil rfl p) with
    ⟨L, rfl⟩ | ⟨q, L, rfl⟩
  · exact .inl ⟨L, (exportRounds_eq L).symm⟩
  · exact .inr ⟨L, q, (congrArg (· ++ [Sum.inr (Ev.ask q)]) (exportRounds_eq L)).symm⟩

theorem linkedG_den_filter_iff (P : Profile) (hi : g.imp.Good) (Ii : SInst)
    (L : List (Σ q : (sigN g.toComp.exports.length).Op, (sigN g.toComp.exports.length).Ar q)) :
    exportRounds L ∈ g.toComp.den (impSem P) ↔
      (∀ x ∈ L, ¬ (g.toExp Ii).TypedQ (x.1.1.val, x.1.2) → x.2 = none) ∧
      exportRounds (L.filter fun x => decide ((g.toExp Ii).TypedQ (x.1.1.val, x.1.2))) ∈
        g.toComp.den (impSem P) := by
  have e : (L.filter fun x => decide ((g.toExp Ii).TypedQ (x.1.1.val, x.1.2))).map
      Round.forget = (L.map Round.forget).filter fun x => decide ((g.toExp Ii).TypedQ x.1) := by
    rw [List.filter_map]
    rfl
  rw [den_iffG, den_iffG, e,
    filterU_iff hi Ii (forget_lt L), List.forall_mem_map]
  rfl

theorem linkedG_den_answers (P : Profile) (hi : g.imp.Good) (Ii : SInst)
    {L : List (Σ q : (sigN g.toComp.exports.length).Op, (sigN g.toComp.exports.length).Ar q)}
    (h : exportRounds L ∈ g.toComp.den (impSem P)) :
    ∀ x ∈ L, (g.toExp Ii).TypedQ (x.1.1.val, x.1.2) →
      x.2 = none ∨ ∃ ws, x.2 = some (.vals ws) := by
  rw [den_iffG] at h
  obtain ⟨-, hgood, -⟩ := den_invU _ hi (decide_iff Ii) (forget_lt L) h
  exact fun x hx hq => hgood (Round.forget x) (List.mem_map_of_mem hx) (decide_eq_true hq)

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGFilter
