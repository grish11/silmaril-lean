module

public import Silmaril.Wasm.Component.Reference.LinkedG.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq.Linked

/-!
# Abstract exporters: generic lemmas, the simple instance and `Linked2`

* `uMoves_eq`: `uMoves` is `twos`;
* `noInl_denU`: the IR denotation of a component without imports makes no lower moves;
  `den_iff`: for such a component, complete rounds of `Comp.den` are complete rounds of
  `Comp.denU`, and conversely;
* `run_append`, `run_split`: sessions of an exporter, concatenated and split;
* `simple_adeq`: a simple component at its core instance meets `ExpSpec.Adeq` (#676's
  `sessRounds_rounds` forward, `specRoundsT_of_denU` and `sessRounds_of_specRoundsT` backward);
* `toG_toComp`, `toG_toRef`, `sessSpec_toG_iff`: `Linked2.toG` has the IR and reference
  components of `Linked2` and the same specification sessions.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedG

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

/-! ## Generic lemmas -/

theorem uMoves_eq : ∀ L : List URound, uMoves L = twos (E := sigU) (F := sigU) L
  | [] => rfl
  | ⟨_, _⟩ :: L => by
    rw [uMoves, uMoves_eq L]
    rfl

theorem noInl_denNodes {M : Type} [CoreModule M] (C : CoreSem M) :
    ∀ (e : Nat) (ns : List (Node M)) {X : Sig.{0}} (D : Strategy X sigU), (∀ t ∈ D, NoInl t) →
      ∀ t ∈ denNodes C e ns D, NoInl t
  | _, [], _, _, hD => by
    rw [denNodes]
    exact hD
  | e, n :: ns, _, D, hD => by
    rw [denNodes]
    exact noInl_denNodes C (e + n.width) ns _ (noInl_comp hD)

/-- **A component without imports makes no lower moves.** -/
theorem noInl_denU {M : Type} [CoreModule M] (C : CoreSem M) {c : Comp M}
    (hc : c.imports = []) : ∀ t ∈ c.denU C, NoInl t := by
  obtain ⟨I, ns, xs⟩ := c
  simp only [Comp.imports_mk] at hc
  subst hc
  rw [Comp.denU]
  exact noInl_comp (noInl_denNodes C _ ns _ (noInl_ofHandler_pure pure_maskH0))

/-- **Complete rounds of `Comp.den` and of `Comp.denU`**, for a component without imports. -/
theorem den_iff {M : Type} [CoreModule M] (C : CoreSem M) {c : Comp M} (hc : c.imports = [])
    (L : List (Round (sigN c.exports.length))) :
    twos L ∈ c.den C ↔ twos (L.map Round.forget) ∈ c.denU C := by
  refine ⟨fun h => ?_, den_rounds C c⟩
  unfold Comp.den atSizes at h
  obtain ⟨l₁, Hn, hl⟩ := hrounds_of_comp (oneShot_narrowH _)
    (fun s _ => noInl_sigN_nil (by rw [hc]; rfl) s) h
  rw [hrounds_narrowH_inv _ Hn] at hl
  exact twos_of_comp_noInl (noInl_denU C hc) hl

section Run

variable {e : ExpSpec} {P : Profile}

theorem run_append {s s₁ s₂ : e.St} {L L' : List URound} (h : e.Run P s L s₁)
    (h' : e.Run P s₁ L' s₂) : e.Run P s (L ++ L') s₂ := by
  induction h with
  | nil => exact h'
  | cons hs _ ih => exact .cons hs (ih h')

theorem run_split : ∀ {s s' : e.St} (L L' : List URound), e.Run P s (L ++ L') s' →
    ∃ s₁, e.Run P s L s₁ ∧ e.Run P s₁ L' s'
  | s, _, [], _, h => ⟨s, .nil s, h⟩
  | _, _, _ :: L, L', h => by
    rw [List.cons_append] at h
    cases h with
    | cons hs h' =>
      obtain ⟨s₁, h₁, h₂⟩ := run_split L L' h'
      exact ⟨s₁, .cons hs h₁, h₂⟩

end Run

/-! ## A simple component as an exporter -/

section Simple

variable {P : Profile} {c : Simple} {I : SInst}

theorem ofSimple_length (c : Simple) :
    (SimpleI.ofSimple c).toComp.exports.length = c.exports.length := by
  simp [SimpleI.ofSimple, SimpleI.toComp]

theorem ofSimple_ty (c : Simple) {w : Nat} (h₁ : w < (SimpleI.ofSimple c).toComp.exports.length)
    (h₂ : w < c.exports.length) :
    (SimpleI.ofSimple c).toComp.exports[w].ty = c.exports[w].ty := by
  simp [SimpleI.ofSimple, SimpleI.toComp]

/-- Sessions of `Simple.expSpec` are sessions of the specification (`SessRounds`). -/
theorem sessRounds_of_run {s s' : (Simple.expSpec c I).St} {L : List URound}
    (h : (Simple.expSpec c I).Run P s L s') : SessRounds P c I s L s' := by
  induction h with
  | nil s => exact .nil s
  | cons hs _ ih =>
    cases hs with
    | ret hj h => exact .ret hj h ih
    | trap hj h => exact .trap hj h ih

/-- Sessions of the specification on typed calls are sessions of `Simple.expSpec`. -/
theorem run_of_sessRounds :
    ∀ {s s' : Store Nat} {L : List URound}, SessRounds P c I s L s' →
      (∀ r ∈ L, (Simple.expSpec c I).Typed r) → (Simple.expSpec c I).Run P s L s'
  | _, _, _, .nil s, _ => ExpSpec.Run.nil (e := Simple.expSpec c I) s
  | _, _, _, .bad (j := j) (p := p) hj hn _, ht => by
    obtain ⟨w, ws, hq, hck⟩ := ht _ List.mem_cons_self
    simp only [Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl⟩ := hq
    have e := ofSimple_ty c w.isLt hj
    have hck' : ValTy.checkList c.exports[w.val].ty.params ws = true := by
      rw [← e]
      exact hck
    rw [hn hj ws rfl] at hck'
    cases hck'
  | _, _, _, .ret hj hret h, ht =>
    .cons (.ret hj hret) (run_of_sessRounds h fun r hr => ht r (List.mem_cons_of_mem _ hr))
  | _, _, _, .trap hj htrap h, ht =>
    .cons (.trap hj htrap) (run_of_sessRounds h fun r hr => ht r (List.mem_cons_of_mem _ hr))

/-- **A simple component meets the exporter interface.** -/
theorem simple_adeq (P : Profile) (hc : c.Good) (hI : c.mod.IsInst I) :
    (Simple.expSpec c I).Adeq P where
  imports := rfl
  fwd L s' h := by
    rw [uMoves_eq]
    obtain ⟨li, lc, hact, H, X⟩ :=
      sessRounds_rounds hc hI (sessRounds_of_run h) hI.1.choose_spec.ok
    have hinst : twos li ∈ I.strategy P I.store := by
      have h' := Silmaril.Wasm.Game.ScalarInstance.append_mem_of hact (I.strategy P s').nil_mem
      rwa [List.append_nil] at h'
    have hsem := sem_rounds hI H hinst
    have henv := envS_rounds (modSem P) c hsem
    show twos L ∈ (SimpleI.ofSimple c).toComp.denU (impSem P)
    rw [denU_ofSimple, denU_toComp]
    exact twos_comp_ofHandler X henv
  bwd L ht h := by
    rw [uMoves_eq] at h
    change twos L ∈ (SimpleI.ofSimple c).toComp.denU (impSem P) at h
    rw [denU_ofSimple] at h
    have hspec := specRoundsT_of_denU hc hI h
    obtain ⟨s', hS⟩ := sessRounds_of_specRoundsT hspec fun x hx => by
      obtain ⟨w, ws, hq, -⟩ := ht x hx
      rw [hq, ← ofSimple_length c]
      exact w.isLt
    exact ⟨s', run_of_sessRounds hS ht⟩

end Simple

/-! ## `Linked2` as an instance -/

section Linked2

variable {P : Profile} {l : Linked2} {Ie Ii : SInst}

theorem toG_toComp (l : Linked2) (Ie : SInst) : (l.toG Ie).toComp = l.toComp := by
  simp [LinkedG.toComp, linkComp, Linked2.toComp, ofSimple_length]

theorem toG_toRef (l : Linked2) (Ie : SInst) : (l.toG Ie).toRef = l.toRef := by
  have e : ∀ w, (l.toG Ie).expName w = l.expName w := by
    intro w
    simp [LinkedG.expName, Linked2.expName, SimpleI.ofSimple, SimpleI.toComp, List.getElem?_map]
    cases l.exp.exports[w]? <;> rfl
  simp only [LinkedG.toRef, Linked2.toRef, e]

theorem expRun_of_expRunT : ∀ {s s' : Store Nat}
    {ds : List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)},
    Linked2.ExpRunT P l Ie s ds s' → LinkedG.ExpRun P (l.toG Ie) s ds s'
  | _, _, _, .nil s => LinkedG.ExpRun.nil (g := l.toG Ie) s
  | _, _, _, .ret w hw hret h =>
    .step ⟨w.val, by simp [ofSimple_length]⟩ hw
      (.ret w.isLt hret) (expRun_of_expRunT h)
  | _, _, _, .trap w hw htrap h =>
    .step ⟨w.val, by simp [ofSimple_length]⟩ hw
      (.trap w.isLt htrap) (expRun_of_expRunT h)

theorem expRunT_of_expRun : ∀ {s s' : (l.toG Ie).exp.St}
    {ds : List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)},
    LinkedG.ExpRun P (l.toG Ie) s ds s' → Linked2.ExpRunT P l Ie s ds s'
  | _, _, _, .nil s => .nil s
  | _, _, _, .step w hw hs h => by
    cases hs with
    | ret hj hret => exact .ret ⟨w.val, hj⟩ hw hret (expRunT_of_expRun h)
    | trap hj htrap => exact .trap ⟨w.val, hj⟩ hw htrap (expRunT_of_expRun h)

/-- The session round of `Linked2` of a session round of `Linked2.toG`. -/
def SessRound.toL (d : LinkedG.SessRound (l.toG Ie) Ii) : Linked2.SessRound l Ii :=
  ⟨d.j, d.vs, d.f, d.cs, d.w, d.dss⟩

/-- The session round of `Linked2.toG` of a session round of `Linked2`. -/
def SessRound.ofL (Ie : SInst) (d : Linked2.SessRound l Ii) : LinkedG.SessRound (l.toG Ie) Ii :=
  ⟨d.j, d.vs, d.f, d.cs, d.w, d.dss⟩

theorem sessSpec_of_toG {u u' : Store Nat} {π π' : (l.toG Ie).exp.St}
    {calls : List (Fin l.imp.exports.length × List IVal)} {outs : List (Option (List IVal))}
    (h : (l.toG Ie).SessSpec P Ii u π calls outs u' π') :
    l.SessSpec P Ie Ii u π calls outs u' π' := by
  induction h with
  | nil u π => exact .nil u π
  | round d hok hp hr hans _ ih =>
    exact .round (SessRound.toL d) hok hp (expRunT_of_expRun hr) hans ih

theorem toG_of_sessSpec {u π u' π' : Store Nat}
    {calls : List (Fin l.imp.exports.length × List IVal)} {outs : List (Option (List IVal))}
    (h : l.SessSpec P Ie Ii u π calls outs u' π') :
    (l.toG Ie).SessSpec P Ii u π calls outs u' π' := by
  induction h with
  | nil u π => exact LinkedG.SessSpec.nil (g := l.toG Ie) u π
  | round d hok hp hr hans _ ih =>
    exact .round (SessRound.ofL Ie d) hok hp (expRun_of_expRunT hr) hans ih

end Linked2

end Silmaril.Proofs.Wasm.Component.Reference.LinkedG
