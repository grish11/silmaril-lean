module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.Coherent
public import Silmaril.Wasm.Game.Determinism.Thms

/-!
# The importer's read-backs cohere, at deterministic profiles

The read-back of a waiting play of the importer's IR (`imp_wait_readback`) gives a play of the
importer's core instance: core rounds `ri` related to the IR rounds (`RdI`), then the pending core
question `f` after core import calls `ics` related to component import calls `dss` (`ImpRel`),
waiting on a core import call that lifts. At `profile o` these core plays are determined by the
component data, so the read-backs of longer and longer prefixes of one play extend one another:

* `impRel_det`: two core import calls on the same question, related by `ImpRel` to component
  calls with the same answers, have the same core answer and the same component calls (a call
  whose arguments do not lift is answered by a trap without a component call);
* `calls_prefix`: from one hidden state, two runs of answered core import calls, followed by a
  move that, if it is a core import call, lifts: if the component calls of the first are a prefix
  of those of the second (after the wiring, `wireRound`), the first core calls are a prefix of
  the second (Proponent's moves are unique, `Trans.player_unique`; the states follow,
  `Trans.functional`);
* `rounds_eq`: two runs of complete core rounds read back from the same IR rounds above the
  importer's node (`RdI`, then `HBR` for its wiring) are equal;
* `pend_prefix`: two waiting core plays with the same complete rounds and the same pending
  question extend one another in their calls;
* `exists_limit`, `streamTake_eq_take`: a pairwise comparable unbounded family of lists has a
  limit stream.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq

open Silmaril.Games
open Silmaril.Games.Abstract (streamTake)
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile toFlat?)

local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

/-- The core import call `e` of the importer has arguments that lift at the import's type. -/
def Lifts (l : Linked2) (I : SInst) (e : I.E.Op) : Prop :=
  ∃ (nm : String) (ft : FuncTy) (ws : List Silmaril.Wasm.Component.Val),
    l.imp.imports[e.1.val]? = some (nm, ft) ∧ liftArgs ft.params (e.2.1.filterMap toFlat?) = some ws

/-- A core question is its export index and its arguments. -/
theorem fop_ext {I : SInst} {f f' : I.F.Op} (h₁ : f.1.val = f'.1.val) (h₂ : f.2.1 = f'.2.1) :
    f = f' := by
  obtain ⟨⟨i, hi⟩, ⟨a, ha⟩⟩ := f
  obtain ⟨⟨i', hi'⟩, ⟨a', ha'⟩⟩ := f'
  dsimp only at h₁ h₂
  subst h₁ h₂
  rfl

/-- **`ImpRel` is functional in the answers**: on the same core question, component calls whose
wired answers agree give the same core answer and the same component calls. -/
theorem impRel_det {l : Linked2} {I : SInst} {m : I.E.Op} {n n' : I.E.Ar m}
    {ds ds' X X' : List (Round (sigN l.imp.imports.length))}
    (h : ImpRel l.imp I ⟨m, n⟩ ds) (h' : ImpRel l.imp I ⟨m, n'⟩ ds')
    (hp : (ds ++ X).map (wireRound l) <+: (ds' ++ X').map (wireRound l)) : n = n' ∧ ds = ds' := by
  obtain ⟨nm, ft, A, hft, hA, hm⟩ := h
  obtain ⟨nm', ft', A', hft', hA', hm'⟩ := h'
  rw [hft] at hft'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hft')
  dsimp only at hm hm' hA hA'
  revert hm hm'
  cases liftArgs ft.params (m.2.1.filterMap toFlat?) with
  | none =>
    rintro ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    exact ⟨hA.symm.trans hA', rfl⟩
  | some ws =>
    rintro ⟨hk, R, rfl, rfl⟩ ⟨hk', R', rfl, rfl⟩
    simp only [List.cons_append, List.map_cons, List.cons_prefix_cons] at hp
    have hR : R = R' := by
      have h₁ := hp.1
      simp only [wireRound, Sigma.mk.injEq, heq_eq_eq, true_and] at h₁
      exact h₁
    subst hR
    exact ⟨hA.symm.trans hA', rfl⟩

theorem impRel_nil_not_lifts {l : Linked2} {I : SInst} {x : Σ e : I.E.Op, I.E.Ar e}
    (h : ImpRel l.imp I x []) : ¬ Lifts l I x.1 := by
  rintro ⟨nm', ft', ws', hft', hl'⟩
  obtain ⟨nm, ft, A, hft, -, hm⟩ := h
  rw [hft] at hft'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hft')
  simp [hl'] at hm

/-- **Two runs of answered core import calls from one state**: if the wired component calls of
the first are a prefix of those of the second, and the move after the second run, if a core
import call, lifts, the first core calls are a prefix of the second. -/
theorem calls_prefix {o : GrowOracle} {l : Linked2} {I : SInst} :
    ∀ {cs cs' : List (Σ e : I.E.Op, I.E.Ar e)}
      {dss dss' : List (List (Round (sigN l.imp.imports.length)))} {q z z' : I.HState}
      {y y' : Move I.E I.F} {Y Y' : List (Move I.E I.F)},
      I.Path (profile o) q (callMoves cs ++ y :: Y) z →
      I.Path (profile o) q (callMoves cs' ++ y' :: Y') z' →
      (∀ e, y' = .inl (.ask e) → Lifts l I e) →
      List.Forall₂ (ImpRel l.imp I) cs dss → List.Forall₂ (ImpRel l.imp I) cs' dss' →
      dss.flatten.map (wireRound l) <+: dss'.flatten.map (wireRound l) →
      cs <+: cs' ∧ dss <+: dss'
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, F, _, _ => by
    cases F
    exact ⟨List.nil_prefix, List.nil_prefix⟩
  | ⟨m, n⟩ :: cs, [], _, _, _, _, _, _, _, _, _, hp, hp', hy', F, F', hd => by
    cases F' with
    | nil =>
      cases F with
      | cons hc F₁ =>
        exfalso
        rename_i ds dsr
        cases hp with
        | cons t₁ _ =>
          cases hp' with
          | cons t₁' _ =>
            have e := Silmaril.Wasm.Game.ScalarInstance.Trans.player_unique t₁ t₁'
              (by simp [Move.IsP])
            have hL := hy' m e.symm
            have hds : ds = [] := by
              simp only [List.flatten_cons, List.flatten_nil, List.map_nil,
                List.prefix_nil, List.map_eq_nil_iff, List.append_eq_nil_iff] at hd
              exact hd.1
            subst hds
            exact impRel_nil_not_lifts hc hL
  | ⟨m, n⟩ :: cs, ⟨m', n'⟩ :: cs', _, _, _, _, _, _, _, _, _, hp, hp', hy', F, F', hd => by
    cases F with
    | cons hc F₁ =>
      cases F' with
      | cons hc' F₁' =>
        rename_i ds dsr ds' dsr'
        cases hp with
        | cons t₁ hp₁ =>
          cases hp' with
          | cons t₁' hp₁' =>
            have e := Silmaril.Wasm.Game.ScalarInstance.Trans.player_unique t₁ t₁'
              (by simp [Move.IsP])
            simp only [Sum.inl.injEq, Ev.ask.injEq] at e
            subst e
            obtain rfl := Silmaril.Wasm.Game.ScalarInstance.Trans.functional t₁ t₁'
            simp only [List.flatten_cons, List.map_append] at hd
            obtain ⟨rfl, rfl⟩ := impRel_det hc hc' (by simpa only [List.map_append] using hd)
            cases hp₁ with
            | cons t₂ hp₂ =>
              cases hp₁' with
              | cons t₂' hp₂' =>
                obtain rfl := Silmaril.Wasm.Game.ScalarInstance.Trans.functional t₂ t₂'
                obtain ⟨h₁, h₂⟩ := calls_prefix hp₂ hp₂' hy' F₁ F₁'
                  ((List.prefix_append_right_inj _).mp hd)
                exact ⟨List.cons_prefix_cons.mpr ⟨rfl, h₁⟩, List.cons_prefix_cons.mpr ⟨rfl, h₂⟩⟩

/-- The relation of a core round of the importer to a round of the importer's node: read back
(`RdI`) to an IR round served by the node's wiring (`HBR`). -/
def RdN (l : Linked2) (I : SInst) (r : CRound I.E I.F) (c : CRound sigU sigU) : Prop :=
  ∃ x, RdI l.imp I r x ∧
    HBR (implsH l.exp.exports.length (wireArgs l)) x (downBy l.exp.exports.length c)

theorem prefix_antisymm {α : Type} {a b : List α} (h₁ : a <+: b) (h₂ : b <+: a) : a = b :=
  h₁.eq_of_length (le_antisymm h₁.length_le h₂.length_le)

/-- **Complete core rounds read back from the same node rounds are equal** (deterministic
profiles, under `WireTy`). -/
theorem rounds_eq {o : GrowOracle} {l : Linked2} (hw : l.WireTy) {I : SInst} :
    ∀ {cl : List (CRound sigU sigU)} {ri ri' : List (CRound I.E I.F)} {s : Store Nat}
      {z z' : I.HState},
      List.Forall₂ (RdN l I) ri cl → List.Forall₂ (RdN l I) ri' cl →
      I.Path (profile o) (.idle s) (cplay ri) z → I.Path (profile o) (.idle s) (cplay ri') z' →
      ri = ri'
  | [], _, _, _, _, _, .nil, .nil, _, _ => rfl
  | c :: cl, ⟨rq, rcs, ra⟩ :: ri, ⟨rq', rcs', ra'⟩ :: ri', s, z, z', .cons hr F, .cons hr' F',
      hp, hp' => by
    obtain ⟨x, ⟨j, vs, xs, dss, hxq, hxs, hq₁, hq₂, hF, hxcs, -⟩, q, a, cs, csc, rfl, hd, H⟩ := hr
    obtain ⟨x', ⟨j', vs', xs', dss', hxq', hxs', hq₁', hq₂', hF', hxcs', -⟩, q', a', cs', csc',
      rfl, hd', H'⟩ := hr'
    rw [hd] at hd'
    simp only [CRound.mk.injEq] at hd'
    obtain ⟨rfl, hcsc, -⟩ := hd'
    subst hcsc
    dsimp only at hxq hxq' hxcs hxcs' hq₁ hq₂ hq₁' hq₂'
    rw [hxq] at hxq'
    simp only [Prod.mk.injEq, Payload.vals.injEq] at hxq'
    obtain ⟨hjj, rfl⟩ := hxq'
    obtain rfl : j = j' := Fin.ext hjj
    rw [hxs] at hxs'
    obtain rfl := Option.some.inj hxs'
    obtain rfl : rq = rq' := fop_ext (hq₁.trans hq₁'.symm) (hq₂.trans hq₂'.symm)
    -- the wired answers of the two rounds agree
    subst hxcs hxcs'
    have hw₁ := hrounds_wire_inv hw dss.flatten csc H
    have hw₂ := hrounds_wire_inv hw dss'.flatten csc H'
    have hdd : dss.flatten.map (wireRound l) = dss'.flatten.map (wireRound l) :=
      hw₁.symm.trans hw₂
    -- the instance's paths
    cases hp with
    | cons t₁ hp₁ =>
      cases hp' with
      | cons t₁' hp₁' =>
        obtain rfl := Silmaril.Wasm.Game.ScalarInstance.Trans.functional t₁ t₁'
        have hy : ∀ e, (.inr (.ans rq ra) : Move I.E I.F) = .inl (.ask e) → Lifts l I e :=
          fun _ h => nomatch h
        have hy' : ∀ e, (.inr (.ans rq ra') : Move I.E I.F) = .inl (.ask e) → Lifts l I e :=
          fun _ h => nomatch h
        have p₁ := calls_prefix hp₁ hp₁' hy' hF hF' ⟨[], by rw [List.append_nil]; exact hdd⟩
        have p₂ := calls_prefix hp₁' hp₁ hy hF' hF ⟨[], by rw [List.append_nil]; exact hdd.symm⟩
        obtain rfl := prefix_antisymm p₁.1 p₂.1
        obtain ⟨q₂, hc₂, hr₂⟩ := path_split_inst hp₁
        obtain ⟨q₂', hc₂', hr₂'⟩ := path_split_inst hp₁'
        obtain rfl := Silmaril.Wasm.Game.ScalarInstance.Path.functional hc₂ hc₂'
        cases hr₂ with
        | cons t₃ hp₃ =>
          cases hr₂' with
          | cons t₃' hp₃' =>
            have e := Silmaril.Wasm.Game.ScalarInstance.Trans.player_unique t₃ t₃'
              (by simp [Move.IsP])
            simp only [Sum.inr.injEq, Ev.ans.injEq, heq_eq_eq, true_and] at e
            subst e
            obtain rfl := Silmaril.Wasm.Game.ScalarInstance.Trans.functional t₃ t₃'
            cases t₃ with
            | oret _ _ _ =>
              rw [rounds_eq hw F F' hp₃ hp₃']

/-- **Two waiting core plays with the same complete rounds and pending question** (deterministic
profiles): if the wired component calls of the first are a prefix of those of the second, and
the second's pending call lifts, the first's core calls are a prefix of the second's. -/
theorem pend_prefix {o : GrowOracle} {l : Linked2} {I : SInst} {s : Store Nat}
    {ri : List (CRound I.E I.F)} {f : I.F.Op} {ics ics' : List (Σ e : I.E.Op, I.E.Ar e)}
    {dss dss' : List (List (Round (sigN l.imp.imports.length)))} {e e' : I.E.Op}
    {z z' : I.HState}
    (hp : I.Path (profile o) (.idle s) (rplay ri f ics ++ [.inl (.ask e)]) z)
    (hp' : I.Path (profile o) (.idle s) (rplay ri f ics' ++ [.inl (.ask e')]) z')
    (hl : Lifts l I e') (hF : List.Forall₂ (ImpRel l.imp I) ics dss)
    (hF' : List.Forall₂ (ImpRel l.imp I) ics' dss')
    (hd : dss.flatten.map (wireRound l) <+: dss'.flatten.map (wireRound l)) :
    ics <+: ics' ∧ dss <+: dss' := by
  simp only [rplay, List.append_assoc, List.cons_append] at hp hp'
  obtain ⟨q₁, h₁, h₂⟩ := path_split_inst hp
  obtain ⟨q₁', h₁', h₂'⟩ := path_split_inst hp'
  obtain rfl := Silmaril.Wasm.Game.ScalarInstance.Path.functional h₁ h₁'
  cases h₂ with
  | cons t hp₂ =>
    cases h₂' with
    | cons t' hp₂' =>
      obtain rfl := Silmaril.Wasm.Game.ScalarInstance.Trans.functional t t'
      exact calls_prefix hp₂ hp₂' (fun x hx => by cases hx; exact hl) hF hF' hd

/-! ## Limits -/

/-- **A pairwise comparable unbounded family of lists has a limit stream.** -/
theorem exists_limit {α : Type} (Z : ℕ → List α) (hcomp : ∀ a b, Z a <+: Z b ∨ Z b <+: Z a)
    (hunb : ∀ k, ∃ n, k < (Z n).length) :
    ∃ ζ : ℕ → α, ∀ n k (hk : k < (Z n).length), (Z n)[k] = ζ k := by
  choose N hN using hunb
  refine ⟨fun k => (Z (N k))[k]'(hN k), fun n k hk => ?_⟩
  rcases hcomp n (N k) with h | h
  · exact h.getElem hk
  · exact (h.getElem (hN k)).symm

/-- A growing family is pairwise comparable. -/
theorem comparable_of_mono {α : Type} {Z : ℕ → List α} (hmono : ∀ n n', n ≤ n' → Z n <+: Z n')
    (a b : ℕ) : Z a <+: Z b ∨ Z b <+: Z a :=
  (le_total a b).elim (fun h => .inl (hmono a b h)) fun h => .inr (hmono b a h)

theorem streamTake_eq_take {α : Type} {ζ : ℕ → α} {Z : List α}
    (h : ∀ k (hk : k < Z.length), Z[k] = ζ k) {m : ℕ} (hm : m ≤ Z.length) :
    streamTake ζ m = Z.take m := by
  apply List.ext_getElem
  · simp [streamTake, hm]
  · intro k h₁ h₂
    simp only [streamTake, List.getElem_ofFn, List.getElem_take]
    exact (h k (by simp [streamTake] at h₁; omega)).symm

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq
