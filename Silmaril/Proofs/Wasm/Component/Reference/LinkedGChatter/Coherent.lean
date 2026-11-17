module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGChatter.Det
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.Chatter

/-!
# The read-backs cohere, for an abstract exporter at deterministic profiles

`LinkedSessionDAdeq.ImpCoherent` and `Coherent` with the exporter abstracted:

* the importer's side (`impRel_detW`, `calls_prefixG`, `rounds_eqG`, `pend_prefixG`): the core
  plays read back from longer and longer prefixes of one IR play extend one another (the
  importer's Proponent moves are unique, `Trans.player_unique`); the wiring is `wireRoundG`;
* the exporter's side (`exp_plays_streamG`): served typed rounds after a prefix, any number of
  chunks of them, played by the exporter's environment, are served along one run of its
  specification, by `ExpSpec.AdeqIC` (in place of `exp_plays_stream`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGChatter

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Games.Abstract (streamTake)
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq
open Silmaril.Proofs.Wasm.Component.Reference.LinkedG
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile toFlat?)

local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

/-! ## The importer's side -/

section Imp

variable {g : LinkedG}

/-- The core import call `e` of the importer `c` has arguments that lift at the import's type. -/
def LiftsI (c : SimpleI) (I : SInst) (e : I.E.Op) : Prop :=
  ∃ (nm : String) (ft : FuncTy) (ws : List Silmaril.Wasm.Component.Val),
    c.imports[e.1.val]? = some (nm, ft) ∧ liftArgs ft.params (e.2.1.filterMap toFlat?) = some ws

/-- **`ImpRel` is functional in the answers** (`LinkedSessionDAdeq.impRel_det`, wired by
`wireRoundG`). -/
theorem impRel_detW {I : SInst} {m : I.E.Op} {n n' : I.E.Ar m}
    {ds ds' X X' : List (Round (sigN g.imp.imports.length))}
    (h : Silmaril.Wasm.Component.Reference.ImpRel g.imp I ⟨m, n⟩ ds) (h' : Silmaril.Wasm.Component.Reference.ImpRel g.imp I ⟨m, n'⟩ ds')
    (hp : (ds ++ X).map (wireRoundG g) <+: (ds' ++ X').map (wireRoundG g)) :
    n = n' ∧ ds = ds' := by
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
      simp only [wireRoundG, Sigma.mk.injEq, heq_eq_eq, true_and] at h₁
      exact h₁
    subst hR
    exact ⟨hA.symm.trans hA', rfl⟩

theorem impRel_nil_not_liftsI {c : SimpleI} {I : SInst} {x : Σ e : I.E.Op, I.E.Ar e}
    (h : Silmaril.Wasm.Component.Reference.ImpRel c I x []) : ¬ LiftsI c I x.1 := by
  rintro ⟨nm', ft', ws', hft', hl'⟩
  obtain ⟨nm, ft, A, hft, -, hm⟩ := h
  rw [hft] at hft'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hft')
  simp [hl'] at hm

/-- **Two runs of answered core import calls from one state** (`LinkedSessionDAdeq.calls_prefix`
for `wireRoundG`). -/
theorem calls_prefixG {o : GrowOracle} {I : SInst} :
    ∀ {cs cs' : List (Σ e : I.E.Op, I.E.Ar e)}
      {dss dss' : List (List (Round (sigN g.imp.imports.length)))} {q z z' : I.HState}
      {y y' : Move I.E I.F} {Y Y' : List (Move I.E I.F)},
      I.Path (profile o) q (callMoves cs ++ y :: Y) z →
      I.Path (profile o) q (callMoves cs' ++ y' :: Y') z' →
      (∀ e, y' = .inl (.ask e) → LiftsI g.imp I e) →
      List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel g.imp I) cs dss → List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel g.imp I) cs' dss' →
      dss.flatten.map (wireRoundG g) <+: dss'.flatten.map (wireRoundG g) →
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
            exact impRel_nil_not_liftsI hc hL
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
            obtain ⟨rfl, rfl⟩ := impRel_detW hc hc' (by simpa only [List.map_append] using hd)
            cases hp₁ with
            | cons t₂ hp₂ =>
              cases hp₁' with
              | cons t₂' hp₂' =>
                obtain rfl := Silmaril.Wasm.Game.ScalarInstance.Trans.functional t₂ t₂'
                obtain ⟨h₁, h₂⟩ := calls_prefixG hp₂ hp₂' hy' F₁ F₁'
                  ((List.prefix_append_right_inj _).mp hd)
                exact ⟨List.cons_prefix_cons.mpr ⟨rfl, h₁⟩, List.cons_prefix_cons.mpr ⟨rfl, h₂⟩⟩

/-- The relation of a core round of the importer to a round of the importer's node
(`LinkedSessionDAdeq.RdN` for `LinkedG`). -/
def RdNG (g : LinkedG) (I : SInst) (r : CRound I.E I.F) (c : CRound sigU sigU) : Prop :=
  ∃ x, RdI g.imp I r x ∧
    HBR (implsH g.exp.comp.exports.length (wireArgsG g)) x (downBy g.exp.comp.exports.length c)

/-- **Complete core rounds read back from the same node rounds are equal** (deterministic
profiles, under `WireTy`). -/
theorem rounds_eqG {o : GrowOracle} (hw : g.WireTy) {I : SInst} :
    ∀ {cl : List (CRound sigU sigU)} {ri ri' : List (CRound I.E I.F)} {s : Store Nat}
      {z z' : I.HState},
      List.Forall₂ (RdNG g I) ri cl → List.Forall₂ (RdNG g I) ri' cl →
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
    subst hxcs hxcs'
    have hw₁ := hrounds_wire_invG hw dss.flatten csc H
    have hw₂ := hrounds_wire_invG hw dss'.flatten csc H'
    have hdd : dss.flatten.map (wireRoundG g) = dss'.flatten.map (wireRoundG g) :=
      hw₁.symm.trans hw₂
    cases hp with
    | cons t₁ hp₁ =>
      cases hp' with
      | cons t₁' hp₁' =>
        obtain rfl := Silmaril.Wasm.Game.ScalarInstance.Trans.functional t₁ t₁'
        have hy : ∀ e, (.inr (.ans rq ra) : Move I.E I.F) = .inl (.ask e) → LiftsI g.imp I e :=
          fun _ h => nomatch h
        have hy' : ∀ e, (.inr (.ans rq ra') : Move I.E I.F) = .inl (.ask e) →
            LiftsI g.imp I e :=
          fun _ h => nomatch h
        have p₁ := calls_prefixG hp₁ hp₁' hy' hF hF' ⟨[], by rw [List.append_nil]; exact hdd⟩
        have p₂ := calls_prefixG hp₁' hp₁ hy hF' hF
          ⟨[], by rw [List.append_nil]; exact hdd.symm⟩
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
              rw [rounds_eqG hw F F' hp₃ hp₃']

/-- **Two waiting core plays with the same complete rounds and pending question**
(`LinkedSessionDAdeq.pend_prefix` for `wireRoundG`). -/
theorem pend_prefixG {o : GrowOracle} {I : SInst} {s : Store Nat}
    {ri : List (CRound I.E I.F)} {f : I.F.Op} {ics ics' : List (Σ e : I.E.Op, I.E.Ar e)}
    {dss dss' : List (List (Round (sigN g.imp.imports.length)))} {e e' : I.E.Op}
    {z z' : I.HState}
    (hp : I.Path (profile o) (.idle s) (rplay ri f ics ++ [.inl (.ask e)]) z)
    (hp' : I.Path (profile o) (.idle s) (rplay ri f ics' ++ [.inl (.ask e')]) z')
    (hl : LiftsI g.imp I e') (hF : List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel g.imp I) ics dss)
    (hF' : List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel g.imp I) ics' dss')
    (hd : dss.flatten.map (wireRoundG g) <+: dss'.flatten.map (wireRoundG g)) :
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
      exact calls_prefixG hp₂ hp₂' (fun x hx => by cases hx; exact hl) hF hF' hd

end Imp

/-! ## The exporter's side -/

section Exp

variable {P : Profile} {g : LinkedG}

theorem map_stream {α β : Type} (f : α → β) (ds₀ : List α) (ds : ℕ → List α) (n : ℕ) :
    (ds₀ ++ (streamTake ds n).flatten).map f =
      ds₀.map f ++ (streamTake (fun k => (ds k).map f) n).flatten := by
  simp only [streamTake, List.map_append, List.map_flatten, List.map_ofFn]
  rfl

/-- **The exporter's environment, serving typed rounds forever, read back along one run**
(`LinkedSessionDAdeq.exp_plays_stream` for an exporter meeting `Adeq` and `AdeqIC`). -/
theorem exp_plays_streamG (he : g.exp.Adeq P) (hIC : g.exp.AdeqIC P)
    (ds₀ : List (Round (sigN g.imp.imports.length)))
    (ds : ℕ → List (Round (sigN g.imp.imports.length))) (hwt₀ : ∀ y ∈ ds₀, WTG g y)
    (hwt : ∀ k, ∀ y ∈ ds k, WTG g y)
    (h : ∀ n, (twos ((ds₀ ++ (streamTake ds n).flatten).map (wireRoundG g)) :
      List (Move sigU sigU)) ∈ (g.expObs (impSemD P)).plays) :
    ∃ st : ℕ → g.exp.St, LinkedG.ExpRun P g g.exp.init ds₀ (st 0) ∧
      ∀ k, LinkedG.ExpRun P g (st k) (ds k) (st (k + 1)) := by
  obtain ⟨S, h₀, hS⟩ := hIC (ds₀.map (wireRoundG g)) (fun k => (ds k).map (wireRoundG g))
    (typed_wired hwt₀) (fun k => typed_wired (hwt k)) fun n => by
      have hn := h n
      rw [expObs_playsG] at hn
      rw [uMoves_eq, ← map_stream]
      exact expEnvG_inv he hn
  exact ⟨S, expRun_of_run _ hwt₀ h₀, fun k => expRun_of_run _ (hwt k) (hS k)⟩

end Exp

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGChatter
