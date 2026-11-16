module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.Imp

/-!
# Reading back the plays of a simple component with imports at a waiting position

* `wait_of_zip_top`, `wait_of_zip_below`, `wait_of_zip_run`: the positions of the two sides of
  an interaction whose visible part waits (or runs, the upper side waiting on the lower one);
* `rplay_snoc_inj`: `rplay` with one more move is injective;
* `imp_wait_readback`: a finite play of `c.toComp.denU (impSem P)` after typed complete rounds
  `up` and a typed pending export call `(j, .vals vs)` with the lower calls `cs`, waiting on the
  lower call `m`, is, layer by layer (as `imp_div_readback`), a play of the core instance from
  its store: rounds `ri` read back by `RdI`, then the lowered core question `f` pending after
  core import calls `ics` related to `cs` (`ImpRel`), and the core import call `e` pending at
  `.waiting f s t e`; its arguments lift at the import's type to `ws`, and `m = (e, .vals ws)`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq
open Silmaril.Wasm.SingleThreaded (ofFlat toFlat? Thread)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

/-! ## Positions -/

section Pos

variable {E F G : Sig.{0}}

/-- **Below a handler, under a waiting composite**, the strategy waits on the same lower call. -/
theorem wait_of_zip_top {h : Handler F G} {s : List (Move E F)} {t : List (Move F G)}
    {p : List (Move E G)} {y : h.toReduction.toLTS.State} {x : Pos E F} {g : G.Op} {m : E.Op}
    (hz : Zip s t p) (hs : Path .idle s x) (ht : h.toReduction.toLTS.Run .idle t y)
    (hp : Path .idle p (.wait g m)) : ∃ f, Path .idle s (.wait f m) := by
  obtain ⟨c', hc', hcomp⟩ := Strategy.zip_path hz Strategy.ZipCompat.idle hs (path_hpos ht)
  obtain rfl := Path.det hc' hp
  generalize hpos y = b at hcomp
  cases hcomp with
  | wait g f e => exact ⟨f, hs⟩

/-- **Above a handler, under a waiting composite**, the strategy waits on a lower call. -/
theorem wait_of_zip_below {h : Handler E F} {s : List (Move E F)} {t : List (Move F G)}
    {p : List (Move E G)} {y : h.toReduction.toLTS.State} {x : Pos F G} {g : G.Op} {e : E.Op}
    (hz : Zip s t p) (hs : h.toReduction.toLTS.Run .idle s y) (ht : Path .idle t x)
    (hp : Path .idle p (.wait g e)) : ∃ m, Path .idle t (.wait g m) := by
  obtain ⟨c', hc', hcomp⟩ := Strategy.zip_path hz Strategy.ZipCompat.idle (path_hpos hs) ht
  obtain rfl := Path.det hc' hp
  generalize hpos y = b at hcomp
  cases hcomp with
  | wait g f e => exact ⟨f, ht⟩

/-- **Above a running strategy**, the upper side of an interaction waits on its question, and
the composite runs. -/
theorem wait_of_zip_run {s : List (Move E F)} {t : List (Move F G)} {p : List (Move E G)}
    {x : Pos F G} {f : F.Op} (hz : Zip s t p) (hs : Path .idle s (.run f))
    (ht : Path .idle t x) : ∃ g, Path .idle t (.wait g f) ∧ Path .idle p (.run g) := by
  obtain ⟨c', hc', hcomp⟩ := Strategy.zip_path hz Strategy.ZipCompat.idle hs ht
  cases hcomp with
  | call g f => exact ⟨g, ht, hc'⟩

theorem path_wplay (cl : List (CRound E F)) (g : F.Op) (cs : List (Round E)) (m : E.Op) :
    Path .idle (rplay cl g cs ++ [.inl (.ask m)]) (.wait g m) :=
  (path_rplay cl g cs).append (.single (.call g m))

/-- `rplay` with one more move is injective. -/
theorem rplay_snoc_inj {l l' : List (CRound E F)} {g g' : F.Op} {cs cs' : List (Round E)}
    {x x' : Move E F} (h : rplay l g cs ++ [x] = rplay l' g' cs' ++ [x']) :
    l = l' ∧ g = g' ∧ cs = cs' ∧ x = x' := by
  obtain ⟨h₁, h₂⟩ := List.append_inj' h rfl
  obtain ⟨r₁, r₂, r₃⟩ := rplay_inj h₁
  exact ⟨r₁, r₂, r₃, List.singleton_inj.mp h₂⟩

end Pos

/-! ## The pending import call -/

/-- **The pending import call through the wiring**: `core3Sem`'s import handler, the
`canon lower` wiring and the import mask forward the core import call `e` only when its
arguments lift at the import's type to `ws`, as the call of import `e` on `ws`. -/
theorem imp_pend_inv {c : SimpleI} (hc : c.Good) {I : SInst} (hI : c.mod.IsInst I) {e : I.E.Op}
    {m₆ : (CoreIface.sig (CoreModule.imports c.mod)).Op} {m₄ m : sigU.Op}
    {k₈ : (CoreIface.sig (CoreModule.imports c.mod)).Ar m₆ → I.E.Ar e}
    {k₆ : sigU.Ar m₄ → (CoreIface.sig (CoreModule.imports c.mod)).Ar m₆}
    {k₄ : sigU.Ar m → sigU.Ar m₄}
    (h₈ : importH (instNumI hI) e = .call m₆ fun r => .pure (k₈ r))
    (h₆ : implsN c.imports.length (SimpleI.lowerArgs c.imports)
      (CoreModule.imports c.mod).length m₆ = .call m₄ fun r => .pure (k₆ r))
    (h₄ : maskH c.imports.length m₄ = .call m fun r => .pure (k₄ r)) :
    ∃ (nm : String) (ft : FuncTy) (ws : List IVal), c.imports[e.1.val]? = some (nm, ft) ∧
      liftArgs ft.params (e.2.1.filterMap toFlat?) = some ws ∧ m = (e.1.val, .vals ws) := by
  obtain ⟨rfl, -⟩ := Prog.call.inj h₈
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
    exact absurd (hn.symm.trans h₆) (by intro h; cases h)
  | some ws =>
    have hs := implsN_lower_some (e := c.imports.length) hft hlt₆ hlt hl
    obtain ⟨rfl, -⟩ := Prog.call.inj (hs.symm.trans h₆)
    rw [maskH_lt hlt] at h₄
    obtain ⟨rfl, -⟩ := Prog.call.inj h₄
    exact ⟨_, _, ws, hft, hl, rfl⟩

/-! ## The read-back -/

/-- **The read-back of a waiting play of the importer's IR**: a finite play of
`c.toComp.denU (impSem P)` after typed complete rounds `up` and the pending typed export call
`(j, .vals vs)` with the lower calls `cs`, waiting on the lower call `m`, is a play of the core
instance from its store: rounds `ri` read back by `RdI`, then the lowered core question `f`
pending after core import calls `ics` related to `cs` by `ImpRel`, waiting on the core import
call `e`, whose arguments lift at the import's type to `ws`, with `m = (e, .vals ws)`. -/
theorem imp_wait_readback {P : Profile} {c : SimpleI} (hc : c.Good) {I : SInst}
    (hI : c.mod.IsInst I) {up : List (CRound sigU sigU)} (htop : ∀ u ∈ up, TopI c u)
    {j : Fin c.exports.length} {vs : List IVal}
    (hck : ValTy.checkList c.exports[j].ty.params vs = true) {cs : List (Round sigU)}
    {m : sigU.Op}
    (h : rplay up (j.val, .vals vs) cs ++ [.inl (.ask m)] ∈ c.toComp.denU (impSem P)) :
    ∃ (ri : List (CRound I.E I.F)) (f : I.F.Op) (ics : List (Round I.E))
      (dss : List (List (Round (sigN c.imports.length)))) (e : I.E.Op) (s : Store Nat)
      (t : Thread) (nm : String) (ft : FuncTy) (ws : List IVal),
      List.Forall₂ (RdI c I) ri up ∧
      I.Path P (.idle I.store) (rplay ri f ics ++ [.inl (.ask e)]) (.waiting f s t e) ∧
      f.1.val = c.exports[j].core ∧
      f.2.1 = (lowerArgs c.exports[j].ty.params vs).map ofFlat ∧
      List.Forall₂ (ImpRel c I) ics dss ∧ cs = dss.flatten.map Round.forget ∧
      c.imports[e.1.val]? = some (nm, ft) ∧
      liftArgs ft.params (e.2.1.filterMap toFlat?) = some ws ∧ m = (e.1.val, .vals ws) := by
  rw [denU_toCompI] at h
  obtain ⟨s, hs, t, ht, hz⟩ := h
  -- the export handler: the environment waits on `m`
  obtain ⟨yt, hyt⟩ := Strategy.mem_ofHandler.mp ht
  obtain ⟨xs₀, hxs₀⟩ := (envSI (impSem P) c).legal hs
  obtain ⟨f₃, hs₃⟩ := wait_of_zip_top hz hxs₀ hyt (path_wplay _ _ _ _)
  -- the import mask
  obtain ⟨s₁, hs₁, y, hy, hz₁⟩ := hs
  obtain ⟨ys₁, hys₁⟩ := Strategy.mem_ofHandler.mp hs₁
  obtain ⟨xy, hxy⟩ := (((Strategy.id sigU).pair (coreNode (impSem P) c.imports.length c.mod
    (SimpleI.lowerArgs c.imports))).comp (Strategy.ofHandler (splitH _))).legal hy
  obtain ⟨m₄, hy₄⟩ := wait_of_zip_below hz₁ hys₁ hxy hs₃
  obtain ⟨u₄, cs₄, rfl⟩ := exists_wplay hy₄
  obtain ⟨low₃', cs', k₄, H₄, H₄', hk₄, rfl⟩ :=
    hb_zip_wait (oneShot_maskH _) hys₁ hs₃ hz₁
  -- the export handler
  obtain ⟨low₃, k₃, H₃, hk₃, hs_eq⟩ :=
    hc_zip_wait (oneShot_implsH _ _) (path_wplay _ _ _ _) hyt hz
  obtain ⟨rfl, -, rfl, -⟩ := rplay_snoc_inj hs_eq
  have e₃ := (exportsH_typed hc hck).symm.trans hk₃
  obtain ⟨he₃, -⟩ := Prog.call.inj e₃
  subst he₃
  -- the complete rounds, down to the pairing
  have G₃ : List.Forall₂ (L3 c) low₃' up :=
    (forall₂_and_right (forall₂_swap
      (hc_forall₂ H₃ fun u hu a => topI_nonpure hc (htop u hu) a)) htop).imp
      fun _ _ ⟨hr, ht⟩ => l3_of hc ht hr
  have G₄ : List.Forall₂ (L4 c) u₄ up :=
    (forall₂_comp (hb_forall₂ H₄) G₃).imp fun _ _ ⟨_, h₁, h₂⟩ => l4_of h₁ h₂
  have hge : ∀ r ∈ u₄, c.imports.length ≤ r.q.1 := fun r hr =>
    let ⟨_, h⟩ := forall₂_mem_left G₄ r hr
    l4_ge h
  -- `splitH` and the pairing
  obtain ⟨a, ha, b, hb, hz₂⟩ := hy
  obtain ⟨yb, hyb⟩ := Strategy.mem_ofHandler.mp hb
  obtain ⟨xa, hxa⟩ := ((Strategy.id sigU).pair (coreNode (impSem P) c.imports.length c.mod
    (SimpleI.lowerArgs c.imports))).legal ha
  obtain ⟨f₅, ha₅⟩ := wait_of_zip_top hz₂ hxa hyb hy₄
  obtain ⟨low₅, k₅, H₅, hk₅, rfl⟩ := hc_zip_wait (oneShot_splitH _) ha₅ hyb hz₂
  rw [hc_splitH_inv H₅ hge] at ha
  simp only [splitH, Nat.not_lt.mpr (Nat.le_add_left _ _), ↓reduceIte] at hk₅
  obtain ⟨hk₅, -⟩ := Prog.call.inj hk₅
  subst hk₅
  obtain ⟨-, -, haN⟩ := ha
  rw [halves_wplay_inr] at haN
  -- the `canon lower` wiring
  obtain ⟨u, hu, v, hv, hz₆⟩ := haN
  obtain ⟨yu, hyu⟩ := Strategy.mem_ofHandler.mp hu
  obtain ⟨xv, hxv⟩ := (((impSem P).sem c.mod).comp
    (Strategy.ofHandler (widenH (CoreModule.exports c.mod).length))).legal hv
  obtain ⟨m₆, hv₆⟩ := wait_of_zip_below hz₆ hyu hxv (path_wplay _ _ _ _)
  obtain ⟨u₆, cs₆, rfl⟩ := exists_wplay hv₆
  obtain ⟨low₆, cs₆', k₆, H₆, H₆', hk₆, hx⟩ :=
    hb_zip_wait (oneShot_implsN _ _ _) hyu (path_wplay _ _ _ _) hz₆
  obtain ⟨rfl, -, rfl, -⟩ := rplay_snoc_inj hx
  -- `widenH`
  obtain ⟨a₇, ha₇, b₇, hb₇, hz₇⟩ := hv
  obtain ⟨yb₇, hyb₇⟩ := Strategy.mem_ofHandler.mp hb₇
  obtain ⟨xa₇, hxa₇⟩ := ((impSem P).sem c.mod).legal ha₇
  obtain ⟨f₇, ha₇'⟩ := wait_of_zip_top hz₇ hxa₇ hyb₇ hv₆
  obtain ⟨low₇, k₇, H₇, hk₇, rfl⟩ := hc_zip_wait (oneShot_widenH _) ha₇' hyb₇ hz₇
  rw [Nat.add_sub_cancel] at hk₇
  have e₇ := (widenH_lt (core_lt hc j) _).symm.trans hk₇
  obtain ⟨he₇, -⟩ := Prog.call.inj e₇
  subst he₇
  -- `core3Sem`'s import handler
  rw [impSem_sem hI] at ha₇
  obtain ⟨x₈, hx₈, y₈, hy₈, hz₈⟩ := ha₇
  obtain ⟨yx₈, hyx₈⟩ := Strategy.mem_ofHandler.mp hx₈
  obtain ⟨xy₈, hxy₈⟩ := ((I.strategy P I.store).comp
    (Strategy.ofHandler (exportH (instNumI hI)))).legal hy₈
  obtain ⟨m₈, hy₈'⟩ := wait_of_zip_below hz₈ hyx₈ hxy₈ ha₇'
  obtain ⟨u₈, cs₈, rfl⟩ := exists_wplay hy₈'
  obtain ⟨low₈, cs₈', k₈, H₈, H₈', hk₈, hx₈'⟩ :=
    hb_zip_wait (oneShot_importH _) hyx₈ ha₇' hz₈
  obtain ⟨rfl, -, rfl, -⟩ := rplay_snoc_inj hx₈'
  -- `core3Sem`'s export handler and the instance
  obtain ⟨a₉, ha₉, b₉, hb₉, hz₉⟩ := hy₈
  obtain ⟨yb₉, hyb₉⟩ := Strategy.mem_ofHandler.mp hb₉
  obtain ⟨q, hq⟩ := Silmaril.Wasm.Game.ScalarInstance.mem_strategy_iff.mp ha₉
  obtain ⟨f₉, ha₉'⟩ := wait_of_zip_top hz₉ (ipath_pos hq) hyb₉ hy₈'
  obtain ⟨ri, k₉, H₉, hk₉, rfl⟩ := hc_zip_wait (oneShot_exportH _) ha₉' hyb₉ hz₉
  have hl := checkLower_of_check hck
  have e₉ := (exportH_op hI (core_lt hc j)
    (opAtI hI (core_lt hc j) (lowered_types' hc hl (core_lt hc j))) rfl rfl).symm.trans hk₉
  obtain ⟨he₉, -⟩ := Prog.call.inj e₉
  subst he₉
  have hqpos := Path.det (ipath_pos hq) ha₉'
  obtain ⟨sq, tq, hq'⟩ : ∃ sq tq, q = .waiting
      (opAtI hI (core_lt hc j) (lowered_types' hc hl (core_lt hc j))) sq tq m₈ := by
    cases q with
    | idle _ => cases hqpos
    | running _ _ _ => cases hqpos
    | waiting f' sq tq e' =>
      simp only [Silmaril.Wasm.Game.ScalarInstance.HState.pos, Pos.wait.injEq] at hqpos
      obtain ⟨rfl, rfl⟩ := hqpos
      exact ⟨sq, tq, rfl⟩
  subst hq'
  -- the complete rounds, down to the instance
  have G₆ : List.Forall₂ (L6 c) u₆ up :=
    (forall₂_comp (forall₂_map_right (hb_forall₂ H₆)) G₄).imp
      fun _ _ ⟨_, h₁, h₂⟩ => l6_of h₁ h₂
  have G₇ : List.Forall₂ (L7 c) low₇ up :=
    (forall₂_comp (forall₂_swap (hc_forall₂ H₇ fun x hx a =>
      let ⟨_, h⟩ := forall₂_mem_left G₆ x hx
      l6_nonpure hc h a)) G₆).imp fun _ _ ⟨_, h₁, h₂⟩ => l7_of hc h₁ h₂
  have G₈ : List.Forall₂ (L8 c hI) u₈ up :=
    (forall₂_comp (hb_forall₂ H₈) G₇).imp fun _ _ ⟨_, h₁, h₂⟩ => l8_of hI h₁ h₂
  have G₉ : List.Forall₂ (RdI c I) ri up :=
    (forall₂_comp (forall₂_swap (hc_forall₂ H₉ fun x hx a =>
      let ⟨_, h⟩ := forall₂_mem_left G₈ x hx
      l8_nonpure hc hI h a)) G₈).imp fun _ _ ⟨_, h₁, h₂⟩ => rd_of hc hI h₁ h₂
  -- the pending calls, answered and pending
  obtain ⟨dss, hF, hcs⟩ := imp_calls_inv hc hI cs₈ _ _ _ H₈' H₆' H₄'
  obtain ⟨nm, ft, ws, hft, hlw, hm⟩ := imp_pend_inv hc hI hk₈ hk₆ hk₄
  exact ⟨ri, _, cs₈, dss, m₈, sq, tq, nm, ft, ws, G₉, hq, rfl, rfl, hF, hcs, hft, hlw, hm⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq
