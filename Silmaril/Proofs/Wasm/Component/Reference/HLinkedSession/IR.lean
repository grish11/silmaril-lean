module

public import Silmaril.Wasm.Component.Reference.HLinkedSession.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.Games
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionIR.Rounds

/-!
# Linked components with host imports: specification to IR

`hlinked2_sess_specToIR`: an `HLinked2.SessSpec` session from the instances' stores is a play
of `l.toComp.den (impSem P)` (`HLinked2.sessMoves`), the host calls of each round visible as
import moves. The layers, from the bottom (`HLinked2.toComp`, `denU_toCompH`):

* the importer's rounds at its untyped denotation (`layers_denU`, unchanged from `Linked2`);
* the importer's node renames its import calls (`hrounds_impl`): a wired call `n` to the
  exporter's export `k + wire[n]`, a host call `wire.length + i` to the host import `i`;
* the first environment, the host imports and the exporter (`env1_rounds`): a host call is
  forwarded by copycat and the mask (one call below, `cplay_id_calls`); an exporter call is a
  round of the exporter's node without calls (`expRunH_rounds`, `expNodeH_rounds`); both are
  rounds of one mixed pairing (`cplay_pair_mixed`);
* the second environment over the first (`cplay_comp_serveC`): the importer's import calls are
  served by the first environment, its host calls stay visible;
* the export handler and `atSizes`, whose `widenH` turns the host calls into moves of
  `sigN host.length`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionIR
open Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy
open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

variable {P : Profile} {l : HLinked2}

/-! ## The classification of the importer's import calls -/

/-- An import call of the importer is wired to an export of the exporter, or is a host call. -/
def Cls (l : HLinked2) (x : Round (sigN l.imp.imports.length)) : Prop :=
  (x.1.1.val < l.wire.length ∧ l.wire.getD x.1.1.val 0 < l.exp.exports.length) ∨
    (l.wire.length ≤ x.1.1.val ∧ x.1.1.val - l.wire.length < l.host.length)

theorem getD_of_wire {l : HLinked2} {n w : Nat} (hw : l.wire[n]? = some w) :
    l.wire.getD n 0 = w := by
  simp [List.getD_eq_getElem?_getD, hw]

theorem expRunH_cls {I : Silmaril.Wasm.Game.ScalarInstance} :
    ∀ {s s' : Store Nat} {ds : List (Round (sigN l.imp.imports.length))},
      HLinked2.ExpRunH P l I s ds s' → ∀ x ∈ ds, Cls l x
  | _, _, _, .nil _, _, hx => nomatch hx
  | _, _, _, .ret w hw _ hrun, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact .inl ⟨(List.getElem?_eq_some_iff.mp hw).1, by rw [getD_of_wire hw]; exact w.isLt⟩
    · exact expRunH_cls hrun x hx
  | _, _, _, .trap w hw _ hrun, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact .inl ⟨(List.getElem?_eq_some_iff.mp hw).1, by rw [getD_of_wire hw]; exact w.isLt⟩
    · exact expRunH_cls hrun x hx
  | _, _, _, .host i hi hrun, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · refine .inr ⟨?_, ?_⟩ <;> simp only [hi] <;> omega
    · exact expRunH_cls hrun x hx

theorem expRunH_append {I : Silmaril.Wasm.Game.ScalarInstance} {s s₁ s₂ : Store Nat}
    {ds ds' : List (Round (sigN l.imp.imports.length))}
    (h : HLinked2.ExpRunH P l I s ds s₁) (h' : HLinked2.ExpRunH P l I s₁ ds' s₂) :
    HLinked2.ExpRunH P l I s (ds ++ ds') s₂ := by
  induction h with
  | nil => exact h'
  | ret w hw hr _ ih => exact .ret w hw hr (ih h')
  | trap w hw ht _ ih => exact .trap w hw ht (ih h')
  | host i hi _ ih => exact .host i hi (ih h')

/-! ## The rounds of the layers -/

/-- The round of the first environment answering an import call. -/
def sx (l : HLinked2) (x : Round (sigN l.imp.imports.length)) : CRound sigU sigU :=
  if x.1.1.val < l.wire.length then
    ⟨(l.host.length + l.wire.getD x.1.1.val 0, x.1.2), [], x.2⟩
  else ⟨(x.1.1.val - l.wire.length, x.1.2), [⟨(x.1.1.val - l.wire.length, x.1.2), x.2⟩], x.2⟩

/-- The round of the pairing (copycat for a host call, the exporter for a wired call). -/
def mx (l : HLinked2) (x : Round (sigN l.imp.imports.length)) :
    CRound sigU sigU ⊕ CRound sigU sigU :=
  if x.1.1.val < l.wire.length then .inr ⟨(l.wire.getD x.1.1.val 0, x.1.2), [], x.2⟩
  else .inl ⟨(x.1.1.val - l.wire.length, x.1.2), [⟨(x.1.1.val - l.wire.length, x.1.2), x.2⟩], x.2⟩

/-- An import call renamed by the importer's node. -/
def rn (l : HLinked2) (x : Round (sigN l.imp.imports.length)) : Round sigU :=
  ⟨(sx l x).q, (sx l x).a⟩

/-- A wired import call, renamed to the exporter's export. -/
def aCall? (l : HLinked2) (x : Round (sigN l.imp.imports.length)) : Option (Round sigU) :=
  if x.1.1.val < l.wire.length then some ⟨(l.wire.getD x.1.1.val 0, x.1.2), x.2⟩ else none

/-- A host import call, renamed to the host import. -/
def hCall? (l : HLinked2) (x : Round (sigN l.imp.imports.length)) : Option (Round sigU) :=
  if x.1.1.val < l.wire.length then none else some ⟨(x.1.1.val - l.wire.length, x.1.2), x.2⟩

theorem lefts_map_mx : ∀ ds : List (Round (sigN l.imp.imports.length)),
    lefts (ds.map (mx l)) = (ds.filterMap (hCall? l)).map fun r => ⟨r.1, [r], r.2⟩
  | [] => rfl
  | x :: ds => by
    by_cases h : x.1.1.val < l.wire.length
    · simp only [List.map_cons, mx, h, ↓reduceIte, lefts, List.filterMap_cons, hCall?,
        lefts_map_mx ds]
    · simp only [List.map_cons, mx, h, ↓reduceIte, lefts, List.filterMap_cons, hCall?,
        lefts_map_mx ds]

theorem rights_map_mx : ∀ ds : List (Round (sigN l.imp.imports.length)),
    rights (ds.map (mx l)) = (ds.filterMap (aCall? l)).map fun r => ⟨r.1, [], r.2⟩
  | [] => rfl
  | x :: ds => by
    by_cases h : x.1.1.val < l.wire.length
    · simp only [List.map_cons, mx, h, ↓reduceIte, rights, List.filterMap_cons, aCall?,
        rights_map_mx ds]
    · simp only [List.map_cons, mx, h, ↓reduceIte, rights, List.filterMap_cons, aCall?,
        rights_map_mx ds]

theorem flatMap_sx_cs : ∀ ds : List (Round (sigN l.imp.imports.length)),
    (ds.map (sx l)).flatMap (·.cs) = ds.filterMap (hCall? l)
  | [] => rfl
  | x :: ds => by
    by_cases h : x.1.1.val < l.wire.length
    · simp only [List.map_cons, List.flatMap_cons, sx, h, ↓reduceIte, List.filterMap_cons,
        hCall?, flatMap_sx_cs ds, List.nil_append]
    · simp only [List.map_cons, List.flatMap_cons, sx, h, ↓reduceIte, List.filterMap_cons,
        hCall?, flatMap_sx_cs ds, List.singleton_append]

theorem hCalls_eq : ∀ {ds : List (Round (sigN l.imp.imports.length))}, (∀ x ∈ ds, Cls l x) →
    ds.filterMap (hCall? l) = (l.hostCalls ds).map Round.forget
  | [], _ => rfl
  | x :: ds, H => by
    have ih := hCalls_eq (ds := ds) fun y hy => H y (List.mem_cons_of_mem _ hy)
    by_cases h : x.1.1.val < l.wire.length
    · have hn : ¬ (l.wire.length ≤ x.1.1.val ∧ x.1.1.val - l.wire.length < l.host.length) :=
        fun h' => by omega
      simp only [List.filterMap_cons, hCall?, h, ↓reduceIte, HLinked2.hostCalls,
        HLinked2.hostCall?, hn, ↓reduceDIte]
      exact ih
    · have hc := H x List.mem_cons_self
      have hy : l.wire.length ≤ x.1.1.val ∧ x.1.1.val - l.wire.length < l.host.length := by
        rcases hc with hc | hc
        · exact absurd hc.1 h
        · exact hc
      simp only [List.filterMap_cons, hCall?, h, ↓reduceIte, HLinked2.hostCalls,
        HLinked2.hostCall?, hy, and_self, ↓reduceDIte, List.map_cons, Round.forget]
      exact congrArg _ ih

/-! ## The denotation of `HLinked2.toComp` -/

/-- The node of the exporter, after the host imports. -/
abbrev expNodeH (C : CoreSem ImpModule) (l : HLinked2) : Strategy sigU sigU :=
  (Strategy.ofHandler (implsH l.host.length [])).comp ((SimpleI.ofSimple l.exp).toComp.denU C)

/-- The node of the importer. -/
abbrev impNodeH (C : CoreSem ImpModule) (l : HLinked2) : Strategy sigU sigU :=
  (Strategy.ofHandler (implsH (l.host.length + l.exp.exports.length)
    (l.wireArgs ++ l.hostArgs))).comp (l.imp.toComp.denU C)

/-- The first environment: the host imports and the exporter. -/
abbrev env1 (C : CoreSem ImpModule) (l : HLinked2) : Strategy sigU sigU :=
  ext l.host.length (Strategy.ofHandler (maskH l.host.length)) (expNodeH C l)

/-- The environment of the linked component's exports. -/
abbrev envH (C : CoreSem ImpModule) (l : HLinked2) : Strategy sigU sigU :=
  ext (l.host.length + l.exp.exports.length) (env1 C l) (impNodeH C l)

theorem denU_toCompH (C : CoreSem ImpModule) (l : HLinked2) :
    l.toComp.denU C = (envH C l).comp (Strategy.ofHandler
      (exportsH (l.host.length + l.exp.exports.length + l.imp.exports.length)
        l.toComp.exports)) := by
  simp only [HLinked2.toComp, Comp.denU, denNodes, Node.den, envAfter, Node.width,
    Comp.exports_mk, SimpleI.exports_length_toComp]
  rfl

/-- The linked export handler forwards export `j` to the importer's export `j`. -/
theorem exportsH_toCompH (l : HLinked2) {j : Nat} (hj : j < l.imp.exports.length) (p : Payload) :
    exportsH (l.host.length + l.exp.exports.length + l.imp.exports.length) l.toComp.exports
      (j, p) = .call (l.host.length + l.exp.exports.length + j, p) fun n => .pure n := by
  have hget : (l.toComp.exports.map Export.impl)[j]? =
      some ⟨[], .call (l.host.length + l.exp.exports.length + j)⟩ := by
    simp [HLinked2.toComp, hj]
  simp only [exportsH, implsH, hget, Impl.prog, runChain, Target.prog,
    ite_eq_left (Nat.add_lt_add_left hj _)]

/-! ## The importer's node -/

theorem implsH_args {x : Round (sigN l.imp.imports.length)} (hx : Cls l x) :
    implsH (l.host.length + l.exp.exports.length) (l.wireArgs ++ l.hostArgs) (x.1.1.val, x.1.2) =
      .call (rn l x).1 fun n => .pure n := by
  rcases hx with ⟨h, hw⟩ | ⟨h, hh⟩
  · have hget : (l.wireArgs ++ l.hostArgs)[x.1.1.val]? =
        some ⟨[], .call (l.host.length + l.wire.getD x.1.1.val 0)⟩ := by
      rw [List.getElem?_append_left (by simpa [HLinked2.wireArgs] using h)]
      simp [HLinked2.wireArgs, List.getD_eq_getElem?_getD, h]
    have hlt : l.host.length + l.wire.getD x.1.1.val 0 <
        l.host.length + l.exp.exports.length := by omega
    have hr : rn l x = ⟨(l.host.length + l.wire.getD x.1.1.val 0, x.1.2), x.2⟩ := by
      unfold rn sx
      rw [ite_eq_left h]
    rw [hr]
    simp only [implsH, hget, Impl.prog, runChain, Target.prog, hlt, ↓reduceIte]
  · have hget : (l.wireArgs ++ l.hostArgs)[x.1.1.val]? =
        some ⟨[], .call (x.1.1.val - l.wire.length)⟩ := by
      rw [List.getElem?_append_right (by simpa [HLinked2.wireArgs] using h)]
      simp [HLinked2.wireArgs, HLinked2.hostArgs, hh]
    have hlt : x.1.1.val - l.wire.length < l.host.length + l.exp.exports.length := by omega
    have hn : ¬ x.1.1.val < l.wire.length := by omega
    have hr : rn l x = ⟨(x.1.1.val - l.wire.length, x.1.2), x.2⟩ := by
      unfold rn sx
      rw [ite_eq_right hn]
    rw [hr]
    simp only [implsH, hget, Impl.prog, runChain, Target.prog, hlt, ↓reduceIte]

theorem rn_snd (x : Round (sigN l.imp.imports.length)) : (rn l x).2 = x.2 := by
  show (sx l x).a = x.2
  unfold sx
  by_cases h : x.1.1.val < l.wire.length
  · rw [ite_eq_left h]
  · rw [ite_eq_right h]

/-- **The importer's node renames its import calls.** -/
theorem hrounds_impl : ∀ {ds : List (Round (sigN l.imp.imports.length))}, (∀ x ∈ ds, Cls l x) →
    HRounds (implsH (l.host.length + l.exp.exports.length) (l.wireArgs ++ l.hostArgs))
      (ds.map Round.forget) (ds.map (rn l))
  | [], _ => .nil
  | x :: ds, H => by
    show HRounds _ (⟨(x.1.1.val, x.1.2), x.2⟩ :: ds.map Round.forget)
      (⟨(rn l x).1, (rn l x).2⟩ :: ds.map (rn l))
    exact .call (q := (x.1.1.val, x.1.2)) (q' := (rn l x).1) (k := fun n => .pure n)
      (a' := (rn l x).2) (a := x.2)
      (implsH_args (H x List.mem_cons_self)) (by show Prog.pure _ = _; rw [rn_snd])
      (hrounds_impl fun y hy => H y (List.mem_cons_of_mem _ hy))

/-! ## The exporter -/

/-- **The exporter's answers to the wired calls**, threading its store, host calls skipped. -/
theorem expRunH_rounds (hc : l.exp.Good) {I : Silmaril.Wasm.Game.ScalarInstance}
    (hI : l.exp.mod.IsInst I) :
    ∀ {s s' : Store Nat} {ds : List (Round (sigN l.imp.imports.length))},
      HLinked2.ExpRunH P l I s ds s' → I.WellFormed s →
      ∃ (li : List (Round I.F)) (lc : List (Round (CoreIface.sig (CoreModule.exports l.exp.mod)))),
        I.Activation P s (twos li) s' ∧ HRounds (exportH (instNum hI)) lc li ∧
        HRounds (exportsH l.exp.mod.exports.length l.exp.toComp.exports)
          (ds.filterMap (aCall? l)) (lc.map Round.forget)
  | _, _, _, .nil _, _ => ⟨[], [], .nil _, .nil, .nil⟩
  | _, _, _, .ret (n := n) (ws := ws) (us := us) w hw hret hrun, hwf => by
    have hwf' : I.WellFormed _ := hret.wellFormed hI (hc.core _ (List.getElem_mem w.isLt)) hwf
    obtain ⟨li₁, lc₁, hact₁, H₁, X₁⟩ := retAt_rounds hc hI hwf hret
    obtain ⟨li, lc, hact, H, X⟩ := expRunH_rounds hc hI hrun hwf'
    have hlt : n.val < l.wire.length := (List.getElem?_eq_some_iff.mp hw).1
    have e : aCall? l ⟨(n, .vals ws), some (.vals us)⟩ =
        some ⟨(w.val, .vals ws), some (.vals us)⟩ := by
      simp only [aCall?, hlt, ↓reduceIte, getD_of_wire hw]
    refine ⟨li₁ ++ li, lc₁ ++ lc, ?_, H₁.append H, ?_⟩
    · rw [twos_append]
      exact path_append hact₁ hact
    · rw [List.filterMap_cons_some e, List.map_append]
      exact X₁.append X
  | _, _, _, .trap (n := n) (ws := ws) w hw htrap hrun, hwf => by
    have hwf' : I.WellFormed _ := htrap.wellFormed hI (hc.core _ (List.getElem_mem w.isLt)) hwf
    obtain ⟨li₁, lc₁, hact₁, H₁, X₁⟩ := trapAt_rounds hc hI hwf htrap
    obtain ⟨li, lc, hact, H, X⟩ := expRunH_rounds hc hI hrun hwf'
    have hlt : n.val < l.wire.length := (List.getElem?_eq_some_iff.mp hw).1
    have e : aCall? l ⟨(n, .vals ws), none⟩ = some ⟨(w.val, .vals ws), none⟩ := by
      simp only [aCall?, hlt, ↓reduceIte, getD_of_wire hw]
    refine ⟨li₁ ++ li, lc₁ ++ lc, ?_, H₁.append H, ?_⟩
    · rw [twos_append]
      exact path_append hact₁ hact
    · rw [List.filterMap_cons_some e, List.map_append]
      exact X₁.append X
  | _, _, _, .host (n := n) (p := p) (R := R) i hi hrun, hwf => by
    obtain ⟨li, lc, hact, H, X⟩ := expRunH_rounds hc hI hrun hwf
    have hn : ¬ n.val < l.wire.length := by omega
    have e : aCall? l ⟨(n, p), R⟩ = none := by simp only [aCall?, hn, ↓reduceIte]
    refine ⟨li, lc, hact, H, ?_⟩
    rw [List.filterMap_cons_none e]
    exact X

/-- The exporter's rounds at its node in the linked component. -/
theorem expNodeH_rounds {I : Silmaril.Wasm.Game.ScalarInstance} (hI : l.exp.mod.IsInst I)
    {low : List (Round sigU)} {li : List (Round I.F)}
    {lc : List (Round (CoreIface.sig (CoreModule.exports l.exp.mod)))}
    (hli : twos li ∈ I.strategy P I.store) (H : HRounds (exportH (instNum hI)) lc li)
    (X : HRounds (exportsH l.exp.mod.exports.length l.exp.toComp.exports) low
      (lc.map Round.forget)) :
    twos low ∈ expNodeH (impSem P) l := by
  have hsem : twos lc ∈ (modSem P).sem l.exp.mod := sem_rounds hI H hli
  have hden : twos low ∈ l.exp.toComp.denU (modSem P) := by
    rw [denU_toComp]
    exact twos_comp_ofHandler X (envS_rounds (modSem P) l.exp hsem)
  refine twos_comp_upper ?_
  rw [denU_ofSimple]
  exact hden

/-! ## The first environment -/

theorem hc_splitH (x : Round (sigN l.imp.imports.length)) (hx : Cls l x) :
    HC (E := sigU) (splitH l.host.length) [sx l x] [CRound.lift (mx l x)] := by
  by_cases h : x.1.1.val < l.wire.length
  · simp only [sx, mx, h, ↓reduceIte, CRound.lift]
    exact .call (splitH_shift' _ _ _) rfl .nil
  · have hh : x.1.1.val - l.wire.length < l.host.length := by
      rcases hx with hx | hx
      · exact absurd hx.1 h
      · exact hx.2
    simp only [sx, mx, h, ↓reduceIte, CRound.lift]
    exact .call (q := (x.1.1.val - l.wire.length, x.1.2))
      (h := splitH _) (q' := Sum.inl (x.1.1.val - l.wire.length, x.1.2)) (k := fun n => .pure n)
      (by simp only [splitH, hh, ↓reduceIte]) rfl .nil

theorem hb_maskH (x : Round (sigN l.imp.imports.length)) (hx : Cls l x) :
    HB (G := sigU) (maskH l.host.length) [sx l x] [sx l x] := by
  by_cases h : x.1.1.val < l.wire.length
  · simp only [sx, h, ↓reduceIte]
    exact .cons .nil .nil
  · have hh : x.1.1.val - l.wire.length < l.host.length := by
      rcases hx with hx | hx
      · exact absurd hx.1 h
      · exact hx.2
    simp only [sx, h, ↓reduceIte]
    exact .cons (.call (h := maskH _) (q := (x.1.1.val - l.wire.length, x.1.2))
      (q' := (x.1.1.val - l.wire.length, x.1.2)) (k := fun n => .pure n)
      (by simp only [maskH, Target.prog, hh, ↓reduceIte]) rfl .nil) .nil

/-- **The first environment answers the importer's import calls**: host calls by one call
below, wired calls by the exporter's rounds. -/
theorem env1_rounds (hc : l.exp.Good) {I : Silmaril.Wasm.Game.ScalarInstance}
    (hI : l.exp.mod.IsInst I) {ds : List (Round (sigN l.imp.imports.length))} {s' : Store Nat}
    (hrun : HLinked2.ExpRunH P l I I.store ds s') :
    cplay (ds.map (sx l)) ∈ env1 (impSem P) l := by
  have hcls := expRunH_cls hrun
  obtain ⟨li, lc, hact, H, X⟩ := expRunH_rounds hc hI hrun hI.1.choose_spec.ok
  have hli : twos li ∈ I.strategy P I.store := by
    have h' := Silmaril.Wasm.Game.ScalarInstance.append_mem_of hact (I.strategy P s').nil_mem
    rwa [List.append_nil] at h'
  have hA := expNodeH_rounds hI hli H X
  have hpair : cplay ((ds.map (mx l)).map CRound.lift) ∈
      (Strategy.id sigU).pair (expNodeH (impSem P) l) := by
    refine cplay_pair_mixed ?_ ?_
    · rw [lefts_map_mx]
      exact cplay_id_calls _
    · rw [rights_map_mx, cplay_nocalls]
      exact hA
  have hY : cplay (ds.map (sx l)) ∈ ((Strategy.id sigU).pair (expNodeH (impSem P) l)).comp
      (Strategy.ofHandler (splitH l.host.length)) := by
    refine cplay_comp_ofHandler ?_ hpair
    rw [List.map_map]
    exact HC.of_map _ _ ds fun x hx => hc_splitH x (hcls x hx)
  unfold env1 ext
  exact cplay_ofHandler_comp (HB.of_map _ _ ds fun x hx => hb_maskH x (hcls x hx)) hY

/-! ## Sessions -/

/-- The IR round of the linked component of an IR round of the importer: the export question
and answer, the host calls visible. -/
def hround (l : HLinked2)
    (u : CRound (sigN l.imp.imports.length) (sigN l.imp.toComp.exports.length)) :
    CRound (sigN l.host.length) (sigN l.toComp.exports.length) :=
  ⟨(⟨u.q.1.val, by simpa [HLinked2.exports_length_toComp, SimpleI.exports_length_toComp]
      using u.q.1.isLt⟩, u.q.2), l.hostCalls u.cs, u.a⟩

section Layers

variable {Ii : Silmaril.Wasm.Game.ScalarInstance}

/-- **Rounds of the importer whose import calls are an `ExpRunH` are rounds of the linked
component, the host calls visible.** -/
theorem hlink_layers (he : l.exp.Good) {Ie : Silmaril.Wasm.Game.ScalarInstance}
    (hIe : l.exp.mod.IsInst Ie) {L : List (LayerI l.imp Ii)} {s' : Store Nat}
    (himp : cplay (L.map LayerI.l₆) ∈ l.imp.toComp.denU (impSem P))
    (hrun : HLinked2.ExpRunH P l Ie Ie.store (L.flatMap fun d => d.dss.flatten) s') :
    cplay ((L.map LayerI.u).map (hround l)) ∈ l.toComp.den (impSem P) := by
  have hcls := expRunH_cls hrun
  have hcl : ∀ d ∈ L, ∀ x ∈ d.dss.flatten, Cls l x := fun d hd x hx =>
    hcls x (List.mem_flatMap.mpr ⟨d, hd, hx⟩)
  have hD1 := env1_rounds he hIe hrun
  have hN : cplay (L.map fun d => (⟨(d.j.val, .vals d.vs), d.dss.flatten.map (rn l), d.ans⟩ :
      CRound sigU sigU)) ∈ impNodeH (impSem P) l :=
    cplay_ofHandler_comp (HB.of_map _ _ L fun d hd => .cons (hrounds_impl (hcl d hd)) .nil) himp
  have hP : cplay (L.map fun d => (⟨.inr (d.j.val, .vals d.vs), d.dss.flatten.map (rn l),
      d.ans⟩ : CRound sigU (sigU ⊕ₛ sigU))) ∈ (Strategy.id sigU).pair (impNodeH (impSem P) l) :=
    by have h := cplay_pair_inr (σ₁ := Strategy.id sigU) hN; rwa [List.map_map] at h
  let LS : List (SRound sigU sigU sigU) := L.map fun d =>
    ⟨(l.host.length + l.exp.exports.length + d.j.val, .vals d.vs),
      d.dss.flatten.map (sx l), d.ans⟩
  have hS : cplay (LS.map SRound.up) ∈ ((Strategy.id sigU).pair (impNodeH (impSem P) l)).comp
      (Strategy.ofHandler (splitH (l.host.length + l.exp.exports.length))) := by
    have e : LS.map SRound.up = L.map fun d =>
        (⟨(l.host.length + l.exp.exports.length + d.j.val, .vals d.vs),
          d.dss.flatten.map (rn l), d.ans⟩ : CRound sigU sigU) := by
      simp only [LS, List.map_map]
      refine List.map_congr_left fun d _ => ?_
      simp only [Function.comp, SRound.up, List.map_map]
      rfl
    rw [e]
    exact cplay_comp_ofHandler (HC.of_map _ _ L fun d _ =>
      .call (h := splitH _) (splitH_shift' _ _ _) rfl .nil) hP
  have hσ : cplay (LS.flatMap (·.subs)) ∈ env1 (impSem P) l := by
    have e : LS.flatMap (·.subs) = (L.flatMap fun d => d.dss.flatten).map (sx l) := by
      simp only [LS, List.flatMap_map, List.map_flatMap]
    rw [e]
    exact hD1
  have hE : cplay (LS.map SRound.vis) ∈ envH (impSem P) l := by
    unfold envH ext
    exact cplay_comp_serveC hσ hS
  have hvis : LS.map SRound.vis = L.map fun d =>
      (⟨(l.host.length + l.exp.exports.length + d.j.val, .vals d.vs),
        (l.hostCalls d.dss.flatten).map Round.forget, d.ans⟩ : CRound sigU sigU) := by
    simp only [LS, List.map_map]
    refine List.map_congr_left fun d hd => ?_
    simp only [Function.comp, SRound.vis, flatMap_sx_cs, hCalls_eq (hcl d hd)]
  rw [hvis] at hE
  have hU : cplay (L.map fun d => (⟨(d.j.val, .vals d.vs),
      (l.hostCalls d.dss.flatten).map Round.forget, d.ans⟩ : CRound sigU sigU)) ∈
      l.toComp.denU (impSem P) := by
    rw [denU_toCompH]
    exact cplay_comp_ofHandler (HC.of_map _ _ L fun d _ =>
      .call (h := exportsH _ _) (q := (d.j.val, .vals d.vs))
        (q' := (l.host.length + l.exp.exports.length + d.j.val, .vals d.vs))
        (k := fun n => .pure n) (exportsH_toCompH l d.j.isLt _) rfl .nil) hE
  have hW : cplay (L.map fun d => (⟨(d.j.val, .vals d.vs), l.hostCalls d.dss.flatten, d.ans⟩ :
      CRound (sigN l.host.length) sigU)) ∈
      (Strategy.ofHandler (widenH l.host.length)).comp (l.toComp.denU (impSem P)) :=
    cplay_ofHandler_comp (HB.of_map _ _ L fun _ _ => .cons (hrounds_widenH _ _) .nil) hU
  rw [List.map_map]
  unfold Comp.den atSizes
  exact cplay_comp_ofHandler (HC.of_map _ _ L fun _ _ => .call (h := narrowH _) rfl rfl .nil) hW

end Layers

/-- **A specification session is a list of session rounds**, played one after another. -/
theorem sessSpecH_rounds {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {u π u' π' : Store Nat}
    {calls : List (Fin l.imp.exports.length × List IVal)} {outs : List (Option (List IVal))}
    {hs : List (List (Round (sigN l.host.length)))}
    (h : HLinked2.SessSpec P l Ie Ii u π calls outs hs u' π') :
    ∃ L : List (Linked2.SessRound l.toL2 Ii), (∀ d ∈ L, d.Ok) ∧
      Ii.Path P (.idle u) (L.flatMap Linked2.SessRound.instMoves) (.idle u') ∧
      HLinked2.ExpRunH P l Ie π (L.flatMap fun d => d.dss.flatten) π' ∧
      cplay ((L.map SessRound.u).map (hround l)) = l.sessMoves calls outs hs := by
  induction h with
  | nil u π => exact ⟨[], (fun _ h => nomatch h), .nil _, .nil _, rfl⟩
  | round d hok hpath hrun hans _ ih =>
    obtain ⟨L, hL, hp, hr, hm⟩ := ih
    refine ⟨d :: L, ?_, ?_, ?_, ?_⟩
    · intro d' hd'
      rcases List.mem_cons.mp hd' with rfl | h
      · exact hok
      · exact hL d' h
    · rw [List.flatMap_cons]
      exact path_append hpath hp
    · rw [List.flatMap_cons]
      exact expRunH_append hrun hr
    · rw [List.map_cons, List.map_cons, cplay, hm]
      simp only [hround, SessRound.u, hans]
      rfl

theorem sessSpecH_length {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {u π u' π' : Store Nat}
    {calls : List (Fin l.imp.exports.length × List IVal)} {outs : List (Option (List IVal))}
    {hs : List (List (Round (sigN l.host.length)))}
    (h : HLinked2.SessSpec P l Ie Ii u π calls outs hs u' π') :
    calls.length = outs.length ∧ calls.length = hs.length := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | round _ _ _ _ _ _ ih => exact ⟨by simp [ih.1], by simp [ih.2]⟩

/-- **Specification sessions of a linked component with host imports are IR plays.** -/
theorem hlinked2_sess_specToIR (he : l.exp.Good) (hi : l.imp.Good)
    {Ie : Silmaril.Wasm.Game.ScalarInstance} (hIe : l.exp.mod.IsInst Ie)
    {Ii : Silmaril.Wasm.Game.ScalarInstance} (hIi : l.imp.mod.IsInst Ii)
    {calls : List (Fin l.imp.exports.length × List IVal)} {outs : List (Option (List IVal))}
    {hs : List (List (Round (sigN l.host.length)))} {u' π' : Store Nat}
    (h : HLinked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs hs u' π') :
    l.sessMoves calls outs hs ∈ l.toComp.den (impSem P) := by
  obtain ⟨Ls, hLs, hp, hr, hm⟩ := sessSpecH_rounds h
  rw [← hm]
  have hp' : Ii.Path P (.idle Ii.store) (cplay (Ls.map SessRound.r)) (.idle u') := by
    rw [cplay_r]
    exact hp
  have hrel := rel_u (l := l.toL2) hLs
  obtain ⟨L, hL, hLr, hLu⟩ := layers_of hi hIi hrel
  have hinst : cplay (L.map LayerI.r) ∈ Ii.strategy P Ii.store := by
    rw [hLr]
    exact cplay_mem_strategy hp'
  have himp : cplay (L.map LayerI.l₆) ∈ l.imp.toComp.denU (impSem P) :=
    layers_denU (l := l.toL2) hIi hL (layers_env hIi hL (layers_sem hIi hL hinst))
  have h1 : (L.map LayerI.u).flatMap (·.cs) = L.flatMap fun d => d.dss.flatten := by
    rw [List.flatMap_map]
    rfl
  have e : L.flatMap (fun d => d.dss.flatten) = Ls.flatMap fun d => d.dss.flatten := by
    rw [← h1, hLu]
    exact flatMap_u_cs (l := l.toL2) Ls
  have hrun' : HLinked2.ExpRunH P l Ie Ie.store (L.flatMap fun d => d.dss.flatten) π' := by
    rw [e]
    exact hr
  have hfin := hlink_layers he hIe himp hrun'
  rw [hLu] at hfin
  exact hfin

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession
