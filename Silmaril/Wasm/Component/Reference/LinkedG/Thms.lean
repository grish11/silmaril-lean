module

public import Silmaril.Wasm.Component.Reference.LinkedG.Defs
public import Silmaril.Wasm.Component.Reference.LinkedSessionRef.Defs
import Silmaril.Proofs.Wasm.Component.Reference.LinkedG.Main

/-!
# Linking with an abstract exporter, and chains of linked modules: theorems

**Scope.** The IR side only: specification sessions against plays of `Comp.denU`/`Comp.den`
over `impSem P`, for every profile `P`. The reference side (`toRef` on the reference machine)
is not proved for `LinkedG` or `LinkedN`; see "Not claimed".

1. **A simple component is an exporter** (`Simple.expSpec_adeq`): under `Simple.Good` and
   `IsInst`, `Simple.expSpec c I` meets `ExpSpec.Adeq P`: its sessions (`RetAt`/`TrapAt`
   rounds threading the Core store) from the instance's store are plays of
   `(SimpleI.ofSimple c).toComp.denU (impSem P)`, and every play of complete rounds of typed
   calls is such a session. It repackages #676's `sessRounds_rounds`, `specRoundsT_of_denU`
   and `sessRounds_of_specRoundsT`.
2. **Linking an abstract exporter** (`LinkedG`, exporter `ExpSpec.Adeq`, importer `Good` and
   `IsInst`, `WireTy` for the read-back):
   * `LinkedG.sess_specToIR`: specification sessions from the importer's store and the
     exporter's initial state are IR plays of `g.toComp.den (impSem P)`;
   * `LinkedG.irToSpec`: IR session plays of typed calls are specification sessions;
   * `LinkedG.sessIR_iff`: both together.

   **`Linked2` is an instance** (`Linked2.toG l Ie`): the same IR and reference components
   (`Linked2.toG_toComp`, `Linked2.toG_toRef`), the same specification sessions
   (`Linked2.sessSpec_toG_iff`), the same IR plays (`Linked2.sessMoves_toG_iff`), and
   `Linked2.Adequate` gives the hypotheses (`Linked2.toG_adeq`, `Linked2.toG_wireTy`);
   `Linked2.sessIR_iff_viaG` re-derives `Linked2.sessIR_iff` from `LinkedG.sessIR_iff`.
3. **A linked component is an exporter** (`LinkedG.toExp_adeq`): its session specification is
   the linked `SessSpec` (one step per `SessRound`), its forward and backward facts are those of
   step 2 at the untyped interface. **Chains, by induction** (`chainExp_adeq`, `LinkedN.adeq`):
   for `LinkedN := ⟨base, links⟩`, under `base.Good`, the base instance and `ChainOk` (each
   importer `Good`, its instance, `WireTy` against the component built so far), the chain's
   specification `n.spec Ib Is` meets `ExpSpec.Adeq P`, and its IR component is
   `n.toComp` (`LinkedN.spec_comp`). **Finite adequacy of `LinkedN` on the IR side**
   (`LinkedN.sessIR_iff`): the plays of complete rounds of typed calls of `n.toComp.denU
   (impSem P)` are exactly the sessions of the chain's specification. Linking one more importer
   onto a chain is `LinkedG.sessIR_iff` with `he := LinkedN.adeq …` (at `Comp.den`, with
   `SessSpec`).

**Not claimed.**

* **The reference side** (`sess_refToSpec`/`sess_specToRef`, `sessAdequacy_full` for `LinkedG`
  and `LinkedN`). The `Linked2` proofs do not factor through `ExpSpec`: the invariant between
  calls (`LReady`) relates the machine's shared core store to A's and B's stores by a store split
  (`Rel4`, A's part the import-free prefix `ownOf s₀`, B's trampolines renamed by `gL`), and A's
  call is a **core** run of A's activation in the shared store (`exp_fwd`, `LinkExp`), after
  B's `canon lower` and A's `canon lift`. When A is itself linked (`LinkedG.toRef` nesting
  `g.exp.ref`), A's call re-enters the component machine (B''s `canon lower` inside A, then
  A''s `canon lift`), so the core-level simulation does not apply. An exporter interface for the
  reference side would need: (R1) a relation between the exporter's state and its part of the
  machine configuration (its prefix of the shared core store and its component instances), kept
  by the importer's steps; (R2) forward machine runs of a cross-instance call into A's lifted
  export `w` from that relation, for each `Step` (resolved, or trapped with the trapped
  configuration); (R3) the converse read-back of such runs into `Step`s; (R4) instantiation of
  `ref` into the relation at `init`, with the aliases by `expName` finding the wired lifts;
  (R5) the relation kept by `resumeCfg`. `ExpSpec.ref` and `LinkedG.toRef` record the
  translation only; no theorem of this topic is about them beyond `Linked2.toG_toRef`.
* Divergence and infinite plays (`LinkedSessionDiv`, `LinkedSessionDAdeq`) for `LinkedG` and
  `LinkedN`.
* Ill-typed calls of the linked component (as for `Linked2`).

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.LinkedG.{Basic, Main}`.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (ScalarInstance)
open Silmaril.Wasm.Execution.Core (Store)

local notation "IVal" => Silmaril.Wasm.Component.Val

/-! ## Step 1: a simple component is an exporter -/

/-- **A simple component meets the exporter interface** (proved, every profile). -/
theorem Simple.expSpec_adeq (P : Profile) {c : Simple} (hc : c.Good) {I : ScalarInstance}
    (hI : c.mod.IsInst I) : (Simple.expSpec c I).Adeq P :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedG.simple_adeq P hc hI

/-! ## Step 2: linking an abstract exporter -/

namespace LinkedG

variable {P : Profile} {g : LinkedG} {Ii : ScalarInstance}

/-- **Specification sessions are IR plays** (proved, every profile). -/
theorem sess_specToIR (he : g.exp.Adeq P) (hi : g.imp.Good) (hIi : g.imp.mod.IsInst Ii)
    {calls : List (Fin g.imp.exports.length × List IVal)} {outs : List (Option (List IVal))}
    {u' : Store Nat} {π' : g.exp.St} (h : g.SessSpec P Ii Ii.store g.exp.init calls outs u' π') :
    g.sessMoves calls outs ∈ g.toComp.den (impSem P) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedG.sess_specToIR he hi hIi h

/-- **IR session plays of typed calls are specification sessions** (proved, every profile). -/
theorem irToSpec (he : g.exp.Adeq P) (hi : g.imp.Good) (hIi : g.imp.mod.IsInst Ii)
    (hw : g.WireTy) (calls : List (Fin g.imp.exports.length × List IVal))
    (outs : List (Option (List IVal))) (ht : SimpleI.TypedCalls g.imp calls)
    (hlen : calls.length = outs.length) (h : g.sessMoves calls outs ∈ g.toComp.den (impSem P)) :
    ∃ (u' : Store Nat) (π' : g.exp.St), g.SessSpec P Ii Ii.store g.exp.init calls outs u' π' :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedG.irToSpec he hi hIi hw calls outs ht hlen h

/-- **The session plays of a linked component are exactly the specification sessions**
(proved, every profile, typed calls with one outcome per call). -/
theorem sessIR_iff (he : g.exp.Adeq P) (hi : g.imp.Good) (hIi : g.imp.mod.IsInst Ii)
    (hw : g.WireTy) (calls : List (Fin g.imp.exports.length × List IVal))
    (outs : List (Option (List IVal))) (ht : SimpleI.TypedCalls g.imp calls)
    (hlen : calls.length = outs.length) :
    g.sessMoves calls outs ∈ g.toComp.den (impSem P) ↔
      ∃ (u' : Store Nat) (π' : g.exp.St), g.SessSpec P Ii Ii.store g.exp.init calls outs u' π' :=
  ⟨irToSpec he hi hIi hw calls outs ht hlen, fun ⟨_, _, h⟩ => sess_specToIR he hi hIi h⟩

end LinkedG

/-! ### `Linked2` is an instance -/

namespace Linked2

/-- `Linked2.toG` has the IR component of `Linked2` (proved). -/
theorem toG_toComp (l : Linked2) (Ie : ScalarInstance) : (l.toG Ie).toComp = l.toComp :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedG.toG_toComp l Ie

/-- `Linked2.toG` has the reference component of `Linked2` (proved). -/
theorem toG_toRef (l : Linked2) (Ie : ScalarInstance) : (l.toG Ie).toRef = l.toRef :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedG.toG_toRef l Ie

/-- **The same specification sessions** (proved). -/
theorem sessSpec_toG_iff {P : Profile} {l : Linked2} {Ie Ii : ScalarInstance}
    {u u' π π' : Store Nat} {calls : List (Fin l.imp.exports.length × List IVal)}
    {outs : List (Option (List IVal))} :
    (l.toG Ie).SessSpec P Ii u π calls outs u' π' ↔ l.SessSpec P Ie Ii u π calls outs u' π' :=
  ⟨Silmaril.Proofs.Wasm.Component.Reference.LinkedG.sessSpec_of_toG,
    Silmaril.Proofs.Wasm.Component.Reference.LinkedG.toG_of_sessSpec⟩

/-- **The same IR session plays** (proved). -/
theorem sessMoves_toG_iff (P : Profile) (l : Linked2) (Ie : ScalarInstance)
    (calls : List (Fin l.imp.exports.length × List IVal)) (outs : List (Option (List IVal))) :
    (l.toG Ie).sessMoves calls outs ∈ (l.toG Ie).toComp.den (impSem P) ↔
      l.sessMoves calls outs ∈ l.toComp.den (impSem P) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedG.sessMoves_toG_iff P l Ie calls outs

/-- The exporter of `Linked2.toG` meets the exporter interface (proved). -/
theorem toG_adeq (P : Profile) {l : Linked2} (hl : l.Adequate) {Ie : ScalarInstance}
    (hIe : l.exp.mod.IsInst Ie) : (l.toG Ie).exp.Adeq P :=
  Simple.expSpec_adeq P hl.expGood hIe

/-- The wiring of `Linked2.toG` is well typed (proved). -/
theorem toG_wireTy {l : Linked2} (hw : l.WireTy) (Ie : ScalarInstance) : (l.toG Ie).WireTy :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedG.toG_wireTy hw Ie

/-- **`Linked2.sessIR_iff` through `LinkedG`** (proved, every profile). -/
theorem sessIR_iff_viaG (P : Profile) (l : Linked2) (hl : l.Adequate) {Ie Ii : ScalarInstance}
    (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii)
    (calls : List (Fin l.imp.exports.length × List IVal)) (outs : List (Option (List IVal)))
    (ht : SimpleI.TypedCalls l.imp calls) (hlen : calls.length = outs.length) :
    l.sessMoves calls outs ∈ l.toComp.den (impSem P) ↔
      ∃ u' π' : Store Nat, l.SessSpec P Ie Ii Ii.store Ie.store calls outs u' π' :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedG.linked2_sessIR_iff P l hl hIe hIi calls outs
    ht hlen

end Linked2

/-! ## Step 3: a linked component is an exporter; chains -/

/-- **A linked component meets the exporter interface** (proved, every profile): its sessions
are the linked `SessSpec` rounds. -/
theorem LinkedG.toExp_adeq {P : Profile} {g : LinkedG} {Ii : ScalarInstance}
    (he : g.exp.Adeq P) (hi : g.imp.Good) (hIi : g.imp.mod.IsInst Ii) (hw : g.WireTy) :
    (g.toExp Ii).Adeq P :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedG.toExp_adeq he hi hIi hw

/-- **Chains of exporters meet the exporter interface** (proved, by induction). -/
theorem chainExp_adeq (P : Profile) {e : ExpSpec} {bs : List (SimpleI × List Nat)}
    {Is : List ScalarInstance} (he : e.Adeq P) (h : ChainOk e bs Is) : (chainExp e bs Is).Adeq P :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedG.chain_adeq P e bs Is he h

/-- The IR component of a chain's specification (proved). -/
theorem chainExp_comp {e : ExpSpec} {bs : List (SimpleI × List Nat)} {Is : List ScalarInstance}
    (h : ChainOk e bs Is) : (chainExp e bs Is).comp = chainComp e.comp bs :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedG.chain_comp e bs Is h

namespace LinkedN

variable {n : LinkedN} {Ib : ScalarInstance} {Is : List ScalarInstance}

/-- The IR component of the chain's specification is the chain's IR component (proved). -/
theorem spec_comp (h : ChainOk (Simple.expSpec n.base Ib) n.links Is) :
    (n.spec Ib Is).comp = n.toComp :=
  chainExp_comp h

/-- **A chain meets the exporter interface** (proved, every profile). -/
theorem adeq (P : Profile) (hb : n.base.Good) (hIb : n.base.mod.IsInst Ib)
    (h : ChainOk (Simple.expSpec n.base Ib) n.links Is) : (n.spec Ib Is).Adeq P :=
  chainExp_adeq P (Simple.expSpec_adeq P hb hIb) h

/-- **Finite adequacy of a chain, IR side** (proved, every profile): the plays of complete
rounds of typed calls of the chain's IR component are exactly the sessions of its
specification. -/
theorem sessIR_iff (P : Profile) (hb : n.base.Good) (hIb : n.base.mod.IsInst Ib)
    (h : ChainOk (Simple.expSpec n.base Ib) n.links Is) (M : List URound)
    (hM : ∀ r ∈ M, (n.spec Ib Is).Typed r) :
    uMoves M ∈ n.toComp.denU (impSem P) ↔ ∃ s', (n.spec Ib Is).Run P (n.spec Ib Is).init M s' := by
  rw [← spec_comp h]
  exact ⟨(adeq P hb hIb h).bwd M hM, fun ⟨s', hs⟩ => (adeq P hb hIb h).fwd M s' hs⟩

end LinkedN

end Silmaril.Wasm.Component.Reference
