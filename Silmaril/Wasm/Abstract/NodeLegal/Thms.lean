module

public import Silmaril.Wasm.Abstract.NodeLegal.Defs
public import Silmaril.Wasm.Abstract.InstSession.Thms
public import Silmaril.Games.Abstract.SessionLegal.Thms
public import Silmaril.Wasm.Abstract.InstSessionD.Thms
public import Silmaril.Wasm.Abstract.SRelabelPull.Thms
public import Silmaril.Wasm.Abstract.NodeDiv.Thms
import Silmaril.Proofs.Wasm.Abstract.NodeLegal.Basic

/-!
# Host-answer domains of an instance session: theorems

At a deterministic profile `profile o`, for any host-answer domain `Q`:

**The domain on Core events is the domain on the instance game** (`instTripleQ_agree`): at every
store, the instance triple restricted by `Q` on its Core events (`instTripleQ`) has exactly the
finished behaviours, call prefixes (`StratObs.satP`) and productive streams of the instance triple
`instTripleS I (profile o)` whose logs are `RoundLegal` (`SessionLegal.restrictLog`). The proof
reads each Core event's store as the store of the instance's hidden state `.waiting` at that call
(the hidden state after a play is unique at `profile o`, `ScalarInstance.Path.functional`); the
instance triple is saturated (`satP_instTripleS_sub`), so a legal call prefix of it is a pending
call.

**The restricted session is the exact legal pullback of the instance session**
`InstSession.instSession I (profile o) s₀`, on every observation of the session strategy:

* `mem_threadS_instTripleQ`: finite plays are the plays of the instance session that are legal
  before each Proponent move (`LegalPlay`);
* `pending_threadS_instTripleQ`: a play ending in an import call (a pending call) is a pending
  play of the instance session whose prefix is legal, its end included (`LegalPlayD`);
* `div_threadS_instTripleQ`: divergences are the divergences of the instance session that are
  `LegalPlayD`;
* `inf_threadS_instTripleQ`: infinite plays are the infinite plays of the instance session all of
  whose finite prefixes are `LegalPlay`;
* `threadS_instTripleQ_le`: the restricted session refines the instance session.

Opponent's answers are not restricted by the strategy (it is receptive): a play may end in an
answer outside `Q`; then the instance makes no further move in the restricted session.

**On the node's interface `ifaceSig`** (`InstSession.spullD`, the read-back along `srelabel`):
`mem_spullD_instTripleQ`, `div_spullD_instTripleQ`, `inf_spullD_instTripleQ`, the same three
pullbacks, legality read on the relabelled play.

**Through the coercions** of a numeric instance `m` (`InstSession.semOfSD m`, between
`importH m` and `exportH m`; the node strategy of `core3SemD`): a play, or a divergence, of
`semOfSD m (threadS (instTripleQ …) s₀)` is the visible part of an interaction of `importH m`, the
read-back instance session and `exportH m` whose **hidden instance play** is legal
(`mem_semOfSD_instTripleQ`, `div_semOfSD_instTripleQ`). Legality is a property of the hidden
instance play (the call stores are hidden), so it is stated on the interaction witness. Infinite
plays at this level go through `DStrategy.InfInteraction`; only `semOfSD_instTripleQ_le` is stated
for them here.
-/

public section

namespace Silmaril.Wasm.Abstract.NodeLegal

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Games.Abstract.StratSession (threadS)
open Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.InstSession (Res ssig instTripleS instSession spullD semOfSD srelabel)
open Silmaril.Wasm.Component (CoreIface)
open Silmaril.Wasm.Component.Reference (NumInstance importH exportH)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)
open Silmaril.Wasm.Numerics (Profile)

variable {I : ScalarInstance} {Q : Store Nat → Result → Prop}

/-- `RoundLegal` is closed under prefixes. -/
theorem roundLegal_prefixClosed {P : Profile} : SessionLegal.PrefixClosed (RoundLegal I P Q) :=
  Silmaril.Proofs.Wasm.Abstract.NodeLegal.roundLegal_prefixClosed

/-- **The instance triple is saturated**: its call prefixes are pending calls. -/
theorem satP_instTripleS_sub {P : Profile} {s : Store Nat} {a : I.F.Op}
    {x : List (Call I.E) × I.E.Op} (h : x ∈ satP (instTripleS I P) s a) :
    x ∈ (instTripleS I P).2.1 s a :=
  Silmaril.Proofs.Wasm.Abstract.NodeLegal.satP_instTripleS_sub h

variable {o : GrowOracle}

/-- **The domain on Core events is the domain on the instance game**: at every store, the
restricted instance triple and the `RoundLegal` part of the instance triple have the same finished
behaviours, call prefixes and productive streams. -/
theorem instTripleQ_agree (s : Store Nat) :
    (instTripleQ I (profile o) Q).1 s =
        (SessionLegal.restrictLog (RoundLegal I (profile o) Q) (instTripleS I (profile o))).1 s ∧
      satP (instTripleQ I (profile o) Q) s =
        satP (SessionLegal.restrictLog (RoundLegal I (profile o) Q) (instTripleS I (profile o))) s ∧
      (instTripleQ I (profile o) Q).2.2 s =
        (SessionLegal.restrictLog (RoundLegal I (profile o) Q) (instTripleS I (profile o))).2.2 s :=
  Silmaril.Proofs.Wasm.Abstract.NodeLegal.agree s

/-- The restricted session is the session of the `RoundLegal` part of the instance triple. -/
theorem threadS_instTripleQ_eq (s₀ : Store Nat) :
    threadS (instTripleQ I (profile o) Q) s₀ =
      threadS (SessionLegal.restrictLog (RoundLegal I (profile o) Q) (instTripleS I (profile o)))
        s₀ :=
  Silmaril.Proofs.Wasm.Abstract.NodeLegal.threadS_eq s₀

/-- **The restricted session refines the instance session.** -/
theorem threadS_instTripleQ_le (s₀ : Store Nat) :
    threadS (instTripleQ I (profile o) Q) s₀ ≤ instSession I (profile o) s₀ := by
  rw [threadS_instTripleQ_eq]
  exact SessionLegal.threadS_restrictLog_le roundLegal_prefixClosed

/-- **Finite plays: the restricted session is the legal pullback of the instance session.** -/
theorem mem_threadS_instTripleQ {s₀ : Store Nat} {q : List (Move I.E (ssig I.exports))} :
    q ∈ (threadS (instTripleQ I (profile o) Q) s₀).toStrategy ↔
      q ∈ (instSession I (profile o) s₀).toStrategy ∧ LegalPlay I (profile o) Q s₀ q := by
  rw [threadS_instTripleQ_eq]
  exact SessionLegal.mem_threadS_restrictLog (InstSession.storeDet_instTripleS o)
    InstSession.noPlainTrap_instTripleS roundLegal_prefixClosed

/-- **Pending calls**: a play ending in an import call is in the restricted session iff it is in
the instance session and legal up to the call. -/
theorem pending_threadS_instTripleQ {s₀ : Store Nat} {q : List (Move I.E (ssig I.exports))}
    {e : I.E.Op} :
    q ++ [.inl (.ask e)] ∈ (threadS (instTripleQ I (profile o) Q) s₀).toStrategy ↔
      q ++ [.inl (.ask e)] ∈ (instSession I (profile o) s₀).toStrategy ∧
        LegalPlayD I (profile o) Q s₀ q := by
  rw [mem_threadS_instTripleQ]
  exact and_congr_right fun _ => SessionLegal.pLegal_snoc trivial

/-- **Divergences: the restricted session is the legal pullback of the instance session.** -/
theorem div_threadS_instTripleQ {s₀ : Store Nat} {q : List (Move I.E (ssig I.exports))} :
    q ∈ (threadS (instTripleQ I (profile o) Q) s₀).div ↔
      q ∈ (instSession I (profile o) s₀).div ∧ LegalPlayD I (profile o) Q s₀ q := by
  rw [threadS_instTripleQ_eq]
  exact SessionLegal.div_threadS_restrictLog (InstSession.storeDet_instTripleS o)
    InstSession.noPlainTrap_instTripleS roundLegal_prefixClosed

/-- **Infinite plays: the restricted session is the legal pullback of the instance session.** -/
theorem inf_threadS_instTripleQ {s₀ : Store Nat} {J : Set (List (Move I.E (ssig I.exports)))} :
    J ∈ (threadS (instTripleQ I (profile o) Q) s₀).inf ↔
      J ∈ (instSession I (profile o) s₀).inf ∧ ∀ q ∈ J, LegalPlay I (profile o) Q s₀ q := by
  rw [threadS_instTripleQ_eq]
  exact SessionLegal.inf_threadS_restrictLog (InstSession.storeDet_instTripleS o)
    InstSession.noPlainTrap_instTripleS roundLegal_prefixClosed

/-! ## On the node's interface -/

/-- **Finite plays read back on `ifaceSig`.** -/
theorem mem_spullD_instTripleQ {s₀ : Store Nat} {p : List (Move I.E I.F)} :
    p ∈ (spullD (threadS (instTripleQ I (profile o) Q) s₀)).toStrategy ↔
      p ∈ (spullD (instSession I (profile o) s₀)).toStrategy ∧
        LegalPlay I (profile o) Q s₀ (p.map srelabel) := by
  simp only [InstSession.spullD_eq_pull, DStrategy.mem_toStrategy_pull]
  exact mem_threadS_instTripleQ

/-- **Divergences read back on `ifaceSig`.** -/
theorem div_spullD_instTripleQ {s₀ : Store Nat} {p : List (Move I.E I.F)} :
    p ∈ (spullD (threadS (instTripleQ I (profile o) Q) s₀)).div ↔
      p ∈ (spullD (instSession I (profile o) s₀)).div ∧
        LegalPlayD I (profile o) Q s₀ (p.map srelabel) := by
  simp only [InstSession.spullD_eq_pull, DStrategy.mem_div_pull]
  exact div_threadS_instTripleQ

/-- **Infinite plays read back on `ifaceSig`.** -/
theorem inf_spullD_instTripleQ {s₀ : Store Nat} {J : Set (List (Move I.E I.F))} :
    J ∈ (spullD (threadS (instTripleQ I (profile o) Q) s₀)).inf ↔
      J ∈ (spullD (instSession I (profile o) s₀)).inf ∧
        ∀ p ∈ J, LegalPlay I (profile o) Q s₀ (p.map srelabel) := by
  rw [InstSession.spullD_eq_pull, InstSession.spullD_eq_pull, DStrategy.mem_inf_pull,
    DStrategy.mem_inf_pull, inf_threadS_instTripleQ]
  constructor
  · rintro ⟨hJ, hi, hl⟩
    exact ⟨⟨hJ, hi⟩, fun p hp => hl _ ⟨p, hp, rfl⟩⟩
  · rintro ⟨⟨hJ, hi⟩, hl⟩
    exact ⟨hJ, hi, by rintro _ ⟨p, hp, rfl⟩; exact hl p hp⟩

/-! ## Through the coercions of a numeric instance -/

/-- **The node strategy of the restricted session refines that of the instance session.** -/
theorem semOfSD_instTripleQ_le (m : NumInstance) (s₀ : Store Nat) :
    semOfSD m (threadS (instTripleQ m.inst (profile o) Q) s₀) ≤
      semOfSD m (instSession m.inst (profile o) s₀) :=
  DStrategy.comp_mono le_rfl
    (DStrategy.comp_mono (InstSession.spullD_mono (threadS_instTripleQ_le s₀)) le_rfl)

/-- **Finite plays of the node strategy**: the visible parts of the interactions through
`importH m` and `exportH m` whose hidden instance play is a legal play of the instance session. -/
theorem mem_semOfSD_instTripleQ {m : NumInstance} {s₀ : Store Nat}
    {p : List (Move (CoreIface.sig m.imports) (CoreIface.sig m.exports))} :
    p ∈ (semOfSD m (threadS (instTripleQ m.inst (profile o) Q) s₀)).toStrategy ↔
      ∃ u ∈ Strategy.ofHandler (importH m), ∃ v, Zip u v p ∧ ∃ a b, Zip a b v ∧
        a ∈ (spullD (instSession m.inst (profile o) s₀)).toStrategy ∧
        LegalPlay m.inst (profile o) Q s₀ (a.map srelabel) ∧ b ∈ Strategy.ofHandler (exportH m) := by
  constructor
  · rintro ⟨u, hu, v, ⟨a, ha, b, hb, hab⟩, huv⟩
    obtain ⟨ha, hl⟩ := mem_spullD_instTripleQ.1 ha
    exact ⟨u, hu, v, huv, a, b, hab, ha, hl, hb⟩
  · rintro ⟨u, hu, v, huv, a, b, hab, ha, hl, hb⟩
    exact ⟨u, hu, v, ⟨a, mem_spullD_instTripleQ.2 ⟨ha, hl⟩, b, hb, hab⟩, huv⟩

/-- **Divergences of the node strategy**: the visible parts of the interactions through
`importH m` and `exportH m` whose hidden instance play is a legal divergence of the instance
session. -/
theorem div_semOfSD_instTripleQ {m : NumInstance} {s₀ : Store Nat}
    {p : List (Move (CoreIface.sig m.imports) (CoreIface.sig m.exports))} :
    p ∈ (semOfSD m (threadS (instTripleQ m.inst (profile o) Q) s₀)).div ↔
      ∃ u v, Zip u v p ∧ u ∈ Strategy.ofHandler (importH m) ∧ ∃ a b, Zip a b v ∧
        a ∈ (spullD (instSession m.inst (profile o) s₀)).div ∧
        LegalPlayD m.inst (profile o) Q s₀ (a.map srelabel) ∧ b ∈ Strategy.ofHandler (exportH m) := by
  rw [NodeDiv.div_semOfSD]
  constructor
  · rintro ⟨u, v, huv, hu, a, b, hab, ha, hb⟩
    obtain ⟨ha, hl⟩ := div_spullD_instTripleQ.1 ha
    exact ⟨u, v, huv, hu, a, b, hab, ha, hl, hb⟩
  · rintro ⟨u, v, huv, hu, a, b, hab, ha, hl, hb⟩
    exact ⟨u, v, huv, hu, a, b, hab, div_spullD_instTripleQ.2 ⟨ha, hl⟩, hb⟩

end Silmaril.Wasm.Abstract.NodeLegal
