module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Institution.Refinement.Plugging.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Thms

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Institution.Refinement

open Silmaril.Elgot
open Comparison

variable {V K F α β : Type}

/-- Independence is equivalent to agreement with resetting the store to any
one chosen external store. -/
theorem storeIndependent_iff (next : Transfer V K α → Part β) (external : V → α) :
    StoreIndependent next ↔ ∀ transfer, next transfer = withExternalStore external next (obs transfer) :=
  ⟨fun independent (label, packet, store) => independent label packet store external,
    fun factor label packet left right => (factor (label, packet, left)).trans
      (factor (label, packet, right)).symm⟩

private theorem bind_mono {A : Type} {lhs rhs : Part A} {next next' : A → Part β}
    (programs : lhs ≤ rhs) (handlers : ∀ result, next result ≤ next' result) :
    (lhs >>= next) ≤ (rhs >>= next') := by
  intro result member
  obtain ⟨input, produced, returned⟩ := Part.mem_bind_iff.mp member
  exact Part.mem_bind (programs input produced) (handlers input result returned)

variable [DecidableEq V] [DecidableEq K]

/-- Plugging is monotone in the mutable program and the continuation. The same
store supplies the initial input on both sides. -/
theorem plugRTL_mono (model : PairModel F Part α) {lhs rhs : RTLClass V K F Part α}
    (programs : rtlSat model lhs rhs) (store : V → α) {next next' : K × α → Part β}
    (handlers : ∀ result, next result ≤ next' result) :
    plugRTL model lhs store next ≤ plugRTL model rhs store next' :=
  bind_mono (programs store) handlers

/-- Plugging is monotone in the lexical program and the continuation. -/
theorem plugSSA_mono (model : PairModel F Part α) {lhs rhs : SSAClass V K F Part α}
    (programs : ssaSat model lhs rhs) (store : V → α) {next next' : K × α → Part β}
    (handlers : ∀ result, next result ≤ next' result) :
    plugSSA model lhs store next ≤ plugSSA model rhs store next' :=
  bind_mono (programs store) handlers

/-- Versioning agrees under every continuation on the common observation. -/
theorem plugSSA_version (model : PairModel F Part α) (program : RTLClass V K F Part α)
    (store : V → α) (next : K × α → Part β) :
    plugSSA model (versionClass program) store next = plugRTL model program store next := by
  simp only [plugSSA, plugRTL, classObserve_version]

theorem plugRTL_deversion [Infinite V] (model : PairModel F Part α) (program : SSAClass V K F Part α)
    (store : V → α) (next : K × α → Part β) :
    plugRTL model (deversionClass program) store next = plugSSA model program store next := by
  simp only [plugSSA, plugRTL, classObserve_deversion]

/-- A store-independent handler of raw RTL factors through the observational
class. The same handler can run from any chosen external store. -/
theorem plugRTLWithStore_eq (model : PairModel F Part α) (graph : CFG V K F) (store external : V → α)
    (next : Transfer V K α → Part β) (independent : StoreIndependent next) :
    plugRTLWithStore model graph store next =
      plugRTL model (Quotient.mk _ graph) store (withExternalStore external next) := by
  change _ = (obs <$> Cyclic.run model.val graph store) >>= withExternalStore external next
  rw [bind_map_left]
  exact bind_congr ((storeIndependent_iff next external).mp independent)

/-- A common store-independent handler preserves mutable refinement even
when it is called with the raw final transfer. -/
theorem plugRTLWithStore_mono (model : PairModel F Part α) {lhs rhs : CFG V K F}
    (programs : rtlSat model (Quotient.mk _ lhs) (Quotient.mk _ rhs)) (store : V → α)
    (next : Transfer V K α → Part β) (independent : StoreIndependent next) :
    plugRTLWithStore model lhs store next ≤ plugRTLWithStore model rhs store next := by
  rw [plugRTLWithStore_eq model lhs store store next independent,
    plugRTLWithStore_eq model rhs store store next independent]
  exact plugRTL_mono model programs store (fun _ => le_rfl)

/-- For a packet-closed table, resuming with the carried store agrees with
the lexical continuation using any external environment. -/
theorem resumeRTL_eq_resumeSSA (model : Model F Part α) (table : List (K × Block V K F))
    (closed : RoundTrip.PacketClosedTable table) (external : V → α) (transfer : Transfer V K α) :
    resumeRTL model table transfer = resumeSSA model table external (obs transfer) :=
  Cyclic.iter_obs_of_step_encoding model table obs _ (RoundTrip.step_packetClosed_obs model table closed external)
    transfer

/-- All mutable stores are interchangeable when entering a packet-closed
continuation table. -/
theorem resumeRTL_storeIndependent (model : Model F Part α) (table : List (K × Block V K F))
    (closed : RoundTrip.PacketClosedTable table) : StoreIndependent (resumeRTL model table) :=
  fun label packet left right =>
    (resumeRTL_eq_resumeSSA model table closed left (label, packet, left)).trans
      (resumeRTL_eq_resumeSSA model table closed left (label, packet, right)).symm

/-- A common packet-closed cyclic continuation preserves refinement even
when the mutable machine passes its final store across the boundary. -/
theorem plugPacketTable_mono (model : PairModel F Part α) {lhs rhs : CFG V K F}
    (programs : rtlSat model (Quotient.mk _ lhs) (Quotient.mk _ rhs)) (store : V → α)
    (table : List (K × Block V K F)) (closed : RoundTrip.PacketClosedTable table) :
    plugRTLWithStore model lhs store (resumeRTL model.val table) ≤
      plugRTLWithStore model rhs store (resumeRTL model.val table) :=
  plugRTLWithStore_mono model programs store _ (resumeRTL_storeIndependent model.val table closed)

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Institution.Refinement
