module

public import Silmaril.Wasm.Abstract.NodeLegalComp.Defs
public import Silmaril.Wasm.Abstract.NodeLegal.Thms
public import Silmaril.Games.DivCompAns.Thms
public import Silmaril.Wasm.Abstract.SRelabelPull.Thms

/-!
# Host-answer domains through the component coercions (proofs)

See `Silmaril.Wasm.Abstract.NodeLegalComp.Thms`.
-/

public section

namespace Silmaril.Proofs.Wasm.Abstract.NodeLegalComp

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Games.Abstract.StratSession (threadS)
open Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.InstSession (ssig instSession spullD srelabel semOfSD spullD_eq_pull
  spullD_mono)
open Silmaril.Wasm.Abstract.NodeLegal (instTripleQ RoundLegal LegalPlayD)
open Silmaril.Wasm.Abstract.NodeLegalComp
open Silmaril.Wasm.Component (CoreIface)
open Silmaril.Wasm.Component.Reference (NumInstance importH exportH payloadAnswer)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)
open Silmaril.Wasm.Numerics (Profile)

variable {I : ScalarInstance} {Q : Store Nat → Result → Prop}

/-- A log of answers legal at every store is legal in the round. -/
theorem roundLegal_of {P : Profile} {s : Store Nat} {a : I.F.Op} {c : List (Call I.E)}
    (h : ∀ x ∈ c, AnsLegal I Q x.1 x.2) : RoundLegal I P Q s a c := by
  rintro c₁ x c₂ rfl s' _ -
  exact h x (List.mem_append_right _ List.mem_cons_self) s'

/-- A play of the instance session whose import answers are legal at every store is legal. -/
theorem legalPlayD_of_lAnsIn {P : Profile} {s₀ : Store Nat}
    {q : List (Move I.E (ssig I.exports))} (hq : LAnsIn (AnsLegal I Q) q) :
    LegalPlayD I P Q s₀ q :=
  SessionLegal.sLegal_of_lAnsIn (fun _ _ _ h => roundLegal_of h) hq

/-- Relabelling the answers above keeps the answers below. -/
theorem lAnsIn_map_srelabel {E : Sig.{0}} {ts : List FnType} {R : (m : E.Op) → E.Ar m → Prop}
    {p : List (Move E (ifaceSig ts))} : LAnsIn R (p.map srelabel) ↔ LAnsIn R p := by
  constructor
  · intro h m n hm
    exact h m n (List.mem_map_of_mem (f := srelabel) hm)
  · intro h m n hm
    obtain ⟨x, hx, he⟩ := List.mem_map.1 hm
    rcases x with e | e
    · cases he
      exact h _ _ hx
    · cases e <;> simp [srelabel] at he

/-- The `R`-answered part is kept by the read-back on `ifaceSig`. -/
theorem ansPart_spullD {E : Sig.{0}} {ts : List FnType} {R : (m : E.Op) → E.Ar m → Prop}
    {σ' σ : DStrategy E (ssig ts)} (h : σ'.AnsPart R σ) : (spullD σ').AnsPart R (spullD σ) := by
  refine ⟨spullD_mono h.1, fun p hp hl => ?_, fun p hp hl => h.2.2.1 _ hp
    (lAnsIn_map_srelabel.2 hl), fun J ⟨hJ, hi⟩ hl => ⟨hJ, h.2.2.2 _ hi ?_⟩⟩
  · rw [spullD_eq_pull] at hp ⊢
    exact h.2.1 _ hp (lAnsIn_map_srelabel.2 hl)
  · rintro _ ⟨p, hp, rfl⟩
    exact lAnsIn_map_srelabel.2 (hl p hp)

/-- `payloadAnswer` is never an exception. -/
theorem toResult_payloadAnswer_ne (ft : FnType) (r : Option Silmaril.Wasm.Component.Payload)
    (a : Nat) : (payloadAnswer ft r).toResult ≠ .throw a := by
  unfold payloadAnswer
  split
  · split <;> simp [Answer.toResult]
  · simp [Answer.toResult]

/-- `importH m` answers every import call legally at every store. -/
theorem answersIn_importH (hQ : NonExnLegal Q) (m : NumInstance) :
    (DStrategy.ofHandler (importH m)).AnswersIn (AnsLegal m.inst Q) :=
  DStrategy.answersIn_ofHandler fun _ r s => hQ s _ (toResult_payloadAnswer_ne _ r)

/-- The node strategy only sees the part of the session answered legally at every store. -/
theorem semOfSD_eq_of_ansPart (hQ : NonExnLegal Q) {m : NumInstance}
    {σ' σ : DStrategy m.inst.E (ssig m.inst.exports)} (h : σ'.AnsPart (AnsLegal m.inst Q) σ) :
    semOfSD m σ' = semOfSD m σ :=
  DStrategy.comp_eq_of_ansPart (answersIn_importH hQ m)
    (DStrategy.ansPart_comp (ansPart_spullD h) _)

/-- The restricted session is the part of the instance session answered legally at every store. -/
theorem ansPart_threadS_instTripleQ {o : GrowOracle} (s₀ : Store Nat) :
    (threadS (instTripleQ I (profile o) Q) s₀).AnsPart (AnsLegal I Q)
      (instSession I (profile o) s₀) :=
  ⟨Silmaril.Wasm.Abstract.NodeLegal.threadS_instTripleQ_le s₀,
    fun _ hq hl => Silmaril.Wasm.Abstract.NodeLegal.mem_threadS_instTripleQ.2
      ⟨hq, (legalPlayD_of_lAnsIn hl).1⟩,
    fun _ hq hl => Silmaril.Wasm.Abstract.NodeLegal.div_threadS_instTripleQ.2
      ⟨hq, legalPlayD_of_lAnsIn hl⟩,
    fun _ hJ hl => Silmaril.Wasm.Abstract.NodeLegal.inf_threadS_instTripleQ.2
      ⟨hJ, fun q hq => (legalPlayD_of_lAnsIn (hl q hq)).1⟩⟩

/-- The hidden middle play of a node interaction is answered legally at every store. -/
theorem lAnsIn_of_importH (hQ : NonExnLegal Q) {m : NumInstance} {G : Sig.{0}}
    {p : List (Move (CoreIface.sig m.imports) G)}
    {u : List (Move (CoreIface.sig m.imports) (ifaceSig m.inst.imports))}
    {v : List (Move (ifaceSig m.inst.imports) G)}
    (hu : u ∈ Strategy.ofHandler (importH m)) (huv : Zip u v p) :
    LAnsIn (AnsLegal m.inst Q) v :=
  lAnsIn_of_zip_right huv (answersIn_importH hQ m _ hu)

/-- **Every hidden interaction of a node is legal at every importer point.** -/
theorem witLegal_of_nodeWit (hQ : NonExnLegal Q) {P : Profile} {m : NumInstance}
    {s₀ : Store Nat} {p u v a b} (h : NodeWit P m s₀ p u v a b) : WitLegal P Q m s₀ a := by
  obtain ⟨hu, huv, hab, -, -⟩ := h
  exact legalPlayD_of_lAnsIn
    (lAnsIn_map_srelabel.2 (lAnsIn_of_zip_left hab (lAnsIn_of_importH hQ hu huv)))

/-- **The coherent hidden interaction of an infinite node play**: when the upper side of an
infinite node interaction moves forever, its limit is the limit of one inner infinite interaction
of the read-back instance session with `exportH m`, all of whose stages are answered legally at
every store and whose hidden instance plays are legal at every importer point. -/
theorem inf_inner_lift (hQ : NonExnLegal Q) {P : Profile} {m : NumInstance} {s₀ : Store Nat}
    (i : DStrategy.InfInteraction (DStrategy.ofHandler (importH m))
      ((spullD (instSession m.inst P s₀)).comp (DStrategy.ofHandler (exportH m))))
    (hu : i.t.Unbounded) :
    ∃ j : DStrategy.InfInteraction (spullD (instSession m.inst P s₀))
        (DStrategy.ofHandler (exportH m)),
      j.p.Unbounded ∧ j.p.lim = i.t.lim ∧ (∀ n, LAnsIn (AnsLegal m.inst Q) (j.p n)) ∧
        ∀ n, WitLegal P Q m s₀ (j.s n) := by
  obtain ⟨j, hju, hj⟩ := i.lim_t hu
  have hp : ∀ n, LAnsIn (AnsLegal m.inst Q) (j.p n) := by
    intro n
    obtain ⟨k, hk⟩ : j.p n ∈ i.t.lim := hj ▸ Chain.mem_lim_self j.p n
    exact lAnsIn_of_prefix
      (lAnsIn_of_zip_right (i.zip k) (answersIn_importH hQ m _ (i.mem_s k))) hk
  exact ⟨j, hju, hj.symm, hp, fun n =>
    legalPlayD_of_lAnsIn (lAnsIn_map_srelabel.2 (lAnsIn_of_zip_left (j.zip n) (hp n)))⟩

end Silmaril.Proofs.Wasm.Abstract.NodeLegalComp
