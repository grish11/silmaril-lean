module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Native.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Terminal.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Native.Normalize

public section

open Silmaril.Isotope Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation AbortEquiv)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Native.Proofs

variable {n : Nat} {F : Family n} {S T B : Code} {ε : Type} [HasEff (Opcode F) ε]
  [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε] {e : ε}

local notation "Ops" => Opcode F
local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))
local notation "D" => Ty.denote (Lifted carriers)
local notation "γ" => (fun x : Empty => x.elim)
local notation "ρ₀" => (fun i : Fin 0 => i.elim0)

theorem denote_eq_run (p : Program F S B e) (d : Derivation Ops Free .nil p.native B.ty)
    (P : PureMaps (Φ := Ops) (ε := ε) carriers) (visible : ∀ f : Ops, ¬ IsPure (⊥ : ε) f) :
    d.denote D (instructions carriers P) γ ρ₀ = p.table.run p.start := by
  obtain ⟨a, b, ha, hb, ta, tb, normalizes⟩ := lower_rendering p
  obtain ⟨da⟩ := Derivation.ofHasType ta.1
  obtain ⟨db⟩ := Derivation.ofHasType tb.1
  exact (sound carriers P normalizes d (da.iter db) ρ₀).trans
    (loop_denote P visible p.table p.effects p.start ha hb da db)

theorem abortEquiv_iff_run_eq (p : Program F S B e) (q : Program F T B e)
    (P : PureMaps (Φ := Ops) (ε := ε) carriers) (visible : ∀ f : Ops, ¬ IsPure (⊥ : ε) f) :
    AbortEquiv (⊥ : ε) Free .nil p.native q.native B.ty ↔ p.table.run p.start = q.table.run q.start := by
  refine ⟨fun native => ?_, fun observed => ?_⟩
  · obtain ⟨dp⟩ := Derivation.ofHasType (program_typed p).1
    obtain ⟨dq⟩ := Derivation.ofHasType (program_typed q).1
    exact (denote_eq_run p dp P visible).symm.trans
      ((sound carriers P native dp dq ρ₀).trans (denote_eq_run q dq P visible))
  · obtain ⟨a, b, ha, hb, _, _, hp⟩ := lower_rendering p
    obtain ⟨a', b', ha', hb', _, _, hq⟩ := lower_rendering q
    obtain ⟨al, ar, bl, br, hal, har, hbl, hbr, _, _, bridge⟩ :=
      Terminal.replay_of_run_eq (s := p.start) (t := q.start) P visible observed p.effects p.iterative
    have sameA := Option.some.inj (hal.symm.trans ha)
    have sameA' := Option.some.inj (har.symm.trans ha')
    have sameB := Option.some.inj (hbl.symm.trans hb)
    have sameB' := Option.some.inj (hbr.symm.trans hb')
    subst al ar bl br
    exact hp.trans (bridge.trans hq.symm)

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Native.Proofs
