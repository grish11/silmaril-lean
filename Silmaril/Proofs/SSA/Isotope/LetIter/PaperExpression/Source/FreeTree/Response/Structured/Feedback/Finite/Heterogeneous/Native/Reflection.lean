module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Native.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Terminal.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Native.Normalize

public section

open Silmaril.Isotope Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless (Tm HasTypeEffect Derivation AbortEquiv)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Native.Proofs

variable {n : Nat} {F : Family n} {S T B : Code} {ε : Type} [HasEff (Opcode F) ε]
  [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε] {e : ε}

local notation "Ops" => Opcode F
local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))
local notation "D" => Ty.denote (Lifted carriers)
local notation "γ" => (fun x : Empty => x.elim)
local notation "ρ₀" => (fun i : Fin 0 => i.elim0)

/-- The exact lowering and native equation used to compare a program with
its extracted one-request table. -/
@[expose] def Renders (M : Table F S B) (s : S.Value) (t : Tm Empty Ops 0) (e : ε) : Prop :=
  ∃ (a : Tm Empty Ops 0) (b : Tm Empty Ops 1),
    (S.literal s).toLetIter 0 = some a ∧ M.source.toLetIter 1 = some b ∧
    HasTypeEffect Free .nil a S.ty e ∧ HasTypeEffect Free (.snoc .nil S.ty) b (Code.sum B S).ty e ∧
    AbortEquiv (⊥ : ε) Free .nil t (.iter a b) B.ty

theorem renders_denote {M : Table F S B} {s : S.Value} {t : Tm Empty Ops 0}
    (h : Renders M s t e) (d : Derivation Ops Free .nil t B.ty)
    (P : PureMaps (Φ := Ops) (ε := ε) carriers) (visible : ∀ f : Ops, ¬ IsPure (⊥ : ε) f)
    (hf : ∀ f : Ops, instrEff f ≤ e) :
    d.denote D (instructions carriers P) γ ρ₀ = M.run s := by
  obtain ⟨a, b, ha, hb, ta, tb, normalizes⟩ := h
  obtain ⟨da⟩ := Derivation.ofHasType ta.1
  obtain ⟨db⟩ := Derivation.ofHasType tb.1
  exact (sound carriers P normalizes d (da.iter db) ρ₀).trans (loop_denote P visible M hf s ha hb da db)

theorem renders_reflect {M : Table F S B} {N : Table F T B} {s : S.Value} {t : T.Value} {x y : Tm Empty Ops 0}
    (left : Renders M s x e) (right : Renders N t y e)
    (P : PureMaps (Φ := Ops) (ε := ε) carriers) (visible : ∀ f : Ops, ¬ IsPure (⊥ : ε) f)
    (hf : ∀ f : Ops, instrEff f ≤ e) (he : IsIterative e)
    (observed : M.run s = N.run t) : AbortEquiv (⊥ : ε) Free .nil x y B.ty := by
  obtain ⟨a, b, ha, hb, _, _, hp⟩ := left
  obtain ⟨a', b', ha', hb', _, _, hq⟩ := right
  obtain ⟨al, ar, bl, br, hal, har, hbl, hbr, _, _, bridge⟩ :=
    Terminal.replay_of_run_eq (s := s) (t := t) P visible observed hf he
  have sameA := Option.some.inj (hal.symm.trans ha)
  have sameA' := Option.some.inj (har.symm.trans ha')
  have sameB := Option.some.inj (hbl.symm.trans hb)
  have sameB' := Option.some.inj (hbr.symm.trans hb')
  subst al ar bl br
  exact hp.trans (bridge.trans hq.symm)

theorem denote_eq_run (p : Program F S B e) (d : Derivation Ops Free .nil p.native B.ty)
    (P : PureMaps (Φ := Ops) (ε := ε) carriers) (visible : ∀ f : Ops, ¬ IsPure (⊥ : ε) f) :
    d.denote D (instructions carriers P) γ ρ₀ = p.table.run p.start :=
  renders_denote (lower_rendering p) d P visible p.effects

theorem abortEquiv_iff_run_eq (p : Program F S B e) (q : Program F T B e)
    (P : PureMaps (Φ := Ops) (ε := ε) carriers) (visible : ∀ f : Ops, ¬ IsPure (⊥ : ε) f) :
    AbortEquiv (⊥ : ε) Free .nil p.native q.native B.ty ↔ p.table.run p.start = q.table.run q.start := by
  refine ⟨fun native => ?_, fun observed => ?_⟩
  · obtain ⟨dp⟩ := Derivation.ofHasType (program_typed p).1
    obtain ⟨dq⟩ := Derivation.ofHasType (program_typed q).1
    exact (denote_eq_run p dp P visible).symm.trans
      ((sound carriers P native dp dq ρ₀).trans (denote_eq_run q dq P visible))
  · exact renders_reflect (lower_rendering p) (lower_rendering q) P visible p.effects p.iterative observed

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Native.Proofs
