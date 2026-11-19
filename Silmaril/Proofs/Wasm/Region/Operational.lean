module

public import Silmaril.Wasm.Region.Operational.Defs
public import Silmaril.Wasm.Region.Thms
public import Silmaril.Semantics.Region.Semantic.Thms

@[expose] public section
namespace Silmaril.Wasm.Region.Proofs
open Silmaril.Semantics.Region

 theorem operational_allows {body : Expr} {b : Cfg.BlockId} {s : Cfg.Segment} {t : Cfg.Target}
    (h : (candidateTargets body b s).Allows t ∨ t = .trap ∨ Cfg.Machine.CatchEdge body b t) :
    (operationalTargets body b s).Allows t := by
  unfold operationalTargets
  split
  · rename_i root
    rcases h with h | rfl | ⟨tb, a, rest, sg, bt, cs, c, cl, path, _⟩
    · cases he : candidateTargets body b s with
      | top => trivial
      | finite xs => exact Finset.mem_insert_of_mem (by simpa [he, Targets.Allows] using h)
    · cases candidateTargets body b s <;> simp [Targets.Allows]
    · rw [root] at path
      have := congrArg List.length path
      simp at this
  · trivial

 theorem operational_step {H : Type} {P : Numerics.Profile} {host : Execution.Core.HostSemantics H}
    {C : Abstract.CallRel H} {body : Expr} {b : Cfg.BlockId} {s : Cfg.Segment}
    {st st' : Cfg.Machine.MState H}
    (lookup : Cfg.lookup body b = some s) (node : st.node = .block b)
    (inv : Cfg.Machine.MInv body st) (step : Cfg.Machine.MStepC P host C body st st') :
    (operationalTargets body b s).Allows st'.node := by
  apply operational_allows
  rcases Cfg.Machine.mstep_edgeC step inv node with edge | trap | caught | ⟨effect, _⟩
  · obtain ⟨s', hs', ht⟩ := edge
    have : s' = s := Option.some.inj (hs'.symm.trans lookup)
    subst s'
    exact .inl (candidate_covers body b s _ (.inl ht))
  · exact .inr (.inl trap)
  · exact .inr (.inr caught)
  · obtain ⟨s', hs', ht⟩ := effect
    have : s' = s := Option.some.inj (hs'.symm.trans lookup)
    subst s'
    exact .inl (candidate_covers body b s _ (.inr ht))

 theorem operational_sound {H : Type} {P : Numerics.Profile}
    {host : Execution.Core.HostSemantics H} {C : Abstract.CallRel H} {body : Expr}
    {A : Cfg.Machine.MState H → Prop} {U X : Cfg.Target → Prop}
    (admit : ∀ st, A st → Cfg.Machine.MInv body st)
    (covered : ∀ st : Cfg.Machine.MState H, Cfg.Machine.MInv body st → U st.node →
      ∃ b s, st.node = .block b ∧ Cfg.lookup body b = some s)
    (outward : ∀ b s, Cfg.lookup body b = some s → U (.block b) → ∀ t,
      (operationalTargets body b s).Allows t → ¬ U t → X t) :
    Sound (system P host C body) A U X := by
  apply Silmaril.Semantics.Region.local_sound (T := system P host C body) (U := U) (X := X) (D := Cfg.Machine.MInv body) (B := fun st => X st.node) _ admit
    (fun _ h => h)
  intro st es st' inv inside edge
  obtain ⟨b, s, node, lookup⟩ := covered st inv inside
  refine ⟨fun _ => Cfg.Machine.mstep_invC edge.2 inv, ?_⟩
  intro outside
  exact outward b s lookup (node ▸ inside) st'.node
    (operational_step lookup node inv edge.2) outside

end Silmaril.Wasm.Region.Proofs
