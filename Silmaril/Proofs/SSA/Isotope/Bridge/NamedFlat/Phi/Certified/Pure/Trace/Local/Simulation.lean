module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Local.Defs
public import Silmaril.Semantics.ITree.Trace.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.LocalTrace

open Silmaril.Elgot (iter)
open Silmaril.Isotope
open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph)
open Silmaril.Isotope.Bridge.NamedFlat.Phi
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture
open LambdaSSA.Semantics.Interaction (Primitive)
open Silmaril.Elgot.ITree
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local

universe u
variable {E : Type u → Type u} {A B C : Type (u + 1)}
  {f : A → Tree E (B ⊕ A)} {g : C → Tree E (B ⊕ C)}
  {boundary : A → C → Prop} {related : Tree E (B ⊕ A) → Tree E (B ⊕ C) → Prop}

private theorem silent_resume {s t : Tree E (B ⊕ C)} (silent : Silent g s t) :
    resume g s = resume g t := by
  induction silent with
  | refl => rfl
  | @more p t _ ih =>
    calc
      resume g (pure (.inr p)) = iter g p := by simp [resume]
      _ = resume g (g p) := (resume_body _ _).symm
      _ = resume g t := ih

private inductive RootMatch (f : A → Tree E (B ⊕ A)) (g : C → Tree E (B ⊕ C))
    (related : Tree E (B ⊕ A) → Tree E (B ⊕ C) → Prop) :
    Visible E B (Tree E B) → Visible E B (Tree E B) → Prop where
  | ret (value : B) : RootMatch f g related (.ret value) (.ret value)
  | vis {R : Type u} (event : E R) {k : R → Tree E (B ⊕ A)} {l : R → Tree E (B ⊕ C)}
      (replies : ∀ reply, related (k reply) (l reply)) :
      RootMatch f g related (.vis event (fun r => resume f (k r)))
        (.vis event (fun r => resume g (l r)))

private theorem normalize_pure (x : B ⊕ A) :
    normalizeStep f (pure x) =
      Part.some (x.elim (fun b => .inl (.ret b)) (fun a => .inr (f a))) := by
  change normalizeStep f (ret x) = _
  cases x <;> simp [normalizeStep, Part.bind_eq_bind]

private theorem match_root
    (atBoundary : ∀ {a c}, boundary a c → related (f a) (g c))
    (inspect : ∀ {t s}, related t s → Layer f g boundary related t s)
    {t : Tree E (B ⊕ A)} {s : Tree E (B ⊕ C)} {node : Visible E B (Tree E B)}
    (linked : related t s) (run : Elgot.Part.Runs (normalizeStep f) t node) :
    ∃ other, out (resume g s) = Part.some other ∧ RootMatch f g related node other := by
  induction run generalizing s with
  | @done t node found =>
    cases inspect linked with
    | diverged => simp [normalizeStep, Part.bind_eq_bind] at found
    | @exit value _ silent =>
      have eq : node = .ret value := by
        simpa [normalize_pure]
          using found
      subst node
      rw [silent_resume silent]
      exact ⟨_, by simp [resume], .ret _⟩
    | @request _ event leftNext _ _ silent replies =>
      have eq : node = .vis event (fun reply => resume f (leftNext reply)) := by
        simpa [normalizeStep, Part.bind_eq_bind] using found
      subst node
      rw [silent_resume silent]
      exact ⟨_, by simp [resume], .vis _ replies⟩
    | edge silent paired =>
      simp [normalize_pure] at found
    | leftTransfer silent next =>
      simp [normalize_pure] at found
  | @more t t' node transfer _ ih =>
    cases inspect linked with
    | diverged => simp [normalizeStep, Part.bind_eq_bind] at transfer
    | exit silent =>
      simp [normalize_pure] at transfer
    | request event silent replies => simp [normalizeStep, Part.bind_eq_bind] at transfer
    | @edge pending _ _ silent paired =>
      have eq : t' = f pending := by
        simpa [normalize_pure]
          using transfer
      subst t'
      rw [silent_resume silent]
      simp only [resume, pure_bind, Sum.elim_inr, ← resume_body g]
      exact ih (atBoundary paired)
    | @leftTransfer pending _ _ silent next =>
      have eq : t' = f pending := by
        simpa [normalize_pure]
          using transfer
      subst t'
      rw [silent_resume silent]
      exact ih next

theorem resume_le
    (atBoundary : ∀ {a c}, boundary a c → related (f a) (g c))
    (inspect : ∀ {t s}, related t s → Layer f g boundary related t s)
    {t : Tree E (B ⊕ A)} {s : Tree E (B ⊕ C)} (linked : related t s) :
    TraceLE (resume f t) (resume g s) := by
  have transfer {t s} (linked : related t s) {node : Visible E B (Tree E B)}
      (root : out (resume f t) = Part.some node) :
      ∃ other, out (resume g s) = Part.some other ∧ RootMatch f g related node other :=
    match_root (f := f) (g := g) (fun h => atBoundary h) (fun h => inspect h)
      linked ((out_resume_runs_iff f t node).mp root)
  intro trace
  induction trace generalizing t s with
  | «prefix» => exact fun _ => trivial
  | request event =>
    rintro ⟨k, hk⟩
    obtain ⟨_, hl, hm⟩ := transfer linked hk
    cases hm with
    | vis _ replies => exact ⟨_, hl⟩
  | exchange event reply tail ih =>
    rintro ⟨k, hk, observed⟩
    obtain ⟨_, hl, hm⟩ := transfer linked hk
    cases hm with
    | vis _ replies => exact ⟨_, hl, ih (replies reply) observed⟩
  | result value =>
    intro observed
    obtain ⟨_, hr, hm⟩ := transfer linked observed
    cases hm with
    | ret _ => exact hr

section Phi

universe v w
variable {V W K J α : Type (u + 1)} {F : Type v} {G : Type w}
  [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J]
  {left : Graph V K F} {right : Graph W J G}
  {leftPrim : Primitive E F α} {rightPrim : Primitive E G α}

theorem sourceObservation_eq_resume (instr : Primitive E F α) (graph : Graph V K F)
    (store : V → Value α) :
    sourceObservation instr graph store = resume (stepTree instr graph) (entryTree instr graph store) := by
  simp only [sourceObservation, runTree, CFG.Cyclic.Phi.run, bind_assoc, entryTree, stepTree,
    resume, ← bind_pure_comp, pure_bind, Sum.elim_inr]
  congr 1
  exact iterate_naturality _ _

theorem source_le (sim : Simulation leftPrim rightPrim left right)
    {leftStore : V → Value α} {rightStore : W → Value α}
    (entry : sim.residual (entryTree leftPrim left leftStore) (entryTree rightPrim right rightStore)) :
    TraceLE (sourceObservation leftPrim left leftStore)
      (sourceObservation rightPrim right rightStore) := by
  rw [sourceObservation_eq_resume, sourceObservation_eq_resume]
  exact resume_le
    (f := stepTree leftPrim left) (g := stepTree rightPrim right) (boundary := sim.boundary)
    (fun h => sim.atBoundary h) (fun h => sim.inspect h) entry

end Phi

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.LocalTrace
