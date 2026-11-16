module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDiv.Main
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef.Call

/-!
# Diverging linked calls, backwards: infinite runs

The infinite counterparts of the backward finite runs of `SplitBack` and `LinkSegs`:

* `coreCfg_diverges_step`: `coreCfg_diverges_inv`, keeping divergent the configuration at which
  the core activation leaves the core phase;
* `link_inf_back`: an infinite core run of the image of a typed part thread (`LinkSt`) is the
  image of an infinite host-free run of the part, one part step per core step
  (`internal_link_back`, `part_cases`); the backward counterpart of `link_inf`;
* `TrapsFrom.not_diverges`, `ResolvesAtL.not_diverges`: a configuration that traps, or resolves
  at a configuration between calls, through a live run does not diverge;
* `seq_of_step`: dependent choice, an infinite sequence of steps from an invariant every point
  of which has a step back into it.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDivInv

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread

/-! ## Leaving the core phase -/

section Generic

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call E → Canon.P E σ (Ret E)}

/-- **Divergence of a core activation**, the configuration at the exit kept: the core activation
diverges, or it reaches `y` by core steps, from which it diverges, leaving the core phase with a
step to `m₁`, which diverges. -/
theorem coreCfg_diverges_step {B : Machine.Config E σ} {th : Option ThreadId}
    {K : List FlatValue → Canon.P E σ (Ret E)} {segs : List (Seg E σ)}
    {rest : List (Activation E σ)} {x : CoreSt E}
    (h : Diverges prof hr dispatch (coreCfg B th K segs rest x)) :
    Silmaril.InfiniteTrace (CoreStep E) x ∨
      ∃ y l m₁, Relation.ReflTransGen (CoreStep E) x y ∧ CoreExit B th K segs rest y l m₁ ∧
        Diverges prof hr dispatch (coreCfg B th K segs rest y) ∧ Diverges prof hr dispatch m₁ := by
  have hd := Silmaril.InfiniteTrace.context_decompose (CoreStep E)
    (InternalStep prof hr dispatch) (coreCfg B th K segs rest)
    (fun a b => ∃ l, (∀ ev, l ≠ .host ev) ∧ Step prof hr dispatch (coreCfg B th K segs rest a) l b ∧
      CoreExit B th K segs rest a l b) (fun a b ⟨l, hl, s⟩ => by
      rcases coreCfg_step_inv s with ⟨-, y, hy, rfl⟩ | hx
      · exact .inl ⟨y, hy, rfl⟩
      · exact .inr ⟨l, hl, s, hx⟩) h
  rcases hd with hi | ⟨y, m₁, hy, ⟨l, hl, s, hx⟩, d⟩
  · exact .inl hi
  · exact .inr ⟨y, l, m₁, hy, hx, Silmaril.InfiniteTrace.fold ⟨l, hl, s⟩ d, d⟩

end Generic

/-! ## Infinite runs of a part, backwards -/

variable {P : Profile}

/-- **An infinite core run of the image of a typed part thread is the image of an infinite
host-free run of the part**, one part step per core step. -/
theorem link_inf_back (g : CanonHost (E3 P) → Nat) {s₀ : Store Nat} {y : CoreSt (E3 P)}
    (h : Silmaril.InfiniteTrace (CoreStep (E3 P)) y) {x : Store Nat × STh} {ρ : Ren} {O : Own}
    {ts} (hL : LinkSt s₀ ρ O x (Store.mapH g y.1, y.2))
    (hs : Silmaril.Wasm.Execution.Core.StoreOk x.1)
    (ht : Silmaril.Wasm.SingleThreaded.ThreadOk x.1 x.2 ts) :
    Silmaril.InfiniteTrace (Silmaril.Wasm.Game.InternalP P) x := by
  refine Silmaril.InfiniteTrace.coinduct (fun x => ∃ (y : CoreSt (E3 P)) (ρ : Ren) (O : Own),
    Silmaril.InfiniteTrace (CoreStep (E3 P)) y ∧ LinkSt s₀ ρ O x (Store.mapH g y.1, y.2) ∧
      Silmaril.Wasm.Execution.Core.StoreOk x.1 ∧ Silmaril.Wasm.SingleThreaded.ThreadOk x.1 x.2 ts)
    ?_ ⟨y, ρ, O, h, hL, hs, ht⟩
  rintro x ⟨y, ρ, O, hy, hL, hs, ht⟩
  obtain ⟨y₁, hst, hy₁⟩ := hy.unfold
  have hm : Silmaril.Wasm.Game.InternalP P (Store.mapH g y.1, y.2) (Store.mapH g y₁.1, y₁.2) :=
    Adequacy.internalP_mapH' g hst.2
  rcases part_cases (P := P) hL hs ht with hc | hc | hc | ⟨x₁, hx⟩
  · exact (link_no_internal hL (.inl hc) hm).elim
  · exact (link_no_internal hL (.inr (.inl hc)) hm).elim
  · exact (link_no_internal hL (.inr (.inr hc)) hm).elim
  obtain ⟨x₂, ρ₂, O₂, hx₂, hL₂, -, -⟩ := internal_link_back hL hx hm
  have hx₂' : Silmaril.Wasm.Game.InternalP P (x.1, x.2) (x₂.1, x₂.2) := hx₂
  obtain ⟨hs₂, htc₂, -⟩ := Silmaril.Proofs.Wasm.Game.InternalP.preserves hs ht hx₂'
  exact ⟨x₂, hx₂, y₁, ρ₂, O₂, hy₁, hL₂, hs₂, htc₂⟩

/-! ## Configurations that do not diverge -/

variable {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}

/-- A configuration that traps through a live run does not diverge. -/
theorem TrapsFrom.not_diverges {M : Machine.Config (E3 P) σ} (hT : TrapsFrom prof P impl M) :
    ¬ Diverges prof (fun _ _ => false) (DI P impl) M := by
  intro d
  obtain ⟨tr, mT, r, hrun, -, hu⟩ := hT
  obtain ⟨m', ⟨l', -, s'⟩, d'⟩ := (hrun.diverges d).unfold
  obtain ⟨-, rfl⟩ := hu.2 _ _ s'
  exact not_diverges_trapCfg _ d'

/-- A configuration that resolves at a configuration between linked calls does not diverge. -/
theorem ResolvesAtL.not_diverges {M : Machine.Config (E3 P) σ}
    {cs : (core3P P).Store (CanonHost (core3P P))} {ιe ιi : InstState}
    {fs : List (CFuncInst (core3P P))} {G : Garb P σ} {ST : List Subtask} {h₀ : σ}
    (hR : ResolvesAtL prof P impl M (readyCfgL cs ιe ιi fs G ST h₀)) :
    ¬ Diverges prof (fun _ _ => false) (DI P impl) M := by
  intro d
  obtain ⟨tr, mE, hlr, rfl⟩ := hR
  exact not_diverges_of_ctl_nil rfl (hlr.diverges d)

/-! ## Dependent choice -/

/-- **Dependent choice**: from an invariant every point of which has a step back into it, an
infinite sequence of steps. -/
theorem seq_of_step {α γ : Type} (Inv : α → Prop) (T : α → γ → α → Prop)
    (h : ∀ a, Inv a → ∃ g b, T a g b ∧ Inv b) {a₀ : α} (h₀ : Inv a₀) :
    ∃ (s : ℕ → α) (gs : ℕ → γ), s 0 = a₀ ∧ ∀ n, T (s n) (gs n) (s (n + 1)) := by
  classical
  let next : {a // Inv a} → γ × {a // Inv a} := fun a =>
    ((Classical.choose (h a.1 a.2)),
      ⟨Classical.choose (Classical.choose_spec (h a.1 a.2)),
        (Classical.choose_spec (Classical.choose_spec (h a.1 a.2))).2⟩)
  let sq : ℕ → {a // Inv a} := fun n => (fun a => (next a).2)^[n] ⟨a₀, h₀⟩
  refine ⟨fun n => (sq n).1, fun n => (next (sq n)).1, rfl, fun n => ?_⟩
  have hs : sq (n + 1) = (next (sq n)).2 := Function.iterate_succ_apply' _ _ _
  show T (sq n).1 (next (sq n)).1 (sq (n + 1)).1
  rw [hs]
  exact (Classical.choose_spec (Classical.choose_spec (h (sq n).1 (sq n).2))).1

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDivInv
