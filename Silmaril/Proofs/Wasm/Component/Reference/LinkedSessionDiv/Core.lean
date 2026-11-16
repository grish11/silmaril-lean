module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd.Sess
public import Silmaril.Proofs.Wasm.Component.Reference.SessionDiv.Main
public import Silmaril.Wasm.Component.Reference.LinkedSessionDiv.Defs
public import Silmaril.Wasm.Game.Trapped.Thms

/-!
# Diverging linked calls: infinite runs

The infinite counterparts of the finite forward runs of `LinkedSessionFwd`:

* `link_inf`: an infinite host-free run of a part related to a shared thread (`LinkSt`, as in
  `reach_link_fwd`) is an infinite core run of the shared thread, one core step per part step
  (`internal_link`, `internalP_unmapH`);
* `not_divB_doomed`: a thread filled with a trap does not run host-free forever (its code
  shrinks, `Wasm.Game.trapped_step_lt`);
* `steps_diverges`: a finite run without host events followed by divergence diverges;
  `diverges_of_segs`: a configuration from which nonempty host-free runs can always be
  continued diverges (productivity is the nonemptiness of each segment).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDiv

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread

variable {P : Profile}

/-! ## Infinite runs of a part -/

/-- **An infinite host-free run of a part is an infinite core run of its image** in the shared
store of host type `CanonHost`, when `gi` inverts the renaming `g` on its host code. -/
theorem link_inf (g : CanonHost (E3 P) → Nat) (gi : Nat → CanonHost (E3 P)) {s₀ : Store Nat}
    {x : ℕ → Store Nat × STh} (hx : ∀ n, Silmaril.Wasm.Game.InternalP P (x n) (x (n + 1)))
    {y : CoreSt (E3 P)} {ρ : Ren} {O : Own} (hs : HostsSat (fun h => gi (g h) = h) y.1)
    (hL : LinkSt s₀ ρ O (x 0) (Store.mapH g y.1, y.2)) :
    Silmaril.InfiniteTrace (CoreStep (E3 P)) y := by
  refine Silmaril.InfiniteTrace.coinduct (fun z => ∃ n ρ O, HostsSat (fun h => gi (g h) = h) z.1 ∧
    LinkSt s₀ ρ O (x n) (Store.mapH g z.1, z.2)) ?_ ⟨0, ρ, O, hs, hL⟩
  rintro z ⟨n, ρ, O, hs, hL⟩
  obtain ⟨⟨σ₁, t₁⟩, ρ₁, O₁, hy₁, hL₁, -, -⟩ := internal_link hL (hx n)
  obtain ⟨s', rfl, hfs, hi⟩ := internalP_unmapH g gi hs hy₁
  exact ⟨(s', t₁), coreStep_of_internalP hi, n + 1, ρ₁, O₁,
    fun a fi h ha hc => hs a fi h (hfs ▸ ha) hc, hL₁⟩

/-! ## Doomed threads -/

/-- The thread `t` at the store `s` is filled with a trap. -/
def Doomed (s : Store Nat) (t : STh) : Prop :=
  ∃ (fr : Silmaril.Wasm.Execution.Core.Frame) (E : Silmaril.Wasm.SingleThreaded.Ctx),
    t.config s = ⟨s, fr, E.fill [.trap]⟩

/-- **A thread filled with a trap does not run host-free forever.** -/
theorem not_divB_doomed {s : Store Nat} {t : STh} (hd : Doomed s t) : ¬ Linked2.DivB P s t := by
  rintro ⟨g, hg0, hg⟩
  obtain ⟨fr, E, ht⟩ := hd
  have key : ∀ n, ∃ E' : Silmaril.Wasm.SingleThreaded.Ctx,
      (g n).2.config (g n).1 = ⟨s, fr, E'.fill [.trap]⟩ ∧
        sizeOf (E'.fill [.trap]) + n ≤ sizeOf (E.fill [.trap]) := by
    intro n
    induction n with
    | zero => exact ⟨E, by rw [hg0]; exact ht, by omega⟩
    | succ n ih =>
      obtain ⟨E', hn, hle⟩ := ih
      obtain ⟨f', c', hy, hst⟩ := hg n
      rw [hn] at hst
      obtain ⟨hs, hf, E'', hc⟩ := Silmaril.Proofs.Wasm.Game.Choice.step_doomed hst
      have hlt := Silmaril.Wasm.Game.trapped_step_lt hst
      simp only at hs hf hc hlt
      refine ⟨E'', ?_, ?_⟩
      · rw [hy]
        show (⟨(g (n + 1)).1, f', c'⟩ : Silmaril.Wasm.Execution.Core.Config Nat) = _
        rw [hs, hf, hc]
      · rw [hc] at hlt
        omega
  obtain ⟨E', -, hle⟩ := key (sizeOf (E.fill [.trap]) + 1)
  omega

/-! ## Divergence of the machine -/

variable {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call (E3 P) → Canon.P (E3 P) σ (Ret (E3 P))}

/-- **A finite run without host events, then divergence, diverges.** -/
theorem steps_diverges {m m' : Machine.Config (E3 P) σ} {tr : List (Label (E3 P) σ)}
    (h : Steps prof hr dispatch m tr m') (hh : ∀ ev, Label.host ev ∉ tr)
    (d : Diverges prof hr dispatch m') : Diverges prof hr dispatch m := by
  induction h with
  | refl => exact d
  | @cons m₁ m₂ m₃ l tr s _ ih =>
    refine Silmaril.InfiniteTrace.fold ⟨l, fun ev he => ?_, s⟩
      (ih (fun ev hm => hh ev (List.mem_cons_of_mem _ hm)) d)
    subst he
    exact hh ev List.mem_cons_self

/-- **Productive segments diverge**: if from every configuration of an invariant `Q` a nonempty
run without host events reaches `Q` again, every configuration of `Q` diverges. -/
theorem diverges_of_segs (Q : Machine.Config (E3 P) σ → Prop)
    (h : ∀ m, Q m → ∃ tr m', Steps prof hr dispatch m tr m' ∧ tr ≠ [] ∧
      (∀ ev, Label.host ev ∉ tr) ∧ Q m')
    {m : Machine.Config (E3 P) σ} (hm : Q m) : Diverges prof hr dispatch m := by
  refine Silmaril.InfiniteTrace.coinduct (fun m => ∃ tr m', Steps prof hr dispatch m tr m' ∧
    tr ≠ [] ∧ (∀ ev, Label.host ev ∉ tr) ∧ Q m') ?_ (h m hm)
  rintro m₀ ⟨tr, m', r, hne, hh, hq⟩
  cases r with
  | refl => exact absurd rfl hne
  | @cons _ m₁ _ l tr' s r' =>
    refine ⟨m₁, ⟨l, fun ev he => ?_, s⟩, ?_⟩
    · subst he
      exact hh ev List.mem_cons_self
    · cases tr' with
      | nil =>
        cases r'
        exact h _ hq
      | cons l' tr'' =>
        exact ⟨_, m', r', List.cons_ne_nil _ _,
          fun ev hm => hh ev (List.mem_cons_of_mem _ hm), hq⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDiv
