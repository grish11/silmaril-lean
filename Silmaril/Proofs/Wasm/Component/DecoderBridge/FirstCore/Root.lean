module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore.Prefix
public import Silmaril.Proofs.Wasm.Component.Reference.Adequacy.RefRun

/-!
# Root instantiation up to the first core instantiation, over any engine

* `FocusAt th X p m m₁`: in every context, the program `p` runs from `m` (a live run) to `m₁`
  with `X` in focus; `FocusAt.here`, `FocusAt.seq`, `FocusAt.left`;
* `root_first`: root instantiation (`instantiateProg`) of a component whose definitions before
  the first core instantiation satisfy `preOk 0 0`, from an unlocked store without component
  instances and root arguments that are allocated component functions, traps with a
  specification trap before that instantiation, or reaches it (`instantiateCore ⟨0⟩ f mi args`
  in focus) with only the nesting depth, the root instance and host allocations in the core
  store changed, and the frame's core modules those of the definitions before it;
* `instTraps_of_lrun`: a live run from the instantiation host event to a configuration whose
  step is a specification trap is a trapping instantiation (`InstantiateTraps`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Instantiate
open Silmaril.Wasm.Component.Machine.StepDefs

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call E → Canon.P E σ (Ret E)}

/-! ## Runs to a hole -/

variable (prof hr dispatch) in
/-- In every context, the program `p` runs from `m` to `m₁`, where `X` is in focus. -/
def FocusAt (th : Option ThreadId) {β α : Type} (X : Canon.P E σ β) (p : Canon.P E σ α)
    (m m₁ : Machine.Config E σ) : Prop :=
  ∀ (f : α → Canon.P E σ (Ret E)) (segs : List (Seg E σ)) (rest : List (Activation E σ)),
    m.store.lockdown = false →
    ∃ (K : β → Canon.P E σ (Ret E)) (tr : List (Label E σ)),
      LRun prof hr dispatch { m with ctl := ⟨th, .prog (p >>= f), segs⟩ :: rest } tr
        { m₁ with ctl := ⟨th, .prog (X >>= K), segs⟩ :: rest }

namespace FocusAt

theorem here {th : Option ThreadId} {β α : Type} {X : Canon.P E σ β} (k : β → Canon.P E σ α)
    (m : Machine.Config E σ) : FocusAt prof hr dispatch th X (X >>= k) m m := by
  intro f segs rest _
  refine ⟨fun u => k u >>= f, [], ?_⟩
  rw [bind_assoc]
  exact .refl _

theorem self {th : Option ThreadId} {β : Type} (X : Canon.P E σ β) (m : Machine.Config E σ) :
    FocusAt prof hr dispatch th X X m m :=
  fun f _ _ _ => ⟨f, [], .refl _⟩

theorem seq {th : Option ThreadId} {β α γ : Type} {X : Canon.P E σ β} {p : Canon.P E σ γ}
    {g : γ → Canon.P E σ α} {m m₁ m₂ : Machine.Config E σ} {tr₁ : List (Label E σ)} {c : γ}
    (h₁ : RunsQ dispatch th p m tr₁ c m₁) (h₂ : FocusAt prof hr dispatch th X (g c) m₁ m₂) :
    FocusAt prof hr dispatch th X (p >>= g) m m₂ := by
  intro f segs rest hl
  obtain ⟨K, tr, r⟩ := h₂ f segs rest (h₁.lock.trans hl)
  refine ⟨K, tr₁ ++ tr, ?_⟩
  have d := h₁.lrun (prof := prof) (hr := hr) hl (fun b => g b >>= f) segs rest
  rw [bind_assoc]
  exact d.trans r

theorem left {th : Option ThreadId} {β α γ : Type} {X : Canon.P E σ β} {p : Canon.P E σ γ}
    {g : γ → Canon.P E σ α} {m m₁ : Machine.Config E σ}
    (h : FocusAt prof hr dispatch th X p m m₁) : FocusAt prof hr dispatch th X (p >>= g) m m₁ := by
  intro f segs rest hl
  obtain ⟨K, tr, r⟩ := h (fun b => g b >>= f) segs rest hl
  refine ⟨K, tr, ?_⟩
  rw [bind_assoc]
  exact r

theorem silent {th : Option ThreadId} {β α γ : Type} {X : Canon.P E σ β} {p : Canon.P E σ γ}
    {g : γ → Canon.P E σ α} {m m₁ m₂ : Machine.Config E σ} {c : γ}
    (h₁ : TRuns p m c m₁) (h₂ : FocusAt prof hr dispatch th X (g c) m₁ m₂) :
    FocusAt prof hr dispatch th X (p >>= g) m m₂ := by
  obtain ⟨tr, hr₁, -⟩ := SRuns.runsQ (dispatch := dispatch) h₁ th
  exact seq hr₁ h₂

end FocusAt

/-! ## Trapping instantiations -/

/-- **A live run from the instantiation host event to a specification trap is a trapping
instantiation.** -/
theorem instTraps_of_lrun [∀ a b, Decidable (E.ExternSub a b)] {m mT m' : Machine.Config E σ}
    {c : Syntax.Component E.Module} {args : Exports E} {tr : List (Label E σ)} {r : TrapReason}
    (hm : HostReadyCfg m)
    (hrun : LRun prof hr dispatch { m with ctl := [.ofProg none (StepDefs.runProg (instantiateProg c args))] }
      tr mT)
    (hlive : Live mT) (hs : Step prof hr dispatch mT (.trap r) m')
    (hr' : ∀ msg, r ≠ .internal msg) : InstantiateTraps prof hr dispatch m c args m' := by
  refine ⟨tr ++ [.trap r], .cons (.hostRun hm) (Adequacy.steps_append hrun.steps
    (.cons hs (.refl _))), ?_, ?_, Adequacy.step_trap_lockdown hs⟩
  · intro ev hev
    rcases List.mem_append.mp hev with hev | hev
    · exact Adequacy.LRun.no_host hrun ev hev
    · simp at hev
  · intro msg hev
    rcases List.mem_append.mp hev with hev | hev
    · exact Adequacy.LRun.no_trap hrun hlive _ hev
    · simp only [List.mem_singleton, Label.trap.injEq] at hev
      exact hr' msg hev.symm

/-- **A program-level specification trap of the instantiation program is a trapping
instantiation.** -/
theorem instTraps_of_trapsQS [∀ a b, Decidable (E.ExternSub a b)] {m mT : Machine.Config E σ}
    {c : Syntax.Component E.Module} {args : Exports E} {tr : List (Label E σ)}
    (hm : HostReadyCfg m) (h : TrapsQS dispatch none (instantiateProg c args) m tr mT) :
    ∃ m', InstantiateTraps prof hr dispatch m c args m' := by
  obtain ⟨q, segs', r, hr', hrun, hlive, hu⟩ :=
    h.lrun (prof := prof) (hr := hr) hm.2.1 (fun _ => pure .unit) [] []
  exact ⟨_, instTraps_of_lrun (tr := tr) hm hrun hlive hu.1 hr'⟩

/-! ## Traps or a hole -/

variable (prof hr dispatch) in
/-- The program `p` traps from `m` with a specification trap, or reaches `X i` in focus, for
some `i`, at a configuration satisfying `Q i`. -/
def FOut {ι β α : Type} (X : ι → Canon.P E σ β) (p : Canon.P E σ α) (m : Machine.Config E σ)
    (Q : ι → Machine.Config E σ → Prop) : Prop :=
  (∃ tr mT, TrapsQS dispatch none p m tr mT) ∨
    ∃ i m₁, FocusAt prof hr dispatch none (X i) p m m₁ ∧ Q i m₁

namespace FOut

variable {ι : Type}

theorem left {β α γ : Type} {X : ι → Canon.P E σ β} {p : Canon.P E σ γ}
    {g : γ → Canon.P E σ α} {m : Machine.Config E σ} {Q : ι → Machine.Config E σ → Prop}
    (h : FOut prof hr dispatch X p m Q) : FOut prof hr dispatch X (p >>= g) m Q := by
  rcases h with ⟨tr, mT, ht⟩ | ⟨i, m₁, hf, hq⟩
  · exact .inl ⟨tr, mT, .left ht⟩
  · exact .inr ⟨i, m₁, hf.left, hq⟩

theorem seqT {β α γ : Type} {X : ι → Canon.P E σ β} {p : Canon.P E σ γ}
    {g : γ → Canon.P E σ α} {m : Machine.Config E σ} {Q₀ : γ → Machine.Config E σ → Prop}
    {Q : ι → Machine.Config E σ → Prop} (h : TOrT dispatch p m Q₀)
    (h' : ∀ c m', Q₀ c m' → FOut prof hr dispatch X (g c) m' Q) :
    FOut prof hr dispatch X (p >>= g) m Q := by
  rcases h with ⟨tr, mT, ht⟩ | ⟨c, m₁, hr₁, hq₁⟩
  · exact .inl ⟨tr, mT, .left ht⟩
  · rcases h' c m₁ hq₁ with ⟨tr, mT, ht⟩ | ⟨i, m₂, hf, hq⟩
    · obtain ⟨tr₁, hr₂, -⟩ := SRuns.runsQ (dispatch := dispatch) hr₁ none
      exact .inl ⟨_, _, .bind hr₂ ht⟩
    · exact .inr ⟨i, m₂, hf.silent hr₁, hq⟩

theorem here {β α : Type} {X : ι → Canon.P E σ β} (i : ι) (k : β → Canon.P E σ α)
    {m : Machine.Config E σ} {Q : ι → Machine.Config E σ → Prop} (hq : Q i m) :
    FOut prof hr dispatch X (X i >>= k) m Q :=
  .inr ⟨i, m, .here k m, hq⟩

end FOut

/-! ## Root instantiation up to the first core instantiation -/

theorem firstCore?_eq {M : Type} (r : List (Syntax.Definition M)) :
    ∀ {pre : List (Syntax.Definition M)} {mi : Nat} {cargs : List (String × Nat)}
      {post : List (Syntax.Definition M)}, firstCore? r = some (pre, mi, cargs, post) →
      r = pre ++ .coreInstance (.instantiate mi cargs) :: post := by
  induction r with
  | nil => intro _ _ _ _ h; cases h
  | cons d ds ih =>
    intro pre mi cargs post h
    have hgen : ∀ q, (firstCore? ds).map (fun q => (d :: q.1, q.2.1, q.2.2.1, q.2.2.2)) =
        some q → q = (pre, mi, cargs, post) → d :: ds =
          pre ++ .coreInstance (.instantiate mi cargs) :: post := by
      intro q hq hq'
      subst hq'
      obtain ⟨⟨pre', mi', cargs', post'⟩, hq₁, he⟩ := Option.map_eq_some_iff.mp hq
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      rw [ih hq₁]
      rfl
    match d, h with
    | .coreInstance (.instantiate mi' cargs'), h =>
      simp only [firstCore?, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      rfl
    | .coreModule _, h | .coreInstance (.exports _), h | .coreType _, h | .component _, h
    | .instance_ _, h | .alias _, h | .type _, h | .canon _, h | .start _ _ _, h
    | .import_ _ _, h | .export_ _ _ _, h | .value _ _, h => exact hgen _ h rfl

theorem tOrT_trapIf {b : Bool} {r : TrapReason} (hr' : ∀ msg, r ≠ .internal msg)
    (m : Machine.Config E σ) :
    TOrT dispatch (trapIf b r : Canon.P E σ Unit) m (fun _ m' => m' = m) := by
  cases b
  · exact TOrT.runs (TRuns.pure () m) rfl
  · exact TOrT.trap (isSpecTrap_trap hr')

theorem tOrT_checkImport (e : Except String Unit) (m : Machine.Config E σ) :
    TOrT dispatch (checkImport e : Canon.P E σ Unit) m (fun _ m' => m' = m) := by
  cases e with
  | error e => exact TOrT.trap (isSpecTrap_trap (r := .hostTrap _) fun _ h => by cases h)
  | ok u => exact TOrT.runs (TRuns.pure () m) rfl

/-- The store at the first core instantiation: the nesting depth incremented, the root
instance allocated, the core store `c'`. -/
def firstStore (S : CStore E) (c' : E.Store (CanonHost E)) : CStore E :=
  { ArenaOps.allocSt ArenaField.insts {} (DispatchSt.incNestingSt S) with core := c' }

/-- **Root instantiation up to the first core instantiation.** -/
theorem root_first [∀ a b, Decidable (E.ExternSub a b)] {m : Machine.Config E σ}
    {r pre post : Syntax.Component E.Module} {mi : Nat} {cargs : List (String × Nat)}
    {args : Exports E} (hs : firstCore? r = some (pre, mi, cargs, post))
    (hpre : preOk 0 0 pre = true) (ha : ArgsOk args m) (hl : m.store.lockdown = false)
    (hi : m.store.insts = []) :
    (∃ tr mT, TrapsQS dispatch none (instantiateProg r args) m tr mT) ∨
      ∃ (f : Frame E) (c' : E.Store (CanonHost E)),
        FocusAt prof hr dispatch none (instantiateCore ⟨0⟩ f mi cargs) (instantiateProg r args) m
          { m with store := firstStore m.store c' } ∧
        HostAllocs E m.store.core c' ∧ f.coreModules = coreMods pre := by
  have hrr := firstCore?_eq r hs
  suffices h : FOut prof hr dispatch (fun p : Frame E × E.Store (CanonHost E) =>
      (instantiateCore (σ := σ) ⟨0⟩ p.1 mi cargs)) (instantiateProg r args) m
      (fun p m₁ => m₁ = { m with store := firstStore m.store p.2 } ∧
        HostAllocs E m.store.core p.2 ∧ p.1.coreModules = coreMods pre) by
    rcases h with h | ⟨⟨f, c'⟩, m₁, hf, rfl, hc, hm⟩
    · exact .inl h
    · exact .inr ⟨f, c', hf, hc, hm⟩
  unfold instantiateProg
  refine FOut.seqT (TOrT.runs (TRuns.modifyStore (f := DispatchSt.incNestingSt) (fun _ => rfl) m)
    (Q := fun _ m' => m' = { m with store := DispatchSt.incNestingSt m.store }) rfl) ?_
  rintro _ m₁ rfl
  refine FOut.left ?_
  unfold instantiateRootCall instantiateRoot
  refine FOut.seqT (tOrT_trapIf (fun _ h => by cases h) _) ?_
  rintro _ m₂ rfl
  refine FOut.seqT (TOrT.runs (TRuns.getStore _)
    (Q := fun s m' => s = (DispatchSt.incNestingSt m.store : CStore E) ∧
      m' = { m with store := DispatchSt.incNestingSt m.store }) ⟨rfl, rfl⟩) ?_
  rintro s m₃ ⟨rfl, rfl⟩
  refine FOut.seqT (tOrT_checkImport _ _) ?_
  rintro _ m₄ rfl
  refine FOut.seqT (TOrT.runs (TRuns.allocObj ArenaField.insts (fun _ _ => rfl) {} _)
    (Q := fun i m' => i = (⟨0⟩ : InstId) ∧
      m' = { m with store := ArenaOps.allocSt ArenaField.insts {} (DispatchSt.incNestingSt m.store) })
    ⟨by simp [ArenaField.size, ArenaField.insts, DispatchSt.incNestingSt, hi],
      rfl⟩) ?_
  rintro i m₅ ⟨rfl, rfl⟩
  refine FOut.left ?_
  unfold instantiateComponent
  refine FOut.left ?_
  dsimp only
  rw [hrr, List.foldlM_append]
  have hpi : PreInv ({} : Scope E)
      ({ m with store := ArenaOps.allocSt ArenaField.insts {} (DispatchSt.incNestingSt m.store) } :
        Machine.Config E σ) 0 0 [] :=
    ⟨rfl, (fun _ h => by cases h), rfl, rfl, hl⟩
  refine FOut.seqT (prefix_run pre 0 0 {} _ [] ha hpre hpi) ?_
  rintro sc' m₆ ⟨c', nf', ncf', rfl, hc, hinv⟩
  rw [List.foldlM_cons]
  refine FOut.left ?_
  simp only [instantiateDef]
  exact .inr ⟨(sc'.frame, c'), _, FocusAt.here _ _, rfl, hc, by simpa using hinv.mods⟩

/-! ## The first core instantiation, for a module without imports -/

section Core

variable [∀ a b, Decidable (E.ExternSub a b)]

theorem coreImportsFor_nil {s : E.Store (CanonHost E)} {md : E.Module} {cargs : List (String × Nat)}
    {f : Frame E} (h : E.importTypes md = []) : coreImportsFor? s md cargs f = some [] := by
  unfold coreImportsFor?
  rw [h]
  rfl

/-- **Preparation fails**: the core instantiation traps `coreTrap`. -/
theorem instantiateCore_none {f : Frame E} {mi : Nat} {cargs : List (String × Nat)}
    {md : E.Module} {m₁ : Machine.Config E σ} (hmd : f.coreModule? mi = some md)
    (himp : E.importTypes md = []) (hp : E.prepare? m₁.store.core md [] = none) :
    ∃ tr mT, TrapsQS dispatch none (instantiateCore ⟨0⟩ f mi cargs) m₁ tr mT := by
  have hc := coreImportsFor_nil (s := m₁.store.core) (cargs := cargs) (f := f) himp
  unfold instantiateCore
  simp only [hmd, need, orTrap, pure_bind]
  obtain ⟨tr, hrun, -⟩ := SRuns.runsQ (dispatch := dispatch) (TRuns.getStore m₁) none
  refine ⟨tr ++ [], m₁, .bind hrun ?_⟩
  simp only [hc, pure_bind, hp]
  exact .trap _ (isSpecTrap_trap (fun _ h => by cases h))

/-- **Preparation reports a start function**: the core instantiation reaches it, the core
store replaced. -/
theorem instantiateCore_start {f : Frame E} {mi : Nat} {cargs : List (String × Nat)}
    {md : E.Module} {m₁ : Machine.Config E σ} {core' : E.Store (CanonHost E)} {ci : E.Inst}
    {sf : E.FuncAddr} (hmd : f.coreModule? mi = some md) (himp : E.importTypes md = [])
    (hp : E.prepare? m₁.store.core md [] = some (core', ci, some sf)) :
    FocusAt prof hr dispatch none (Instantiate.runStart ⟨0⟩ sf) (instantiateCore ⟨0⟩ f mi cargs) m₁
      { m₁ with store := setCoreSt core' m₁.store } := by
  have hc := coreImportsFor_nil (s := m₁.store.core) (cargs := cargs) (f := f) himp
  unfold instantiateCore
  simp only [hmd, need, orTrap, pure_bind]
  refine FocusAt.silent (TRuns.getStore m₁) ?_
  simp only [hc, pure_bind, hp]
  refine FocusAt.silent (TRuns.modifyStore (f := setCoreSt core') (fun _ => rfl) m₁) ?_
  exact FocusAt.here _ _

end Core

end Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore
