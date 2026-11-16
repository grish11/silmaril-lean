module

public import Silmaril.Wasm.Abstract.FullObs.Defs
public import Silmaril.Wasm.Abstract.BodyTrace.Thms
public import Silmaril.Semantics.ITree.Thms

/-!
# The full observation determines the pending calls (proofs)

Proofs for `Silmaril.Wasm.Abstract.FullObsFaithful.Thms`. When every answer type is inhabited,
a pending call `m` after `cs` is answered by some `a`, and the tree after `cs ++ [⟨m, a⟩]` has
some observation (`exists_obs`, classical): a finished path (a return or silent divergence)
or, if it has none, an infinite productive run, built by choosing an answer at each visible
node. Either observation of the whole tree extends `cs ++ [⟨m, a⟩]` (`obs_after_pend`), so
any tree with the same finished logs and the same infinite runs has `m` pending after `cs`
too (`pend_of_obs`). With an uninhabited answer type this fails (`callEmpty`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.FullObsFaithful

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract.Body
  Silmaril.Wasm.Abstract.BodyTrace Silmaril.Wasm.Abstract.FullObs Silmaril.Elgot.ITree

universe u

variable {E : Sig.{u}} {Y Y' : Type (u + 1)}

theorem vis_heq {Ev : Type u → Type u} {A : Type (u + 1)} {R R' : Type u} {e : Ev R} {e' : Ev R'}
    {k : R → Tree Ev A} {k' : R' → Tree Ev A} (h : vis e k = vis e' k') :
    R = R' ∧ HEq e e' ∧ HEq k k' := by
  have := congrArg out h
  simp only [out_vis, Part.some_inj, Visible.vis.injEq] at this
  exact this

/-! ## Prefixes of observations are pending -/

/-- A finished path through `cs` and then the call `c` has `c.1` pending after `cs`. -/
theorem pend_of_path {t : Tree (SigEv E) Y} {cs rest : List (Call E)} {c : Call E}
    {x : PathEnd Y} (h : Path t (cs ++ c :: rest) x) : Pend t cs c.1 := by
  induction cs generalizing t with
  | nil =>
    cases h with
    | vis ht _ => exact .here ht
  | cons c' cs ih =>
    cases h with
    | vis ht hp => exact .vis ht (ih hp)

/-- A pending call after `cs`, then the call `c`, has `c.1` pending after `cs`. -/
theorem pend_of_pend {t : Tree (SigEv E) Y} {cs rest : List (Call E)} {c : Call E} {m : E.Op}
    (h : Pend t (cs ++ c :: rest) m) : Pend t cs c.1 := by
  induction cs generalizing t with
  | nil =>
    cases h with
    | vis ht _ => exact .here ht
  | cons c' cs ih =>
    cases h with
    | vis ht hp => exact .vis ht (ih hp)

/-- An infinite run of a child, behind its call. -/
theorem infPath_cons {t : Tree (SigEv E) Y} {R : Type u} {e : SigEv E R}
    {k : R → Tree (SigEv E) Y} {n : R} {ω : Stream' (Call E)} (ht : t = vis e k)
    (h : InfPath (k n) ω) : InfPath t (Stream'.cons ⟨e.1, cast e.2.symm n⟩ ω) := by
  obtain ⟨τ, h0, hτ⟩ := h
  refine ⟨fun i => Nat.casesOn (motive := fun _ => Tree (SigEv E) Y) i t τ, rfl, fun i => ?_⟩
  cases i with
  | zero => exact ⟨R, e, k, n, ht, rfl, h0⟩
  | succ i => exact hτ i

/-! ## Every tree has an observation -/

/-- With every answer type inhabited, every tree has a finished path or an infinite run. -/
theorem exists_obs (hE : ∀ m, Nonempty (E.Ar m)) (t : Tree (SigEv E) Y) :
    (∃ cs x, Path t cs x) ∨ ∃ ω, InfPath t ω := by
  classical
  refine or_iff_not_imp_left.2 fun h0 => ?_
  have step : ∀ t : Tree (SigEv E) Y, (¬ ∃ cs x, Path t cs x) →
      ∃ (R : Type u) (e : SigEv E R) (k : R → Tree (SigEv E) Y) (r : R),
        t = vis e k ∧ ¬ ∃ cs x, Path (k r) cs x := by
    intro t ht
    rcases cases_visible t with rfl | ⟨v, rfl⟩ | ⟨R, e, k, rfl⟩
    · exact (ht ⟨[], .div, .div rfl⟩).elim
    · exact (ht ⟨[], .val v, .ret rfl⟩).elim
    · obtain ⟨n⟩ := hE e.1
      exact ⟨R, e, k, cast e.2 n, rfl, fun ⟨cs, x, hp⟩ => ht ⟨_, x, .vis rfl hp⟩⟩
  choose R e k r hvis hnext using step
  let σ : Nat → {t : Tree (SigEv E) Y // ¬ ∃ cs x, Path t cs x} := fun i =>
    Nat.rec ⟨t, h0⟩ (fun _ p => ⟨k p.1 p.2 (r p.1 p.2), hnext p.1 p.2⟩) i
  exact ⟨fun i => ⟨(e (σ i).1 (σ i).2).1, cast (e (σ i).1 (σ i).2).2.symm (r (σ i).1 (σ i).2)⟩,
    fun i => (σ i).1, rfl, fun i => ⟨_, _, _, _, hvis (σ i).1 (σ i).2, rfl, rfl⟩⟩

/-- After a pending call answered by `a`, the tree has a finished path or an infinite run
extending the answered call. -/
theorem obs_after_pend (hE : ∀ m, Nonempty (E.Ar m)) {t : Tree (SigEv E) Y}
    {cs : List (Call E)} {m : E.Op} (h : Pend t cs m) : ∀ a : E.Ar m,
      (∃ rest x, Path t (cs ++ ⟨m, a⟩ :: rest) x) ∨
        ∃ ω : Stream' (Call E), InfPath t ω ∧ ω.take (cs.length + 1) = cs ++ [⟨m, a⟩] := by
  induction h with
  | @here t R e k ht =>
    intro a
    have hc : cast e.2.symm (cast e.2 a) = a := by simp
    rcases exists_obs hE (k (cast e.2 a)) with ⟨rest, x, hp⟩ | ⟨ω, hω⟩
    · have hq := Path.vis ht hp
      rw [hc] at hq
      exact .inl ⟨rest, x, hq⟩
    · have hq := infPath_cons ht hω
      rw [hc] at hq
      exact .inr ⟨_, hq, rfl⟩
  | vis ht _ ih =>
    intro a
    rcases ih a with ⟨rest, x, hq⟩ | ⟨ω, hω, hω'⟩
    · exact .inl ⟨rest, x, .vis ht hq⟩
    · exact .inr ⟨_, infPath_cons ht hω, congrArg (_ :: ·) hω'⟩

/-- **Pending calls from finished logs and infinite runs**, for trees. -/
theorem pend_of_obs (hE : ∀ m, Nonempty (E.Ar m)) {t : Tree (SigEv E) Y}
    {t' : Tree (SigEv E) Y'} (hp : ∀ cs x, Path t cs x → ∃ x', Path t' cs x')
    (hi : ∀ ω, InfPath t ω → InfPath t' ω) {cs : List (Call E)} {m : E.Op}
    (h : Pend t cs m) : Pend t' cs m := by
  obtain ⟨a⟩ := hE m
  rcases obs_after_pend hE h a with ⟨rest, x, hq⟩ | ⟨ω, hω, htake⟩
  · obtain ⟨x', hq'⟩ := hp _ x hq
    exact pend_of_path hq'
  · obtain ⟨m', hm'⟩ := (infPath_iff_pend.1 (hi ω hω)) (cs.length + 1)
    rw [htake] at hm'
    exact pend_of_pend (rest := []) hm'

/-! ## Bodies -/

variable {S T A B : Type (u + 1)}

theorem liftCall_injective : Function.Injective (liftCall (E := E)) := by
  intro c c' h
  have := congrArg (fun d : Call (liftSig E) => (⟨d.1.down, d.2.down⟩ : Call E)) h
  exact this

/-- Same finished logs and same infinite runs: the pending calls of `f` are pending in `g`. -/
theorem toPending_subset (hE : ∀ m, Nonempty (E.Ar m)) {f g : Hom E S T A B}
    (hl : ∀ s a l e, (l, e) ∈ toAFun f s a → ∃ e', (l, e') ∈ toAFun g s a)
    (hi : ∀ s a, toInf f s a ⊆ toInf g s a) (s : S) (a : A) :
    toPending f s a ⊆ toPending g s a := by
  rintro _ ⟨cs, m, h, rfl⟩
  refine ⟨cs, m, pend_of_obs hE (fun cs x hx => ?_) (fun ω hω => ?_) h, rfl⟩
  · obtain ⟨e', cs', x', hx', he⟩ := hl s a _ _ ⟨cs, x, hx, rfl⟩
    rw [List.map_injective_iff.2 liftCall_injective (congrArg Prod.fst he)]
    exact ⟨x', hx'⟩
  · obtain ⟨ω', hω', he⟩ := hi s a ⟨ω, hω, rfl⟩
    have : ω = ω' := funext fun n => liftCall_injective (congrFun he n)
    exact this ▸ hω'

/-- The same, as equality of the pending calls. -/
theorem toPending_eq (hE : ∀ m, Nonempty (E.Ar m)) {f g : Hom E S T A B}
    (hl : ∀ s a l, (∃ e, (l, e) ∈ toAFun f s a) ↔ ∃ e, (l, e) ∈ toAFun g s a)
    (hi : toInf f = toInf g) : toPending f = toPending g :=
  funext fun s => funext fun a => Set.Subset.antisymm
    (toPending_subset hE (fun s a l e he => (hl s a l).1 ⟨e, he⟩)
      (fun s a => (congrFun (congrFun hi s) a).le) s a)
    (toPending_subset hE (fun s a l e he => (hl s a l).2 ⟨e, he⟩)
      (fun s a => (congrFun (congrFun hi s) a).ge) s a)

/-- **The full observation is faithful up to trap payloads** (answers inhabited). -/
theorem toFull_eq_iff (hE : ∀ m, Nonempty (E.Ar m)) (f g : Hom E S T A B) :
    toFull f = toFull g ↔ (toAFun f = toAFun g ∧ toPending f = toPending g) := by
  constructor
  · intro h
    have h1 : toAFun f = toAFun g := congrArg Prod.fst h
    have h2 : toInf f = toInf g := congrArg Prod.snd h
    exact ⟨h1, toPending_eq hE (fun _ _ _ => by rw [h1]) h2⟩
  · rintro ⟨h1, h2⟩
    exact Prod.ext h1 (toInf_eq_of_toPending h2)

/-- **Up to trap ≈ divergence**: collapsed finished behaviours and infinite runs. -/
theorem fullCollapseEquiv_iff (hE : ∀ m, Nonempty (E.Ar m)) (f g : Hom E S T A B) :
    FullCollapseEquiv f g ↔
      (AFun.ObsEquiv AFun.obsCollapse (toAFun f) (toAFun g) ∧ toInf f = toInf g) := by
  constructor
  · intro h
    exact ⟨h.1, toInf_eq_of_toPending h.2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, toPending_eq hE (fun s a l => ⟨fun ⟨e, he⟩ => ?_, fun ⟨e, he⟩ => ?_⟩) h2⟩
    · have hm : AFun.obsCollapse (l, e) ∈ AFun.obsCollapse '' toAFun g s a := by
        rw [← h1 s a]; exact ⟨_, he, rfl⟩
      obtain ⟨⟨l', e'⟩, hm', hx⟩ := hm
      have hl : l' = l := congrArg Prod.fst hx
      exact ⟨e', hl ▸ hm'⟩
    · have hm : AFun.obsCollapse (l, e) ∈ AFun.obsCollapse '' toAFun f s a := by
        rw [h1 s a]; exact ⟨_, he, rfl⟩
      obtain ⟨⟨l', e'⟩, hm', hx⟩ := hm
      have hl : l' = l := congrArg Prod.fst hx
      exact ⟨e', hl ▸ hm'⟩

/-! ## The hypothesis is necessary -/

/-- Two imports, neither of which ever answers. -/
def emptyAns : Sig.{0} := ⟨Bool, fun _ => PEmpty⟩

/-- Call the import `b`, which never answers. -/
noncomputable def callEmpty (b : Bool) :
    Hom emptyAns PUnit.{2} PUnit.{2} PUnit.{2} PUnit.{2} := fun _ _ =>
  ExceptT.mk (vis (E := SigEv emptyAns) (R := PEmpty) ⟨b, rfl⟩ PEmpty.elim)

theorem toAFun_callEmpty (b : Bool) : toAFun (callEmpty b) = fun _ _ => ∅ := by
  funext s a
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  rintro _ ⟨cs, x, h, -⟩
  obtain ⟨n, -⟩ := path_vis_inv h
  exact n.elim

theorem toInf_callEmpty (b : Bool) : toInf (callEmpty b) = fun _ _ => ∅ := by
  funext s a
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  rintro _ ⟨ω, ⟨τ, h0, hτ⟩, -⟩
  obtain ⟨R, e, k, r, h1, -, -⟩ := hτ 0
  rw [h0] at h1
  obtain ⟨rfl, -, -⟩ := vis_heq h1
  exact r.elim

theorem callEmpty_counterexample :
    toFull (callEmpty true) = toFull (callEmpty false) ∧
      toPending (callEmpty true) ≠ toPending (callEmpty false) := by
  refine ⟨Prod.ext ?_ ?_, fun h => ?_⟩
  · exact (toAFun_callEmpty true).trans (toAFun_callEmpty false).symm
  · exact (toInf_callEmpty true).trans (toInf_callEmpty false).symm
  · have hm : (([] : List (Call (liftSig emptyAns))), (ULift.up true : (liftSig emptyAns).Op)) ∈
        toPending (callEmpty false) ⟨⟩ ⟨⟩ := by
      rw [← h]; exact ⟨[], true, Pend.here (E := emptyAns) (R := PEmpty) (e := ⟨true, rfl⟩) rfl, rfl⟩
    obtain ⟨cs, m, h, he⟩ := hm
    obtain ⟨hcs, hm⟩ := Prod.mk.inj he
    cases h with
    | here h =>
      obtain ⟨rfl, he, -⟩ := vis_heq h
      obtain rfl := eq_of_heq he
      exact Bool.noConfusion (congrArg ULift.down hm)
    | vis _ _ => simp at hcs

end Silmaril.Proofs.Wasm.Abstract.FullObsFaithful
