module

public import Silmaril.Wasm.Game.HandleAccept.Writer.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.Writer.Basic
public import Silmaril.Proofs.Wasm.Game.HandleAccept.Writer.Decode

/-!
# Proofs: writer languages over environment sets, and structural bounds

* `fixedLang_subset_of_forall`: a fixed-environment bound in every environment of a set bounds
  the language over the set;
* `atom_writeClosed2`, `moduleConsWLang_subset_atoms2`: without `nil` and `cons` imports a cons
  writer module accepts only words;
* `atom_writeClosed`, `list_writeClosed`, `moduleSxWLang_subset_arities`, `listArities_empty`,
  `moduleSxWLang_subset_atoms`: the list arities of an n-ary writer module are those of its
  list-constructor imports; without any, it accepts only words.

New proofs (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Writers

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Wasm.Game.HandleAccept Silmaril.Wasm.Game.HandleAccept.Writers Silmaril.Accept
  Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api

/-- Over a set of fixed environments. -/
theorem fixedLang_subset_of_forall {X Op : Type} {W : Writer Op X} {pol : Policy (BitVec 32)}
    {Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) X)} {L : Set X}
    {T : Set (List (WEv Op (BitVec 32)))}
    (h : ∀ ρ ∈ Envs, fixedLang W pol {ρ} T ⊆ L) : fixedLang W pol Envs T ⊆ L := by
  intro x hx
  rw [fixedLang, langOver, Set.mem_iUnion] at hx
  obtain ⟨⟨ρ, hρ⟩, hx⟩ := hx
  refine h ρ hρ ?_
  rw [fixedLang, langOver, Set.mem_iUnion]
  exact ⟨⟨ρ, rfl⟩, hx⟩

/-! ## Structural bounds -/

theorem atom_writeClosed2 (w : BitVec 64) (args : List (BitVec 32)) :
    WriteClosed (consW (BitVec 64)) atoms2 (.atom w) args := by
  intro ts y _ hb _
  cases ts with
  | nil => cases hb; exact ⟨w, rfl⟩
  | cons _ _ => cases hb

/-- **A module without `nil` and `cons` imports accepts only words** (every module, profile and
policy without UB). -/
theorem moduleConsWLang_subset_atoms2 {P : Profile} {m : Module} {ix : ConsWImports}
    {pol : Policy (BitVec 32)} (hn : (Verify.instOf m).imports.length ≤ ix.nil)
    (hc : (Verify.instOf m).imports.length ≤ ix.cons) (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) : moduleConsWLang P m ix pol ⊆ atoms2 := by
  refine writerLang_subset_of_closed ha hw
    (write_mem_traces ?_ ?_)
  · intro e op args r hd
    obtain ⟨_, h⟩ | ⟨-, h⟩ := consWDecAsk_cases hd
      <;> cases h
  · intro e v op args r hd
    have hlt := e.1.isLt
    obtain ⟨r', ⟨-, w, h⟩ | ⟨h1, -⟩ | ⟨h1, -⟩⟩ :=
      consWDecAns_cases hd
    · cases h; exact atom_writeClosed2 w []
    · omega
    · omega

theorem atom_writeClosed (K : Set Nat) (w : BitVec 64) (args : List (BitVec 32)) :
    WriteClosed (sexpW (BitVec 64)) {x | ListArities K x} (.atom w) args := by
  intro ts y _ hb _
  cases ts with
  | nil => cases hb; trivial
  | cons _ _ => cases hb

theorem list_writeClosed {K : Set Nat} {args : List (BitVec 32)} (hK : args.length ∈ K) :
    WriteClosed (sexpW (BitVec 64)) {x | ListArities K x} .list args := by
  intro ts y hl hb hts
  cases hb
  exact ⟨hl ▸ hK, fun i => hts _ (List.getElem_mem _)⟩

/-- **List arities are bounded by the imports**: every list node of every tree a module
accepts through the n-ary API has the arity of one of its list-constructor imports (every
module, profile and policy without UB). -/
theorem moduleSxWLang_subset_arities {P : Profile} {m : Module} {ix : SxWImports}
    {pol : Policy (BitVec 32)} (ha : pol.onAccept ≠ .ub) (hw : pol.onWrite ≠ .ub) :
    moduleSxWLang P m ix pol ⊆ {x | ListArities (sxArities ix (Verify.instOf m).imports) x} := by
  refine writerLang_subset_of_closed ha hw
    (write_mem_traces ?_ ?_)
  · intro e op args r hd
    obtain ⟨_, h⟩ | ⟨-, h⟩ := sxWDecAsk_cases hd
      <;> cases h
  · intro e v op args r hd
    obtain ⟨r', ⟨-, w, h⟩ | ⟨h1, args', hl, h⟩⟩ :=
      sxWDecAns_cases hd
    · cases h; exact atom_writeClosed _ w []
    · cases h
      exact list_writeClosed ⟨e.1.val, h1, e.1.isLt, hl.symm⟩

theorem listArities_empty {x : SExp (BitVec 64)} (h : ListArities ∅ x) : x ∈ atoms := by
  cases x with
  | atom w => exact ⟨w, rfl⟩
  | list n cs => exact absurd h.1 (Set.notMem_empty n)

/-- **A module without list-constructor imports accepts only words.** -/
theorem moduleSxWLang_subset_atoms {P : Profile} {m : Module} {ix : SxWImports}
    {pol : Policy (BitVec 32)} (hl : ∀ j ∈ ix.lists, (Verify.instOf m).imports.length ≤ j)
    (ha : pol.onAccept ≠ .ub) (hw : pol.onWrite ≠ .ub) : moduleSxWLang P m ix pol ⊆ atoms := by
  intro x hx
  refine listArities_empty ?_
  have h := moduleSxWLang_subset_arities ha hw hx
  have hK : sxArities ix (Verify.instOf m).imports = ∅ := by
    ext n
    simp only [sxArities, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨j, hj, hlt, -⟩
    exact absurd (hl j hj) (by omega)
  rw [hK] at h
  exact h

end Silmaril.Proofs.Wasm.Game.HandleAccept.Writers
