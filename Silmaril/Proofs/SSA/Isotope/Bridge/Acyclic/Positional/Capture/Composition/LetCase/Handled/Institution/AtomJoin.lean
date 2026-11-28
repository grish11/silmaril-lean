module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Direct.Join.Defs

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open CategoryTheory
open Silmaril.Isotope.Institution.Acyclic.Captured (RankedEquation denoteRanked)
open Region (packedExitType)
open Reverse (CheckedTable)
open LetCase.LocallyNameless (Derivation Equiv HasType Pure)
open LetCase.Structural.Reply (Γ₀)
open LetSeq.StraightLine.Structural (Slot Assembly)
open LetSeq.StraightLine.Structural.Categorical (traceJ)
open scoped LetSeq.StraightLine.Structural Tagged

variable {α Φ : Type} [TaggedSignature α Φ] {L : List (Ty α)}

/-! ## A prefix in the bound term of a let

The typing and the congruence of a prefix around a term, and the
sequencing equation that moves a prefix out of the bound term of a let.
The equation uses the native sequencing laws at a request and at a pattern
let. -/

mutual

theorem SpelledPrefix.plug_typed_proof : {stack : List (List α)} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {holds : Holds Δ stack} → {stack' : List (List α)} → {m' : Nat} → {Δ' : BoundCtx (Ty α) m'} →
    {holds' : Holds Δ' stack'} → (p : SpelledPrefix (Φ := Φ) stack Δ holds stack' Δ' holds') →
    {e : LetCase.LocallyNameless.Tm Empty Φ m'} → {C : Ty α} → HasType Φ Γ₀ Δ' e C → HasType Φ Γ₀ Δ (p.plug e) C
  | _, _, _, _, _, _, _, _, .stop, _, _, h => h
  | _, _, _, _, _, _, _, _, .unit next, _, _, h => next.plug_typed_proof h
  | _, _, _, _, _, _, _, _, .atom next, _, _, h => next.plug_typed_proof h
  | _, _, _, .cons top _, _, _, _, _, .step next, _, _, h =>
    .let₂ (slotTyping top).toHasType (next.plug_typed_proof h)
  | _, _, _, _, _, _, _, _, .ask g argument reply, _, _, h =>
    .let₁ (Derivation.op (f := g) (argTyping argument)).toHasType (reply.plug_typed_proof h)
  | _, _, _, _, _, _, _, _, .pick _ next, _, _, h => next.plug_typed_proof h

theorem SpelledPrefixTags.plug_typed_proof : {stack : List (List α)} → {tags : List (List α)} →
    {m : Nat} → {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {stack' : List (List α)} → {m' : Nat} →
    {Δ' : BoundCtx (Ty α) m'} → {holds' : Holds Δ' stack'} →
    (p : SpelledPrefixTags (Φ := Φ) stack tags Δ holds stack' Δ' holds') → {e : LetCase.LocallyNameless.Tm Empty Φ m'} →
    {C : Ty α} → HasType Φ Γ₀ Δ' e C → HasType Φ Γ₀ (Δ.snoc (tagsTy tags)) (p.plug e) C
  | _, _, _, _, _, _, _, _, _, .bind _ next, _, _, h => next.plug_typed_proof h

end

mutual

theorem SpelledPrefix.plug_congr_proof : {stack : List (List α)} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {holds : Holds Δ stack} → {stack' : List (List α)} → {m' : Nat} → {Δ' : BoundCtx (Ty α) m'} →
    {holds' : Holds Δ' stack'} → (p : SpelledPrefix (Φ := Φ) stack Δ holds stack' Δ' holds') →
    {e e' : LetCase.LocallyNameless.Tm Empty Φ m'} → {C : Ty α} → Equiv false Γ₀ Δ' e e' C →
    Equiv false Γ₀ Δ (p.plug e) (p.plug e') C
  | _, _, _, _, _, _, _, _, .stop, _, _, _, h => h
  | _, _, _, _, _, _, _, _, .unit next, _, _, _, h => next.plug_congr_proof h
  | _, _, _, _, _, _, _, _, .atom next, _, _, _, h => next.plug_congr_proof h
  | _, _, _, .cons top _, _, _, _, _, .step next, _, _, _, h =>
    .let₂ (.refl (slotTyping top).toHasType) (next.plug_congr_proof h)
  | _, _, _, _, _, _, _, _, .ask g argument reply, _, _, _, h =>
    .let₁ (.refl (Derivation.op (f := g) (argTyping argument)).toHasType) (reply.plug_congr_proof h)
  | _, _, _, _, _, _, _, _, .pick _ next, _, _, _, h => next.plug_congr_proof h

theorem SpelledPrefixTags.plug_congr_proof : {stack : List (List α)} → {tags : List (List α)} →
    {m : Nat} → {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {stack' : List (List α)} → {m' : Nat} →
    {Δ' : BoundCtx (Ty α) m'} → {holds' : Holds Δ' stack'} →
    (p : SpelledPrefixTags (Φ := Φ) stack tags Δ holds stack' Δ' holds') → {e e' : LetCase.LocallyNameless.Tm Empty Φ m'} →
    {C : Ty α} → Equiv false Γ₀ Δ' e e' C → Equiv false Γ₀ (Δ.snoc (tagsTy tags)) (p.plug e) (p.plug e') C
  | _, _, _, _, _, _, _, _, _, .bind _ next, _, _, _, h => next.plug_congr_proof h

end

omit [TaggedSignature α Φ] in
/-- Weakening a term beneath its newest slot and then renaming under that
slot is renaming under that slot along the weakened renaming. -/
theorem underBinder_rename_up {m k : Nat} (K : LetCase.LocallyNameless.Tm Empty Φ (m + 1)) (w : Fin (m + 1) → Fin k) :
    K.underBinder.rename (LetCase.LocallyNameless.Tm.up w) = K.rename (LetCase.LocallyNameless.Tm.up (fun i => w i.succ)) :=
  (LetCase.LocallyNameless.Tm.rename_comp _ _ K).trans (LetCase.LocallyNameless.Tm.rename_congr (fun i => Fin.cases rfl (fun _ => rfl) i) K)

omit [TaggedSignature α Φ] in
/-- The same past two slots. -/
theorem underBinder_twice_rename_up {m k : Nat} (K : LetCase.LocallyNameless.Tm Empty Φ (m + 1)) (w : Fin (m + 2) → Fin k) :
    K.underBinder.underBinder.rename (LetCase.LocallyNameless.Tm.up w) = K.rename (LetCase.LocallyNameless.Tm.up (fun i => w i.succ.succ)) := by
  simp only [LetCase.LocallyNameless.Tm.underBinder, LetCase.LocallyNameless.Tm.rename_comp]
  exact LetCase.LocallyNameless.Tm.rename_congr (fun i => Fin.cases rfl (fun _ => rfl) i) K

mutual

theorem SpelledPrefix.let_plug_proof : {stack : List (List α)} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {holds : Holds Δ stack} → {stack' : List (List α)} → {m' : Nat} → {Δ' : BoundCtx (Ty α) m'} →
    {holds' : Holds Δ' stack'} → (p : SpelledPrefix (Φ := Φ) stack Δ holds stack' Δ' holds') →
    {v : LetCase.LocallyNameless.Tm Empty Φ m'} → {K : LetCase.LocallyNameless.Tm Empty Φ (m + 1)} → {J C : Ty α} → HasType Φ Γ₀ Δ' v J →
    HasType Φ Γ₀ (Δ.snoc J) K C →
    Equiv false Γ₀ Δ (.let₁ (p.plug v) K) (p.plug (.let₁ v (K.rename (LetCase.LocallyNameless.Tm.up p.weaken.toFun)))) C
  | _, _, _, _, _, _, _, _, .stop, v, K, _, _, hv, hK =>
    cast (congrArg (fun x => Equiv false Γ₀ _ (LetCase.LocallyNameless.Tm.let₁ v K) (LetCase.LocallyNameless.Tm.let₁ v x) _)
      (((LetCase.LocallyNameless.Tm.rename_congr (fun i => Fin.cases rfl (fun _ => rfl) i) K).trans (LetCase.LocallyNameless.Tm.rename_id K)).symm))
      (.refl (.let₁ hv hK))
  | _, _, _, _, _, _, _, _, .unit next, _, _, _, _, hv, hK => next.let_plug_proof hv hK
  | _, _, _, _, _, _, _, _, .atom next, _, _, _, _, hv, hK => next.let_plug_proof hv hK
  | _, _, _, .cons top _, _, _, _, _, .step next, v, K, _, _, hv, hK =>
    (Equiv.bindLetPair (slotTyping top).toHasType (next.plug_typed_proof hv) hK).trans
      (Equiv.let₂ (.refl (slotTyping top).toHasType)
        (cast (congrArg (fun x => Equiv false Γ₀ _ (LetCase.LocallyNameless.Tm.let₁ (next.plug v) K.underBinder.underBinder)
            (next.plug (LetCase.LocallyNameless.Tm.let₁ v x)) _)
          (underBinder_twice_rename_up K next.weaken.toFun))
          (next.let_plug_proof hv hK.underBinder.underBinder)))
  | _, _, _, _, _, _, _, _, .ask g argument reply, _, _, _, _, hv, hK =>
    (Equiv.bindLet (Derivation.op (f := g) (argTyping argument)).toHasType (reply.plug_typed_proof hv) hK).trans
      (Equiv.let₁ (.refl (Derivation.op (f := g) (argTyping argument)).toHasType)
        (reply.let_plug_proof hv hK))
  | _, _, _, _, _, _, _, _, .pick _ next, _, _, _, _, hv, hK => next.let_plug_proof hv hK

theorem SpelledPrefixTags.let_plug_proof : {stack : List (List α)} → {tags : List (List α)} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {stack' : List (List α)} → {m' : Nat} →
    {Δ' : BoundCtx (Ty α) m'} → {holds' : Holds Δ' stack'} →
    (p : SpelledPrefixTags (Φ := Φ) stack tags Δ holds stack' Δ' holds') → {v : LetCase.LocallyNameless.Tm Empty Φ m'} →
    {K : LetCase.LocallyNameless.Tm Empty Φ (m + 1)} → {J C : Ty α} → HasType Φ Γ₀ Δ' v J → HasType Φ Γ₀ (Δ.snoc J) K C →
    Equiv false Γ₀ (Δ.snoc (tagsTy tags)) (.let₁ (p.plug v) K.underBinder)
      (p.plug (.let₁ v (K.rename (LetCase.LocallyNameless.Tm.up p.weaken.toFun)))) C
  | _, _, _, _, _, _, _, _, _, .bind _ next, v, K, _, _, hv, hK =>
    cast (congrArg (fun x => Equiv false Γ₀ _ (LetCase.LocallyNameless.Tm.let₁ (next.plug v) K.underBinder) (next.plug (LetCase.LocallyNameless.Tm.let₁ v x)) _)
        (underBinder_rename_up K next.weaken.toFun))
      (next.let_plug_proof hv hK.underBinder)

end

/-- A let that binds a slot is the body with its newest slot renamed to
that slot. Pure-let beta at a slot. -/
theorem let_slot_proof {m : Nat} {Δ : BoundCtx (Ty α) m} {J C : Ty α} (i : Slot Δ J)
    {K : LetCase.LocallyNameless.Tm Empty Φ (m + 1)} (hK : HasType Φ Γ₀ (Δ.snoc J) K C) :
    Equiv false Γ₀ Δ (.let₁ (.bv i.1) K) (K.rename (Fin.cases i.1 (fun j => j))) C := by
  have beta := Equiv.letBeta (pureEff := false) Pure.bv (slotTyping i).toHasType hK
  have moved : LetCase.LocallyNameless.Tm.instantiate K (.bv i.1) = K.rename (Fin.cases i.1 (fun j => j)) := by
    simp only [LetCase.LocallyNameless.Tm.instantiate]
    refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun j => ?_) K).trans
      (LetCase.LocallyNameless.Tm.bsubst_bv_eq_rename (Fin.cases i.1 (fun j => j)) K)
    exact Fin.cases rfl (fun _ => rfl) j
  rwa [moved] at beta

/-- A let whose bound term is a prefix around a slot is the prefix around
the body, with the body weakened past the slots of the prefix and its
newest slot renamed to that slot. -/
theorem SpelledPrefix.let_plug_slot_proof {stack : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m}
    {holds : Holds Δ stack} {stack' : List (List α)} {m' : Nat} {Δ' : BoundCtx (Ty α) m'}
    {holds' : Holds Δ' stack'} (p : SpelledPrefix (Φ := Φ) stack Δ holds stack' Δ' holds') {J C : Ty α}
    (top : Slot Δ' J) {K : LetCase.LocallyNameless.Tm Empty Φ (m + 1)} (hK : HasType Φ Γ₀ (Δ.snoc J) K C) :
    Equiv false Γ₀ Δ (.let₁ (p.plug (.bv top.1)) K)
      (p.plug (K.rename (Fin.cases top.1 p.weaken.toFun))) C :=
  (p.let_plug_proof (slotTyping top).toHasType hK).trans
    (p.plug_congr_proof
      (cast (congrArg (fun x => Equiv false Γ₀ Δ' (LetCase.LocallyNameless.Tm.let₁ (.bv top.1) (K.rename (LetCase.LocallyNameless.Tm.up p.weaken.toFun))) x C)
          ((LetCase.LocallyNameless.Tm.rename_comp _ _ K).trans (LetCase.LocallyNameless.Tm.rename_congr (fun i => Fin.cases rfl (fun _ => rfl) i) K)))
        (let_slot_proof top (HasType.rename (p.weaken.up J) hK))))

/-! ## The join is inlined

A let whose bound term is a case on a slot, with a prefix around a
supplied slot in each arm, is natively equal to the case with, in each
arm, the prefix around the body renamed into the arm. The case is pulled
out of the bound term by the native sequencing law, and each arm is
handled by the equation above. -/

theorem join_inline_proof {stackA stackB : List (List α)} {m : Nat} {Γ : BoundCtx (Ty α) m} {A B J C : Ty α}
    (y : Slot Γ (.coprod A B)) {holdsA : Holds (Γ.snoc A) stackA} {stackA' : List (List α)} {mA : Nat}
    {ΔA : BoundCtx (Ty α) mA} {holdsA' : Holds ΔA stackA'}
    (left : SpelledPrefix (Φ := Φ) stackA (Γ.snoc A) holdsA stackA' ΔA holdsA') (topA : Slot ΔA J)
    {holdsB : Holds (Γ.snoc B) stackB} {stackB' : List (List α)} {mB : Nat} {ΔB : BoundCtx (Ty α) mB}
    {holdsB' : Holds ΔB stackB'}
    (right : SpelledPrefix (Φ := Φ) stackB (Γ.snoc B) holdsB stackB' ΔB holdsB') (topB : Slot ΔB J)
    {K : LetCase.LocallyNameless.Tm Empty Φ (m + 1)} (hK : HasType Φ Γ₀ (Γ.snoc J) K C) :
    Equiv false Γ₀ Γ (.let₁ (.case (.bv y.1) (left.plug (.bv topA.1)) (right.plug (.bv topB.1))) K)
      (.case (.bv y.1) (left.plug (K.rename (joinRenaming left.weaken topA).toFun))
        (right.plug (K.rename (joinRenaming right.weaken topB).toFun))) C :=
  (Equiv.bindLetCase (slotTyping y).toHasType (left.plug_typed_proof (slotTyping topA).toHasType)
      (right.plug_typed_proof (slotTyping topB).toHasType) hK).trans
    (Equiv.case (.refl (slotTyping y).toHasType)
      (cast (congrArg (fun x => Equiv false Γ₀ (Γ.snoc A) (LetCase.LocallyNameless.Tm.let₁ (left.plug (.bv topA.1)) K.underBinder)
          (left.plug x) C)
          ((LetCase.LocallyNameless.Tm.rename_comp _ _ K).trans (LetCase.LocallyNameless.Tm.rename_congr (fun i => Fin.cases rfl (fun _ => rfl) i) K)))
        (left.let_plug_slot_proof topA hK.underBinder))
      (cast (congrArg (fun x => Equiv false Γ₀ (Γ.snoc B) (LetCase.LocallyNameless.Tm.let₁ (right.plug (.bv topB.1)) K.underBinder)
          (right.plug x) C)
          ((LetCase.LocallyNameless.Tm.rename_comp _ _ K).trans (LetCase.LocallyNameless.Tm.rename_congr (fun i => Fin.cases rfl (fun _ => rfl) i) K)))
        (right.let_plug_slot_proof topB hK.underBinder)))

/-- A join is natively equal to its expansion. -/
theorem SpelledJoinTags.equiv_expand_proof {atoms next : List α} : {stack : List (List α)} →
    {tags : List (List α)} → {m : Nat} → {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {s : Fin m} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (m + 1)} → (j : SpelledJoinTags atoms next stack tags Δ holds s L t) →
    Equiv false Γ₀ (Δ.snoc (tagsTy tags)) t j.inlined (packedExitType L)
  | _, _, _, _, _, _, _, .join _ _ _ (topA := topA) (topB := topB) left _ right _ rest =>
    join_inline_proof ⟨0, rfl⟩ left topA right topB rest.typing.toHasType

/-! ## Ranked validity of a typed term natively equal to a spelled tree -/

/-- The graph read back from a typed term that is natively equal to a
spelled tree and the graph read back from a spelled tree are valid
together exactly when the two trees have the same normal form. -/
theorem rankedValid_expanded_iff_proof {n : Nat} {β : BoundCtx (Ty α) n} {t t' u : LetCase.LocallyNameless.Tm Empty Φ n}
    (separable : Separable β) (typing : Derivation Φ Γ₀ β t (packedExitType L)) (d : Spelled β L t')
    (same : Equiv false Γ₀ β t t' (packedExitType L)) (q : Spelled β L u) :
    RankedValid false (sentenceOf (entryOf (CheckedTable.ofLetCase d.exits_ne_nil typing))
        (entryOf q.graph)) ↔
      (d.normal (.id β)).1 = (q.normal (.id β)).1 :=
  (rankedValid_spelled_iff separable (entryOf (CheckedTable.ofLetCase d.exits_ne_nil typing))
      (entryOf q.graph)
      ⟨t', d, (CheckedTable.ofLetCase_emit false d.exits_ne_nil typing).trans same⟩ (spelled_graph q)).trans
    (Iff.trans
      ⟨fun h => (same.symm.trans ((CheckedTable.ofLetCase_emit false d.exits_ne_nil typing).symm.trans h)).trans
          (CheckedTable.ofLetCase_emit false q.exits_ne_nil q.typing),
        fun h => ((CheckedTable.ofLetCase_emit false d.exits_ne_nil typing).trans (same.trans h)).trans
          (CheckedTable.ofLetCase_emit false q.exits_ne_nil q.typing).symm⟩
      (spelled_equiv_iff_normal separable d q))

/-- At the ordered trace model with atoms, the two graphs have the same
ordered-exit arrow exactly when the two trees have the same normal
form. -/
theorem denoteRanked_expanded_iff_proof {n : Nat} {β : BoundCtx (Ty α) n} {t t' u : LetCase.LocallyNameless.Tm Empty Φ n}
    (separable : Separable β) (typing : Derivation Φ Γ₀ β t (packedExitType L)) (d : Spelled β L t')
    (same : Equiv false Γ₀ β t t' (packedExitType L)) (q : Spelled β L u) :
    denoteRanked (traceJ (α := α) (Φ := Φ)) (atomTraceModel α Φ)
        (entryOf (CheckedTable.ofLetCase d.exits_ne_nil typing)) =
        denoteRanked (traceJ (α := α) (Φ := Φ)) (atomTraceModel α Φ) (entryOf q.graph) ↔
      (d.normal (.id β)).1 = (q.normal (.id β)).1 :=
  (rankedValid_spelled_iff_atomTrace separable (entryOf (CheckedTable.ofLetCase d.exits_ne_nil typing))
      (entryOf q.graph)
      ⟨t', d, (CheckedTable.ofLetCase_emit false d.exits_ne_nil typing).trans same⟩
      (spelled_graph q)).symm.trans (rankedValid_expanded_iff_proof separable typing d same q)

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
