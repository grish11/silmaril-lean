module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Direct.Renaming.Defs

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open Region (packedExitType)
open LetCase.LocallyNameless (Derivation Equiv HasType Pure)
open LetCase.Structural.Reply (Γ₀)
open LetSeq.StraightLine.Structural (Slot Assembly)
open scoped LetSeq.StraightLine.Structural Tagged Binary

variable {α Φ : Type} [TaggedSignature α Φ] {L : List (Ty α)}

/-! ## The normal form of a renamed tree

The normal form of a renamed spelled tree along a renaming is the normal
form of the tree along the composite. The proof follows the action, one
family at a time. -/

mutual

theorem Spelled.renamed_normal_proof : {n : Nat} → {β : BoundCtx (Ty α) n} → {t : LetCase.LocallyNameless.Tm Empty Φ n} →
    (d : Spelled β L t) → {m : Nat} → {γ : BoundCtx (Ty α) m} → {k : Nat} → {δ : BoundCtx (Ty α) k} →
    (ρ : BoundCtx.Renaming β γ) → (π : BoundCtx.Renaming γ δ) →
    (d.renamed ρ).tree.normal π = d.normal (ρ.comp π)
  | _, _, _, .ret exit payload, _, _, _, _, ρ, π => by
    simp only [Spelled.renamed, Spelled.normal]
    rw [assembly_rename_comp]
  | _, _, _, .ask f argument head, _, _, _, _, ρ, π => by
    have h := head.renamed_normal_proof ρ (.op f (argTerm (argument.rename ρ)))
      (congrArg (LetCase.LocallyNameless.Tm.op f) (argTerm_rename argument ρ)).symm π
    simp only [Spelled.renamed, Spelled.normal]
    rw [assembly_rename_comp, h]
  | _, _, _, .chain c, _, _, _, _, ρ, π => by
    have h := c.renamed_opened_proof ρ .nil rfl π
    simp only [Spelled.renamed, Spelled.normal]
    exact h

theorem SpelledHead.renamed_normal_proof : {n : Nat} → {β : BoundCtx (Ty α) n} → {tags : List (List α)} →
    {e t : LetCase.LocallyNameless.Tm Empty Φ n} → (d : SpelledHead tags e β L t) → {m : Nat} → {γ : BoundCtx (Ty α) m} →
    {k : Nat} → {δ : BoundCtx (Ty α) k} → (ρ : BoundCtx.Renaming β γ) → (e' : LetCase.LocallyNameless.Tm Empty Φ m) →
    (he : e' = e.rename ρ.toFun) → (π : BoundCtx.Renaming γ δ) →
    (d.renamed ρ e' he).tree.normal π = d.normal (ρ.comp π)
  | _, _, _, _, _, .bind reply, _, _, _, _, ρ, _, _, π => by
    have h := reply.renamed_normal_proof ρ π
    simp only [SpelledHead.renamed, SpelledHead.normal]
    exact h
  | _, _, _, _, _, .destruct a b rest later, _, _, _, _, ρ, _, _, π => by
    have h := later.renamed_normal_proof (ρ.up (.base a)) (armRenaming π (tupleTy (a :: b :: rest)) (.base a))
    have e : (ρ.up (.base a)).comp (armRenaming π (tupleTy (a :: b :: rest)) (.base a)) =
        armRenaming (ρ.comp π) (tupleTy (a :: b :: rest)) (.base a) :=
      renaming_ext (Fin.cases rfl (fun _ => rfl))
    rw [e] at h
    simp only [SpelledHead.renamed, SpelledHead.normal]
    rw [h]
  | _, _, _, _, _, .branch atoms next rest left right, _, _, _, δ, ρ, _, _, π => by
    have hl := left.renamed_normal_proof ρ (π.comp (BoundCtx.Renaming.succ δ (tagsTy (atoms :: next :: rest))))
    have hr := right.renamed_normal_proof ρ (π.comp (BoundCtx.Renaming.succ δ (tagsTy (atoms :: next :: rest))))
    simp only [SpelledHead.renamed, SpelledHead.normal]
    rw [hl, hr]
    rfl

theorem SpelledTags.renamed_normal_proof : {n : Nat} → {β : BoundCtx (Ty α) n} → {tags : List (List α)} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)} → (d : SpelledTags tags β L t) → {m : Nat} → {γ : BoundCtx (Ty α) m} →
    {k : Nat} → {δ : BoundCtx (Ty α) k} → (ρ : BoundCtx.Renaming β γ) → (π : BoundCtx.Renaming γ δ) →
    (d.renamed ρ).tree.normal π = d.normal (ρ.comp π)
  | _, _, _, _, .only atoms payload, _, _, _, _, ρ, π => by
    have h := payload.renamed_normal_proof ρ π
    simp only [SpelledTags.renamed, SpelledTags.normal]
    rw [h]
  | _, _, _, _, .split atoms next rest left right, _, _, _, _, ρ, π => by
    have hl := left.renamed_normal_proof (ρ.up (tagsTy (atoms :: next :: rest))) (π.up _)
    have hr := right.renamed_normal_proof (ρ.up (tagsTy (atoms :: next :: rest))) (π.up _)
    rw [renaming_up_comp] at hl hr
    simp only [SpelledTags.renamed, SpelledTags.normal]
    rw [hl, hr]

theorem SpelledTuple.renamed_normal_proof : {n : Nat} → {β : BoundCtx (Ty α) n} → {atoms : List α} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)} → (d : SpelledTuple atoms β L t) → {m : Nat} → {γ : BoundCtx (Ty α) m} →
    {k : Nat} → {δ : BoundCtx (Ty α) k} → (ρ : BoundCtx.Renaming β γ) → (π : BoundCtx.Renaming γ δ) →
    (d.renamed ρ).tree.normal π = d.normal (ρ.comp π)
  | _, _, _, _, .unit body, _, _, _, _, ρ, π => by
    have h := body.renamed_normal_proof (ρ.up (tupleTy ([] : List α))) (π.up _)
    rw [renaming_up_comp] at h
    simp only [SpelledTuple.renamed, SpelledTuple.normal]
    rw [h]
  | _, _, _, _, .atom a body, _, _, _, _, ρ, π => by
    have h := body.renamed_normal_proof (ρ.up (tupleTy [a])) (π.up _)
    rw [renaming_up_comp] at h
    simp only [SpelledTuple.renamed, SpelledTuple.normal]
    rw [h]
  | _, _, _, _, .pair a b rest later, _, _, _, _, ρ, π => by
    have h := later.renamed_normal_proof ((ρ.up (tupleTy (a :: b :: rest))).up (.base a)) ((π.up _).up _)
    rw [renaming_up_comp, renaming_up_comp] at h
    simp only [SpelledTuple.renamed, SpelledTuple.normal]
    rw [h]
  | _, _, _, _, .hold atoms chain, _, _, _, _, ρ, π => by
    have h := chain.renamed_opened_proof (ρ.up (tupleTy atoms)) (.cons ⟨0, rfl⟩ .nil) rfl (π.up (tupleTy atoms))
    rw [renaming_up_comp] at h
    simp only [SpelledTuple.renamed, SpelledTuple.normal]
    rw [h]

theorem SpelledStack.renamed_opened_proof : {stack : List (List α)} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {holds : Holds Δ stack} → {t : LetCase.LocallyNameless.Tm Empty Φ m} → (d : SpelledStack stack Δ holds L t) → {k : Nat} →
    {Θ : BoundCtx (Ty α) k} → {j : Nat} → {Ξ : BoundCtx (Ty α) j} → (ρ : BoundCtx.Renaming Δ Θ) →
    (holds' : Holds Θ stack) → (h : holds.rename ρ = holds') → (π : BoundCtx.Renaming Θ Ξ) →
    (d.renamed ρ holds' h).tree.opened π = d.opened (ρ.comp π)
  | _, _, _, _, _, .done body, _, _, _, _, ρ, .nil, _, π => by
    have ih := body.renamed_normal_proof ρ π
    simp only [SpelledStack.renamed, SpelledStack.opened]
    exact ih
  | _, _, _, .cons _ _, _, .unit next, _, _, _, _, ρ, .cons _ older', h, π =>
    next.renamed_opened_proof ρ older' (Holds.cons.inj h).2 π
  | _, _, _, .cons _ _, _, .atom next, _, _, _, _, ρ, .cons _ older', h, π =>
    next.renamed_opened_proof ρ older' (Holds.cons.inj h).2 π
  | (a :: b :: rest) :: stack, _, _, .cons _ older, _, .step next, _, Θ, _, Ξ, ρ, .cons _ older', h, π => by
    have ih := next.renamed_opened_proof ((ρ.up (.base a)).up (tupleTy (b :: rest)))
      (.cons ⟨0, rfl⟩ (older'.rename (pastPair Θ (.base a) (tupleTy (b :: rest)))))
      (congrArg (Holds.cons ⟨0, rfl⟩) (holds_square older (pastPair Θ (.base a) (tupleTy (b :: rest)))
        (Holds.cons.inj h).2 (renaming_ext (fun _ => rfl))))
      ((π.up (.base a)).up (tupleTy (b :: rest)))
    rw [renaming_up_comp, renaming_up_comp] at ih
    exact congrArg (fun r : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree .body _ L u =>
      CaseTree.renamed (pending := .body) r.2
        (upTele (swapStack stack Ξ [.base a, tupleTy (b :: rest)]) (pairsTele (b :: rest)))) ih
  | _, _, _, _, _, .ask g argument reply, _, _, _, _, ρ, holds', h, π => by
    have ih := reply.renamed_opened_proof ρ holds' h π
    simp only [SpelledStack.renamed, SpelledStack.opened]
    rw [assembly_rename_comp, ih]
    rfl
  | _, _, _, holds, _, .pick sel next, _, _, _, _, ρ, holds', h, π => by
    have ih := next.renamed_opened_proof ρ (holds'.select sel)
      ((Holds.select_rename sel holds ρ).symm.trans (congrArg (Holds.select sel) h)) π
    simp only [SpelledStack.renamed, SpelledStack.opened]
    rw [ih]

theorem SpelledStackTags.renamed_opened_proof : {stack : List (List α)} → {tags : List (List α)} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {t : LetCase.LocallyNameless.Tm Empty Φ (m + 1)} →
    (d : SpelledStackTags stack tags Δ holds L t) → {k : Nat} → {Θ : BoundCtx (Ty α) k} → {j : Nat} →
    {Ξ : BoundCtx (Ty α) j} → (ρ : BoundCtx.Renaming Δ Θ) → (holds' : Holds Θ stack) →
    (h : holds.rename ρ = holds') → (π : BoundCtx.Renaming Θ Ξ) →
    (d.renamed ρ holds' h).tree.opened π = d.opened (ρ.comp π)
  | _, _, _, _, holds, _, .bind atoms next, _, Θ, _, _, ρ, holds', h, π => by
    have ih := next.renamed_opened_proof (ρ.up (tupleTy atoms))
      (.cons ⟨0, rfl⟩ (holds'.rename (BoundCtx.Renaming.succ Θ (tupleTy atoms))))
      (congrArg (Holds.cons ⟨0, rfl⟩) (holds_square holds (BoundCtx.Renaming.succ Θ (tupleTy atoms)) h
        (renaming_ext (fun _ => rfl)))) (π.up (tupleTy atoms))
    rw [renaming_up_comp] at ih
    simp only [SpelledStackTags.renamed, SpelledStackTags.opened]
    rw [ih]
  | _, _, _, _, holds, _, .split atoms next more left right, _, Θ, _, _, ρ, holds', h, π => by
    have ihl := left.renamed_opened_proof ((ρ.up (tagsTy (atoms :: next :: more))).up (tupleTy atoms))
      (.cons ⟨0, rfl⟩ (holds'.rename (pastPair Θ (tagsTy (atoms :: next :: more)) (tupleTy atoms))))
      (congrArg (Holds.cons ⟨0, rfl⟩) (holds_square holds
        (pastPair Θ (tagsTy (atoms :: next :: more)) (tupleTy atoms)) h (renaming_ext (fun _ => rfl))))
      ((π.up (tagsTy (atoms :: next :: more))).up (tupleTy atoms))
    have ihr := right.renamed_opened_proof (ρ.up (tagsTy (atoms :: next :: more)))
      (holds'.rename (BoundCtx.Renaming.succ Θ (tagsTy (atoms :: next :: more))))
      (holds_square holds (BoundCtx.Renaming.succ Θ (tagsTy (atoms :: next :: more))) h
        (renaming_ext (fun _ => rfl))) (π.up (tagsTy (atoms :: next :: more)))
    rw [renaming_up_comp, renaming_up_comp] at ihl
    rw [renaming_up_comp] at ihr
    simp only [SpelledStackTags.renamed, SpelledStackTags.opened]
    rw [ihl, ihr]
  | _, tags, _, _, _, _, .later g argument arms, _, _, _, _, ρ, holds', h, π => by
    have ih := arms.renamed_opened_proof ρ holds' h π
      ((argument.rename (ρ.up (tagsTy tags))).rename (π.up (tagsTy tags)))
    simp only [SpelledStackTags.renamed, SpelledStackTags.opened]
    rw [ih, assembly_rename_comp, renaming_up_comp]
  | _, _, _, _, holds, _, .deferred atoms next more shape left right hl hr, _, Θ, _, _, ρ, holds', h, π => by
    have ihl := left.renamed_opened_proof ((ρ.up (tagsTy (atoms :: next :: more))).up (tupleTy atoms))
      (.cons ⟨0, rfl⟩ (holds'.rename (pastPair Θ (tagsTy (atoms :: next :: more)) (tupleTy atoms))))
      (congrArg (Holds.cons ⟨0, rfl⟩) (holds_square holds
        (pastPair Θ (tagsTy (atoms :: next :: more)) (tupleTy atoms)) h (renaming_ext (fun _ => rfl))))
      ((π.up (tagsTy (atoms :: next :: more))).up (tupleTy atoms))
    have ihr := right.renamed_opened_proof (ρ.up (tagsTy (atoms :: next :: more)))
      (holds'.rename (BoundCtx.Renaming.succ Θ (tagsTy (atoms :: next :: more))))
      (holds_square holds (BoundCtx.Renaming.succ Θ (tagsTy (atoms :: next :: more))) h
        (renaming_ext (fun _ => rfl))) (π.up (tagsTy (atoms :: next :: more)))
    rw [renaming_up_comp, renaming_up_comp] at ihl
    rw [renaming_up_comp] at ihr
    simp only [SpelledStackTags.renamed, SpelledStackTags.opened]
    rw [ihl, ihr]

theorem SpelledLaterTags.renamed_opened_proof : {stack : List (List α)} → {tags : List (List α)} → {g : Φ} →
    {m : Nat} → {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {t : LetCase.LocallyNameless.Tm Empty Φ (m + 1 + 1)} →
    (d : SpelledLaterTags stack tags g Δ holds L t) → {k : Nat} → {Θ : BoundCtx (Ty α) k} → {j : Nat} →
    {Ξ : BoundCtx (Ty α) j} → (ρ : BoundCtx.Renaming Δ Θ) → (holds' : Holds Θ stack) →
    (h : holds.rename ρ = holds') → (π : BoundCtx.Renaming Θ Ξ) →
    (arg : Assembly (Ξ.snoc (tagsTy tags)) (instrSrc g)) →
    (d.renamed ρ holds' h).tree.opened π arg = d.opened (ρ.comp π) arg
  | _, _, _, _, _, holds, _, .only atoms next, _, Θ, _, _, ρ, holds', h, π, arg => by
    have ih := next.renamed_opened_proof (ρ.up (tupleTy atoms))
      (.cons ⟨0, rfl⟩ (holds'.rename (BoundCtx.Renaming.succ Θ (tupleTy atoms))))
      (congrArg (Holds.cons ⟨0, rfl⟩) (holds_square holds (BoundCtx.Renaming.succ Θ (tupleTy atoms)) h
        (renaming_ext (fun _ => rfl)))) (π.up (tupleTy atoms))
    rw [renaming_up_comp] at ih
    simp only [SpelledLaterTags.renamed, SpelledLaterTags.opened]
    rw [ih]
  | _, _, _, _, _, holds, _, .split atoms next more left right, _, Θ, _, Ξ, ρ, holds', h, π, arg => by
    have ihl := left.renamed_opened_proof ((ρ.up (tagsTy (atoms :: next :: more))).up (tupleTy atoms))
      (.cons ⟨0, rfl⟩ (holds'.rename (pastPair Θ (tagsTy (atoms :: next :: more)) (tupleTy atoms))))
      (congrArg (Holds.cons ⟨0, rfl⟩) (holds_square holds
        (pastPair Θ (tagsTy (atoms :: next :: more)) (tupleTy atoms)) h (renaming_ext (fun _ => rfl))))
      ((π.up (tagsTy (atoms :: next :: more))).up (tupleTy atoms))
    have ihr := right.renamed_opened_proof (ρ.up (tagsTy (atoms :: next :: more)))
      (holds'.rename (BoundCtx.Renaming.succ Θ (tagsTy (atoms :: next :: more))))
      (holds_square holds (BoundCtx.Renaming.succ Θ (tagsTy (atoms :: next :: more))) h
        (renaming_ext (fun _ => rfl))) (π.up (tagsTy (atoms :: next :: more)))
      (arg.rename (BoundCtx.Renaming.succ (Ξ.snoc (tagsTy (atoms :: next :: more))) (tagsTy (next :: more))))
    rw [renaming_up_comp, renaming_up_comp] at ihl
    rw [renaming_up_comp] at ihr
    simp only [SpelledLaterTags.renamed, SpelledLaterTags.opened]
    rw [ihl, ihr]

end

/-! ## The renamed prefix

The end renaming of a renamed prefix commutes with the weakenings of the
two prefixes, and the term of the renamed prefix around a term renamed
along the end renaming is the renamed term of the prefix. -/

mutual

theorem SpelledPrefix.renamed_weaken_proof : {stack : List (List α)} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {holds : Holds Δ stack} → {stack' : List (List α)} → {m' : Nat} → {Δ' : BoundCtx (Ty α) m'} →
    {holds' : Holds Δ' stack'} → (p : SpelledPrefix (Φ := Φ) stack Δ holds stack' Δ' holds') → {k : Nat} →
    {Θ : BoundCtx (Ty α) k} → (ρ : BoundCtx.Renaming Δ Θ) → (H : Holds Θ stack) → (h : holds.rename ρ = H) →
    p.weaken.comp (p.renamed ρ H h).ren = ρ.comp (p.renamed ρ H h).tree.weaken
  | _, _, _, _, _, _, _, _, .stop, _, _, _, _, _ => renaming_ext (fun _ => rfl)
  | _, _, _, .cons _ _, _, _, _, _, .unit next, _, _, ρ, .cons _ older', h =>
    next.renamed_weaken_proof ρ older' (Holds.cons.inj h).2
  | _, _, _, .cons _ _, _, _, _, _, .atom next, _, _, ρ, .cons _ older', h =>
    next.renamed_weaken_proof ρ older' (Holds.cons.inj h).2
  | (a :: b :: rest) :: _, _, Δ, .cons _ older, _, _, _, _, .step next, _, Θ, ρ, .cons _ older', h =>
    (congrArg (fun r => (pastPair Δ (.base a) (tupleTy (b :: rest))).comp r)
      (next.renamed_weaken_proof ((ρ.up (.base a)).up (tupleTy (b :: rest)))
        (.cons ⟨0, rfl⟩ (older'.rename (pastPair Θ (.base a) (tupleTy (b :: rest)))))
        (congrArg (Holds.cons ⟨0, rfl⟩) (holds_square older (pastPair Θ (.base a) (tupleTy (b :: rest)))
          (Holds.cons.inj h).2 (renaming_ext (fun _ => rfl)))))).trans (renaming_ext (fun _ => rfl))
  | _, _, _, _, _, _, _, _, .ask _ _ reply, _, _, ρ, H, h => reply.renamed_weaken_proof ρ H h
  | _, _, _, holds, _, _, _, _, .pick sel next, _, _, ρ, H, h =>
    next.renamed_weaken_proof ρ (H.select sel)
      ((Holds.select_rename sel holds ρ).symm.trans (congrArg (Holds.select sel) h))

theorem SpelledPrefixTags.renamed_weaken_proof : {stack : List (List α)} → {tags : List (List α)} →
    {m : Nat} → {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {stack' : List (List α)} → {m' : Nat} →
    {Δ' : BoundCtx (Ty α) m'} → {holds' : Holds Δ' stack'} →
    (p : SpelledPrefixTags (Φ := Φ) stack tags Δ holds stack' Δ' holds') → {k : Nat} →
    {Θ : BoundCtx (Ty α) k} → (ρ : BoundCtx.Renaming Δ Θ) → (H : Holds Θ stack) → (h : holds.rename ρ = H) →
    p.weaken.comp (p.renamed ρ H h).ren = ρ.comp (p.renamed ρ H h).tree.weaken
  | _, _, _, Δ, holds, _, _, _, _, .bind atoms next, _, Θ, ρ, H, h =>
    (congrArg (fun r => (BoundCtx.Renaming.succ Δ (tupleTy atoms)).comp r)
      (next.renamed_weaken_proof (ρ.up (tupleTy atoms))
        (.cons ⟨0, rfl⟩ (H.rename (BoundCtx.Renaming.succ Θ (tupleTy atoms))))
        (congrArg (Holds.cons ⟨0, rfl⟩) (holds_square holds (BoundCtx.Renaming.succ Θ (tupleTy atoms)) h
          (renaming_ext (fun _ => rfl)))))).trans (renaming_ext (fun _ => rfl))

end

mutual

theorem SpelledPrefix.renamed_plug_proof : {stack : List (List α)} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {holds : Holds Δ stack} → {stack' : List (List α)} → {m' : Nat} → {Δ' : BoundCtx (Ty α) m'} →
    {holds' : Holds Δ' stack'} → (p : SpelledPrefix (Φ := Φ) stack Δ holds stack' Δ' holds') → {k : Nat} →
    {Θ : BoundCtx (Ty α) k} → (ρ : BoundCtx.Renaming Δ Θ) → (H : Holds Θ stack) → (h : holds.rename ρ = H) →
    (e : LetCase.LocallyNameless.Tm Empty Φ m') →
    (p.plug e).rename ρ.toFun = (p.renamed ρ H h).tree.plug (e.rename (p.renamed ρ H h).ren.toFun)
  | _, _, _, _, _, _, _, _, .stop, _, _, _, _, _, _ => rfl
  | _, _, _, .cons _ _, _, _, _, _, .unit next, _, _, ρ, .cons _ older', h, e =>
    next.renamed_plug_proof ρ older' (Holds.cons.inj h).2 e
  | _, _, _, .cons _ _, _, _, _, _, .atom next, _, _, ρ, .cons _ older', h, e =>
    next.renamed_plug_proof ρ older' (Holds.cons.inj h).2 e
  | (a :: b :: rest) :: _, _, _, .cons _ older, _, _, _, _, .step next, _, Θ, ρ, .cons _ older', h, e =>
    congrArg₂ (fun i x => LetCase.LocallyNameless.Tm.let₂ (.bv i) x) (congrArg Subtype.val (Holds.cons.inj h).1)
      (next.renamed_plug_proof ((ρ.up (.base a)).up (tupleTy (b :: rest)))
        (.cons ⟨0, rfl⟩ (older'.rename (pastPair Θ (.base a) (tupleTy (b :: rest)))))
        (congrArg (Holds.cons ⟨0, rfl⟩) (holds_square older (pastPair Θ (.base a) (tupleTy (b :: rest)))
          (Holds.cons.inj h).2 (renaming_ext (fun _ => rfl)))) e)
  | _, _, _, _, _, _, _, _, .ask g argument reply, _, _, ρ, H, h, e =>
    congrArg₂ LetCase.LocallyNameless.Tm.let₁ (congrArg (LetCase.LocallyNameless.Tm.op g) (argTerm_rename argument ρ)) (reply.renamed_plug_proof ρ H h e)
  | _, _, _, holds, _, _, _, _, .pick sel next, _, _, ρ, H, h, e =>
    next.renamed_plug_proof ρ (H.select sel)
      ((Holds.select_rename sel holds ρ).symm.trans (congrArg (Holds.select sel) h)) e

theorem SpelledPrefixTags.renamed_plug_proof : {stack : List (List α)} → {tags : List (List α)} →
    {m : Nat} → {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {stack' : List (List α)} → {m' : Nat} →
    {Δ' : BoundCtx (Ty α) m'} → {holds' : Holds Δ' stack'} →
    (p : SpelledPrefixTags (Φ := Φ) stack tags Δ holds stack' Δ' holds') → {k : Nat} →
    {Θ : BoundCtx (Ty α) k} → (ρ : BoundCtx.Renaming Δ Θ) → (H : Holds Θ stack) → (h : holds.rename ρ = H) →
    (e : LetCase.LocallyNameless.Tm Empty Φ m') →
    (p.plug e).rename (LetCase.LocallyNameless.Tm.up ρ.toFun) = (p.renamed ρ H h).tree.plug (e.rename (p.renamed ρ H h).ren.toFun)
  | _, _, _, _, holds, _, _, _, _, .bind atoms next, _, Θ, ρ, H, h, e =>
    next.renamed_plug_proof (ρ.up (tupleTy atoms))
      (.cons ⟨0, rfl⟩ (H.rename (BoundCtx.Renaming.succ Θ (tupleTy atoms))))
      (congrArg (Holds.cons ⟨0, rfl⟩) (holds_square holds (BoundCtx.Renaming.succ Θ (tupleTy atoms)) h
        (renaming_ext (fun _ => rfl)))) e

end

/-! ## The specialization term and the renamed prefix

The specialization term of a prefix at a payload slot `Z`, renamed along
any renaming `τ` of the context with `Z` newest, is the term of the prefix
renamed along `τ` past `Z`, around the term at the end with its slots sent
along the end renaming and `Z` sent to the weakened image of `τ 0`. The
statement is over all `τ`, so that the induction renames each prefix once
and never composes two renamed prefixes. -/

mutual

theorem SpelledPrefix.special_renamed_proof (Z : Ty α) : {stack : List (List α)} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {stack' : List (List α)} → {m' : Nat} →
    {Δ' : BoundCtx (Ty α) m'} → {holds' : Holds Δ' stack'} →
    (p : SpelledPrefix (Φ := Φ) stack Δ holds stack' Δ' holds') → {k : Nat} → {Θ : BoundCtx (Ty α) k} →
    (τ : BoundCtx.Renaming (Δ.snoc Z) Θ) → (ρ : BoundCtx.Renaming Δ Θ) →
    (BoundCtx.Renaming.succ Δ Z).comp τ = ρ → (H : Holds Θ stack) → (h : holds.rename ρ = H) →
    (e : LetCase.LocallyNameless.Tm Empty Φ (m' + 1)) →
    (p.special Z e).rename τ.toFun = (p.renamed ρ H h).tree.plug
      (e.rename (Fin.cases ((p.renamed ρ H h).tree.weaken.toFun (τ.toFun 0)) (p.renamed ρ H h).ren.toFun))
  | _, _, _, _, _, _, _, _, .stop, _, _, τ, _, hρ, _, _, e => by
    subst hρ
    exact LetCase.LocallyNameless.Tm.rename_congr (fun i => Fin.cases rfl (fun _ => rfl) i) e
  | _, _, _, .cons _ _, _, _, _, _, .unit next, _, _, τ, ρ, hρ, .cons _ older', h, e =>
    next.special_renamed_proof Z τ ρ hρ older' (Holds.cons.inj h).2 e
  | _, _, _, .cons _ _, _, _, _, _, .atom next, _, _, τ, ρ, hρ, .cons _ older', h, e =>
    next.special_renamed_proof Z τ ρ hρ older' (Holds.cons.inj h).2 e
  | (a :: b :: rest) :: _, _, Δ, .cons top older, _, _, _, _, .step next, _, Θ, τ, ρ, hρ, .cons _ older', h,
      e => by
    subst hρ
    have ih := next.special_renamed_proof Z
      ((beforePairRenaming Δ Z (.base a) (tupleTy (b :: rest))).comp ((τ.up (.base a)).up (tupleTy (b :: rest))))
      ((((BoundCtx.Renaming.succ Δ Z).comp τ).up (.base a)).up (tupleTy (b :: rest)))
      (renaming_ext (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))))
      (.cons ⟨0, rfl⟩ (older'.rename (pastPair Θ (.base a) (tupleTy (b :: rest)))))
      (congrArg (Holds.cons ⟨0, rfl⟩) (holds_square older (pastPair Θ (.base a) (tupleTy (b :: rest)))
        (Holds.cons.inj h).2 (renaming_ext (fun _ => rfl)))) e
    exact congrArg₂ (fun i x => LetCase.LocallyNameless.Tm.let₂ (.bv i) x) (congrArg Subtype.val (Holds.cons.inj h).1)
      ((LetCase.LocallyNameless.Tm.rename_comp beforePair (LetCase.LocallyNameless.Tm.up (LetCase.LocallyNameless.Tm.up τ.toFun)) (next.special Z e)).trans ih)
  | _, _, Δ, _, _, _, _, _, .ask g argument reply, _, _, τ, ρ, hρ, H, h, e => by
    have ih := reply.special_renamed_proof Z τ ρ hρ H h e
    subst hρ
    exact congrArg₂ LetCase.LocallyNameless.Tm.let₁
      (congrArg (LetCase.LocallyNameless.Tm.op g) ((argTerm_rename (argument.rename (BoundCtx.Renaming.succ Δ Z)) τ).trans
        (congrArg argTerm (assembly_rename_comp argument (BoundCtx.Renaming.succ Δ Z) τ)))) ih
  | _, _, _, holds, _, _, _, _, .pick sel next, _, _, τ, ρ, hρ, H, h, e =>
    next.special_renamed_proof Z τ ρ hρ (H.select sel)
      ((Holds.select_rename sel holds ρ).symm.trans (congrArg (Holds.select sel) h)) e

theorem SpelledPrefixTags.special_renamed_proof (Z : Ty α) : {stack : List (List α)} →
    {tags : List (List α)} → {m : Nat} → {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} →
    {stack' : List (List α)} → {m' : Nat} → {Δ' : BoundCtx (Ty α) m'} → {holds' : Holds Δ' stack'} →
    (p : SpelledPrefixTags (Φ := Φ) stack tags Δ holds stack' Δ' holds') → {k : Nat} →
    {Θ : BoundCtx (Ty α) k} → (τ : BoundCtx.Renaming (Δ.snoc Z) Θ) → (ρ : BoundCtx.Renaming Δ Θ) →
    (BoundCtx.Renaming.succ Δ Z).comp τ = ρ → (H : Holds Θ stack) → (h : holds.rename ρ = H) →
    (e : LetCase.LocallyNameless.Tm Empty Φ (m' + 1)) →
    ((p.special Z e).rename (swapRenaming Δ (tagsTy tags) Z).toFun).rename (LetCase.LocallyNameless.Tm.up τ.toFun) =
      (p.renamed ρ H h).tree.plug
        (e.rename (Fin.cases ((p.renamed ρ H h).tree.weaken.toFun (τ.toFun 0)) (p.renamed ρ H h).ren.toFun))
  | _, _, _, Δ, holds, _, _, _, _, .bind atoms next, _, Θ, τ, ρ, hρ, H, h, e => by
    subst hρ
    have ih := next.special_renamed_proof Z
      ((swapRenaming Δ (tupleTy atoms) Z).comp (τ.up (tupleTy atoms)))
      (((BoundCtx.Renaming.succ Δ Z).comp τ).up (tupleTy atoms))
      (renaming_ext (Fin.cases rfl (fun _ => rfl)))
      (.cons ⟨0, rfl⟩ (H.rename (BoundCtx.Renaming.succ Θ (tupleTy atoms))))
      (congrArg (Holds.cons ⟨0, rfl⟩) (holds_square holds (BoundCtx.Renaming.succ Θ (tupleTy atoms)) h
        (renaming_ext (fun _ => rfl)))) e
    exact (LetCase.LocallyNameless.Tm.rename_comp (swapRenaming Δ (tupleTy atoms) Z).toFun (LetCase.LocallyNameless.Tm.up τ.toFun) (next.special Z e)).trans ih

end

/-- The specialization term of a prefix at a payload slot is the term of
the prefix placed under the payload, around the term at the end with the
payload moved beneath the prefix. -/
theorem SpelledPrefix.special_eq_plug_proof (Z : Ty α) {stack : List (List α)} {m : Nat}
    {Δ : BoundCtx (Ty α) m} {holds : Holds Δ stack} {stack' : List (List α)} {m' : Nat}
    {Δ' : BoundCtx (Ty α) m'} {holds' : Holds Δ' stack'}
    (p : SpelledPrefix (Φ := Φ) stack Δ holds stack' Δ' holds') (e : LetCase.LocallyNameless.Tm Empty Φ (m' + 1)) :
    p.special Z e = (p.under Z).tree.plug (e.rename (p.past Z).toFun) :=
  (LetCase.LocallyNameless.Tm.rename_id (p.special Z e)).symm.trans
    (p.special_renamed_proof Z (.id (Δ.snoc Z)) (BoundCtx.Renaming.succ Δ Z) (renaming_ext (fun _ => rfl)) _ rfl e)

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
