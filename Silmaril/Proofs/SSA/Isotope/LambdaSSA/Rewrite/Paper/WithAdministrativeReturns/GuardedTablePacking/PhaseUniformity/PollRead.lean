module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.BitEntry.PollTable.Read.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.PollTable

/-! # The reader of the polling fragment is exact -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity (Eqv Step)
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open Paper.WithCaseBind.BitQuery (signature)
open Paper.TypeCategory (ofType ofRegion iterate sumIso phaseFold classFold coprod_desc_ofRegion
  iterate_uniformity_ofBranchValue)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)

local notation "N" => Step (τ := Ty Empty) (Φ := signature.Instr) false
local notation "π" => Paper.Extension.Singleton.projection (Step (τ := Ty Empty) (Φ := signature.Instr) false)

set_option backward.isDefEq.respectTransparency false
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (seqValueBranches caseValueBranches)
open Paper.TypeCategory (ofRegion_id ofRegion_comp)
open Paper.Extension.Singleton (iterateSum iterateSum_map)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open Paper.Extension.Singleton.Generation (exactCopair_ofRegion)

local notation "QLit" => Paper.Extension.Singleton.ofRegion (Step (τ := Ty Empty) (Φ := signature.Instr) false)
local notation "U" => (Ty.unit : Ty Empty)
open Paper.TypeCategory (iterate_roll)
open Silmaril.DeBruijn (lift)
open CfgEta.TypeCategory.Retained (distributorRegion distributorRegion_typed)
open CfgEta.TypeCategory (productSndBranches whiskerLeftRegion whiskerLeftRegion_typed)
open Paper.TypeCategory (whiskerLeft whiskerLeft_comp whiskerLeft_id whiskerLeft_ofRegion whiskerLeftFunctor
  tensorObj leftCoproductComparisonIso leftCoproductComparisonIso_hom leftCoproductComparisonIso_inv
  leftCoproductDistributor)
open Paper.TypeCategory.Projection (productSnd iterate_projected_whiskerLeft)
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
  (packedReadbackRep dispatcherRep orderedRow emptyDispatchRep)
open Paper.TypeCategory (sumInl sumInr blockRoute blockStep iterate_blockStep iterate_fixpoint)
open Paper.TypeCategory (whiskerLeft_iterate iterate_naturality)

/-! ## The pieces of the reader -/

theorem isBv0_eq {n : Nat} {t : STm (n + 1)} (h : isBv0 t = true) : t = .bv 0 := by
  cases t <;> simp [isBv0] at h
  rw [h]

theorem opLabel_eq (f : signature.Instr) : f = .ask (opLabel f) := by
  cases f
  rfl

theorem leafOfFin_fin (i : Fin 3) : (leafOfFin i).fin = i := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl

theorem fin_leafOfFin : (b : PollLeaf) → leafOfFin b.fin = b
  | .exit => rfl
  | .goto false => rfl
  | .goto true => rfl

theorem startOfFin_eq {i : Fin 3} {s : Bool} (h : startOfFin i = some s) : i = startFin s := by
  match i with
  | 0 => cases h; rfl
  | 1 => cases h; rfl
  | 2 => cases h

theorem startOfFin_startFin : (s : Bool) → startOfFin (startFin s) = some s
  | false => rfl
  | true => rfl

theorem readLeaf_sound {x : LambdaSSA.Flat signature.Instr 3 3} {b : PollLeaf} (h : readLeaf x = some b) :
    x = .br b.fin (.bv 0) := by
  cases x with
  | br i a =>
    by_cases ha : isBv0 a = true
    · simp [readLeaf, ha] at h
      rw [isBv0_eq ha, ← h, leafOfFin_fin]
    · simp [readLeaf, ha] at h
  | let₁ _ _ => cases h
  | let₂ _ _ => cases h
  | case _ _ _ => cases h

theorem readLeaf_leaf (b : PollLeaf) : readLeaf (.br b.fin (.bv 0)) = some b :=
  congrArg some (fin_leafOfFin b)

theorem readOp_sound {e : STm 2} {l : Bool} (h : readOp e = some l) : e = .op (.ask l) (.bv 0) := by
  cases e with
  | op f a =>
    by_cases ha : isBv0 a = true
    · simp [readOp, ha] at h
      rw [isBv0_eq ha, ← h, ← opLabel_eq f]
    · simp [readOp, ha] at h
  | _ => cases h

theorem readBlock_sound {x : LambdaSSA.Flat signature.Instr 3 2} {r : Bool × PollLeaf × PollLeaf}
    (h : readBlock x = some r) : x = pollFlatBlock r.1 r.2.1 r.2.2 := by
  cases x with
  | case e l r' =>
    cases he : readOp e with
    | none => simp [readBlock, he] at h
    | some lab =>
      cases hl : readLeaf l with
      | none => simp [readBlock, he, hl] at h
      | some b₁ =>
        cases hr : readLeaf r' with
        | none => simp [readBlock, he, hl, hr] at h
        | some b₂ =>
          simp [readBlock, he, hl, hr] at h
          rw [← h, readOp_sound he, readLeaf_sound hl, readLeaf_sound hr]
          rfl
  | br _ _ => cases h
  | let₁ _ _ => cases h
  | let₂ _ _ => cases h

theorem readBlock_block (l : Bool) (b₁ b₂ : PollLeaf) :
    readBlock (pollFlatBlock l b₁ b₂) = some (l, b₁, b₂) := by
  simp [readBlock, pollFlatBlock, readOp, isBv0, opLabel, readLeaf_leaf]

theorem readEntry_sound {x : LambdaSSA.Flat signature.Instr 3 1} {s : Bool} (h : readEntry x = some s) :
    x = .br (startFin s) (.bv 0) := by
  cases x with
  | br i a =>
    by_cases ha : isBv0 a = true
    · simp [readEntry, ha] at h
      rw [isBv0_eq ha, startOfFin_eq h]
    · simp [readEntry, ha] at h
  | let₁ _ _ => cases h
  | let₂ _ _ => cases h
  | case _ _ _ => cases h

theorem readEntry_entry (s : Bool) : readEntry (.br (startFin s) (.bv 0)) = some s := by
  simp [readEntry, isBv0, startOfFin_startFin]

/-! ## The reader is exact -/

/-- The graph of the rows that were read. -/
theorem ofRows_flat_block (s : Bool) (r₀ r₁ : Bool × PollLeaf × PollLeaf) (i : Fin 2) :
    (PollTable.ofRows s r₀ r₁).flat.block i =
      (match i with
        | 0 => pollFlatBlock r₀.1 r₀.2.1 r₀.2.2
        | 1 => pollFlatBlock r₁.1 r₁.2.1 r₁.2.2 : LambdaSSA.Flat signature.Instr 3 2) := by
  match i with
  | 0 => rfl
  | 1 => rfl

/-- A graph that the reader accepts is the graph of the table it returns. -/
theorem read_sound {g : LambdaSSA.FiniteCFG signature.Instr 2 1 1} {d : PollTable}
    (h : PollTable.read g = some d) : g = d.flat := by
  obtain ⟨entry, block⟩ := g
  cases hs : readEntry entry with
  | none => simp [PollTable.read, hs] at h
  | some s =>
    cases h₀ : readBlock (block 0) with
    | none => simp [PollTable.read, hs, h₀] at h
    | some r₀ =>
      cases h₁ : readBlock (block 1) with
      | none => simp [PollTable.read, hs, h₀, h₁] at h
      | some r₁ =>
        simp [PollTable.read, hs, h₀, h₁] at h
        rw [← h]
        have eb : block = (PollTable.ofRows s r₀ r₁).flat.block := funext fun i => by
          rw [ofRows_flat_block]
          match i with
          | 0 => exact readBlock_sound h₀
          | 1 => exact readBlock_sound h₁
        rw [eb, readEntry_sound hs]
        rfl

/-- The rows of a table give the table back. -/
theorem ofRows_rows (d : PollTable) :
    PollTable.ofRows d.start (d.label false, d.branch false false, d.branch false true)
      (d.label true, d.branch true false, d.branch true true) = d := by
  obtain ⟨label, branch, start⟩ := d
  have el : (fun c => match c with | false => label false | true => label true) = label := by
    funext c
    cases c <;> rfl
  have eb : (fun c tag => match c, tag with
      | false, false => branch false false
      | false, true => branch false true
      | true, false => branch true false
      | true, true => branch true true) = branch := by
    funext c tag
    cases c <;> cases tag <;> rfl
  exact congrArg₂ (fun l b => (⟨l, b, start⟩ : PollTable)) el eb

/-- The reader accepts the graph of every table and returns that table. -/
theorem read_flat (d : PollTable) : PollTable.read d.flat = some d := by
  have e : PollTable.read d.flat =
      some (PollTable.ofRows d.start (d.label false, d.branch false false, d.branch false true)
        (d.label true, d.branch true false, d.branch true true)) := by
    simp [PollTable.read, PollTable.flat, readEntry_entry, readBlock_block, pairBit]
  rw [e, ofRows_rows]

/-- The reader accepts exactly the graphs of tables. -/
theorem read_iff {g : LambdaSSA.FiniteCFG signature.Instr 2 1 1} {d : PollTable} :
    PollTable.read g = some d ↔ g = d.flat :=
  ⟨read_sound, fun h => h ▸ read_flat d⟩

/-! ## Certificates and completeness for accepted graphs -/

section Accepted

variable {g g' : LambdaSSA.FiniteCFG signature.Instr 2 1 1} {d d' : PollTable}

theorem read_typed (h : PollTable.read g = some d) : ValueBranches [Bit] g.erase [Bit] :=
  read_sound h ▸ d.source_typed

theorem read_bitPointed (h : PollTable.read g = some d) :
    BitPointed g.erase (fun i => some (d.label (pairBit i))) d.act (fun _ => pairIdx d.start) := by
  rw [read_sound h]
  exact poll_bitPointed d

theorem read_source_entered (h : PollTable.read g = some d) :
    Paper.WithAdministrativeReturns.WithGuardedTablePacking.Eqv false [Bit] g.erase
      (seqRegion (.br 0 (.inl (.var 0))) (d.router.entered (pairIdx d.start))) [Bit] := by
  rw [read_sound h]
  exact poll_source_entered d

open Paper.WithAdministrativeReturns.WithGuardedTablePacking (Valid) in
theorem read_complete (h : PollTable.read g = some d) (h' : PollTable.read g' = some d') :
    Eqv false [Bit] g.erase g'.erase [Bit] ↔ Valid (read_typed h).hasType (read_typed h').hasType := by
  obtain rfl := read_sound h
  obtain rfl := read_sound h'
  exact poll_complete d d'

theorem read_eqv_iff_bisim (h : PollTable.read g = some d) (h' : PollTable.read g' = some d') :
    Eqv false [Bit] g.erase g'.erase [Bit] ↔
      ∃ R : Fin 2 → Fin 2 → Prop, (∀ x y, R x y → d.label (pairBit x) = d'.label (pairBit y)) ∧
        (∀ x y, R x y → ∀ tag pl, Act.Rel R (d.act x tag pl) (d'.act y tag pl)) ∧
        R (pairIdx d.start) (pairIdx d'.start) := by
  obtain rfl := read_sound h
  obtain rfl := read_sound h'
  exact poll_eqv_iff_bisim d d'

end Accepted

/-! ## Accepted graphs written in flat syntax -/

theorem selfLit_flat (l : Bool) : selfLit l = (selfTable l).flat :=
  congrArg (LambdaSSA.FiniteCFG.mk _) (funext fun i => by
    match i with
    | 0 => rfl
    | 1 => rfl)

theorem swapLit_flat (l : Bool) : swapLit l = (swapTable l).flat :=
  congrArg (LambdaSSA.FiniteCFG.mk _) (funext fun i => by
    match i with
    | 0 => rfl
    | 1 => rfl)

theorem read_selfLit (l : Bool) : PollTable.read (selfLit l) = some (selfTable l) :=
  read_iff.2 (selfLit_flat l)

theorem read_swapLit (l : Bool) : PollTable.read (swapLit l) = some (swapTable l) :=
  read_iff.2 (swapLit_flat l)

/-- Two accepted graphs with different row actions have equal sources. -/
theorem selfLit_swapLit (l : Bool) : Eqv false [Bit] (selfLit l).erase (swapLit l).erase [Bit] :=
  (read_eqv_iff_bisim (read_selfLit l) (read_swapLit l)).2
    ⟨fun _ _ => True, fun _ _ _ => rfl, fun _ _ _ tag _ => by
      cases tag
      · exact rfl
      · exact ⟨rfl, trivial⟩, trivial⟩

/-- Two accepted graphs with different labels have different sources. -/
theorem selfLit_label (l l' : Bool) :
    Eqv false [Bit] (selfLit l).erase (selfLit l').erase [Bit] ↔ l = l' :=
  ⟨fun e => by
      obtain ⟨R, hl, -, r⟩ := (read_eqv_iff_bisim (read_selfLit l) (read_selfLit l')).1 e
      exact hl _ _ r,
    fun h => h ▸ Paper.Extension.Eqv.refl (read_typed (read_selfLit l)).hasType⟩

/-! ## Rejection is not inequivalence -/

/-- The reader rejects a block behind a let that renames its parameter,
and the source is the source of an accepted graph, in default Paper. -/
theorem alias_eqv (l : Bool) : Paper.Eqv [Bit] (aliasMiss l).erase (selfLit l).erase [Bit] := by
  have inner : Region.HasType [Bit, Bit, Bit]
      (.case (.op (.ask l) (.var 0)) (.br 2 (.var 0)) (.br 0 (.var 0)) : Region signature.Instr)
      (List.ofFn (fun _ : Fin 2 => Bit) ++ [Bit]) :=
    (ValueBranches.case (A := Bit) (B := Bit) (.op (.var (i := 0) rfl)) (.br (ℓ := 2) (A := Bit) rfl (.var rfl))
      (.br (ℓ := 0) (A := Bit) rfl (.var rfl))).hasType
  have ok : Region.HasType [Bit, Bit]
      (.case (.op (.ask l) (.var 0)) (.br 2 (.var 0)) (.br 1 (.var 0)) : Region signature.Instr)
      (List.ofFn (fun _ : Fin 2 => Bit) ++ [Bit]) :=
    (ValueBranches.case (A := Bit) (B := Bit) (.op (.var (i := 0) rfl)) (.br (ℓ := 2) (A := Bit) rfl (.var rfl))
      (.br (ℓ := 1) (A := Bit) rfl (.var rfl))).hasType
  refine Paper.Eqv.cfg (fun _ : Fin 2 => Bit)
    (Paper.Eqv.refl (ValueBranches.br (ℓ := 0) (A := Bit) (L := [Bit, Bit, Bit]) rfl (.var (i := 0) rfl)).hasType)
    (fun i => ?_)
  match i with
  | 0 => exact .cfgEta (.native (.letValue (A := Bit) (.var (i := 0) rfl) inner))
  | 1 => exact Paper.Eqv.refl ok

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
