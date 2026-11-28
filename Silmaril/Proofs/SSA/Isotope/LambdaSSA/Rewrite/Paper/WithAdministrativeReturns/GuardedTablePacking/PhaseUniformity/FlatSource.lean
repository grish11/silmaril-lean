module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.ProductState

/-! # A cyclic flat source and the loop on pairs -/

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
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
  (packedReadbackRep entry_route dispatcherRep orderedRow)

/-! ## The named table, the flat graph and their typing -/

/-- The named cyclic table elaborates to the flat graph, with the exit
list `[exit]` and the input register `p` as the captured variable. -/
theorem named_flat (l : Bool) :
    Bridge.NamedFlat.elaborate (pairNamed l) [.exit] (fun _ : Fin 1 => PairReg.p) = some (pairFlat l) := by
  have h : Bridge.NamedFlat.elaborate (pairNamed l) [.exit] (fun _ : Fin 1 => PairReg.p) =
      some ⟨(pairFlat l).entry, Fin.cases ((pairFlat l).block 0) Fin.elim0⟩ := rfl
  refine h.trans (congrArg some (congrArg (LambdaSSA.FiniteCFG.mk _) (funext fun i => ?_)))
  match i with
  | 0 => rfl

/-- The flat graph is typed in the flat judgment: the header receives a
pair, the exit a Bit, and the captured input is a pair. -/
theorem flat_typed (l : Bool) :
    LambdaSSA.FiniteCFG.HasType (.snoc .nil Pair) (fun _ : Fin 1 => Pair) (fun _ : Fin 1 => Bit)
      (pairFlat l) where
  entry := .br (i := 0) .bv
  block := fun _ => .let₂ (A := Bit) (B := Bit) .bv
    (.case (A := Bit) (B := Bit) (.op .bv) (.br (i := 1) .bv) (.br (i := 0) (.pair .bv .bv)))

/-! ## One-header flat loops, in default Paper -/

variable {S : Ty Empty} {K : Nat} {b enc dec : Region signature.Instr}

/-- A header block is its loop step followed by the decoding of the sum
exit into the back edge and the exit. Native case on a constructor. -/
theorem flat_core (hb : ValueBranches [S] b [S, Bit]) :
    Paper.Eqv [S] b ((flatStep b).lsubst (fun _ => SyntacticCategory.iterationDispatch)) [S, Bit] := by
  have e : (flatStep b).lsubst (fun _ => SyntacticCategory.iterationDispatch) =
      b.lsubst (compLSubst sumExits (fun _ => SyntacticCategory.iterationDispatch)) := lsubst_comp b _ _
  rw [e]
  have c := Paper.Eqv.lsubstCongr (σ := labelId)
    (υ := compLSubst sumExits (fun _ => SyntacticCategory.iterationDispatch)) (K := [S, Bit]) hb
    (fun i _ h => by
      match i, h with
      | 0, h =>
        cases h
        have hl : Region.HasType [Bit, S, S] (.br 1 (.var 0) : Region signature.Instr) [S, Bit] :=
          (ValueBranches.br (ℓ := 1) (A := Bit) rfl (.var rfl)).hasType
        have hr : Region.HasType [S, S, S] (.br 0 (.var 0) : Region signature.Instr) [S, Bit] :=
          (ValueBranches.br (ℓ := 0) (A := S) rfl (.var rfl)).hasType
        exact .symm ((Paper.Eqv.cfgEta (.native (.base (.caseInr (A := Bit) (B := S) (.var rfl) hl hr)))).trans
          (.cfgEta (.native (.base (.letBr (ℓ := 0) (A := S) (B := S) (.var rfl) (.var rfl) rfl)))))
      | 1, h =>
        cases h
        have hl : Region.HasType [Bit, Bit, S] (.br 1 (.var 0) : Region signature.Instr) [S, Bit] :=
          (ValueBranches.br (ℓ := 1) (A := Bit) rfl (.var rfl)).hasType
        have hr : Region.HasType [S, Bit, S] (.br 0 (.var 0) : Region signature.Instr) [S, Bit] :=
          (ValueBranches.br (ℓ := 0) (A := S) rfl (.var rfl)).hasType
        exact .symm ((Paper.Eqv.cfgEta (.native (.base (.caseInl (A := Bit) (B := S) (.var rfl) hl hr)))).trans
          (.cfgEta (.native (.base (.letBr (ℓ := 1) (A := Bit) (B := Bit) (.var rfl) (.var rfl) rfl))))))
  rwa [lsubst_labelId] at c

/-- A one-header flat table is the loop of its header's step, at the
source entry, in default Paper: congruence of the table on its block. -/
theorem flat_loop (hb : ValueBranches [S] b [S, Bit]) :
    Paper.Eqv [S] (flatLoop b) (loopRegion S (flatStep b)) [Bit] :=
  Paper.Eqv.cfg (fun _ : Fin 1 => S)
    (Paper.Eqv.refl (ValueBranches.br (ℓ := 0) (A := S) rfl (.var rfl)).hasType)
    (fun _ => Paper.Eqv.renameVars (flat_core hb) headerRen)

/-- A one-header flat table whose step, conjugated by an encoding with a
section, is the dispatcher step of a router table, factors through the
packed loop of that table. -/
theorem flat_factors (he : ValueBranches [S] enc [States K]) (hd : ValueBranches [States K] dec [S])
    (hb : ValueBranches [S] b [S, Bit]) (ret : Retracts S enc dec) (t : Router K)
    (hstep : Eqv false [States K] (seqRegion dec (seqRegion (flatStep b) (postRegion enc))) (dispatch K t.rows)
      [Silmaril.coprod Bit (States K)]) : Factors dec (flatLoop b) t := by
  have packed : Eqv false [States K] (seqRegion dec (flatLoop b))
      (seqRegion dec (loopRegion S (flatStep b))) [Bit] :=
    (Paper.Extension.Singleton.ofRegion_eq_iff N (seqRegion_typed hd (flatLoop_typed hb))
      (seqRegion_typed hd (loopRegion_typed (flatStep_typed hb)))).1
      ((q_comp hd (flatLoop_typed hb)).trans
        ((congrArg (QLit hd ≫ ·)
          ((Paper.Extension.Singleton.ofRegion_eq_iff N (flatLoop_typed hb)
            (loopRegion_typed (flatStep_typed hb))).2 (.paper (flat_loop hb)))).trans
          (q_comp hd (loopRegion_typed (flatStep_typed hb))).symm))
  exact packed.trans (conjugate_factors he hd (flatStep_typed hb) ret t hstep)

/-! ## The source with two live Bits -/

/-- The flat source is the loop on pairs at the source entry, in default Paper. -/
theorem source_loop (l : Bool) : Paper.Eqv [Pair] (pairSource l) (loopRegion Pair (pairBody l)) [Bit] :=
  flat_loop (flatBody_typed l)

/-! ## Transfer to the router table, in the opt-in quotient -/

theorem q_source_loop (l : Bool) : Eqv false [Pair] (pairSource l) (loopRegion Pair (pairBody l)) [Bit] :=
  .paper (source_loop l)

/-- The flat source factors through the packed loop of the router table. -/
theorem source_factors (l : Bool) : Factors pairDec (pairSource l) (pairRouter l) :=
  flat_factors pairEnc_typed pairDec_typed (flatBody_typed l) enc_dec (pairRouter l) (pair_step l)

open Paper.WithAdministrativeReturns.WithGuardedTablePacking (Valid) in
/-- Two flat sources are equal at the source entry exactly when they are
valid in every supported model. -/
theorem source_complete (l l' : Bool) :
    Eqv false [Pair] (pairSource l) (pairSource l') [Bit] ↔
      Valid (pairSource_typed l).hasType (pairSource_typed l').hasType :=
  factored_complete pairEnc_typed pairDec_typed (pairSource_typed l) (pairSource_typed l') enc_dec
    (pairRouter l) (pairRouter l') (source_factors l) (source_factors l')

/-- Two flat sources are equal exactly when their requests have the same label. -/
theorem source_eqv_iff (l l' : Bool) : Eqv false [Pair] (pairSource l) (pairSource l') [Bit] ↔ l = l' :=
  ⟨fun e => (pair_eqv_iff l l').1 ((q_source_loop l).symm.trans (e.trans (q_source_loop l'))),
    fun h => h ▸ Paper.Extension.Eqv.refl (pairSource_typed l).hasType⟩

/-- A flat source and a loop on pairs are equal exactly when their
requests have the same label. -/
theorem source_loop_iff (l l' : Bool) :
    Eqv false [Pair] (pairSource l) (loopRegion Pair (pairBody l')) [Bit] ↔ l = l' :=
  ⟨fun e => (pair_eqv_iff l l').1 ((q_source_loop l).symm.trans e), fun h => h ▸ q_source_loop l⟩

/-! ## The packed readback -/

/-- The table-packing seed at the flat source. -/
theorem source_readback (l : Bool) :
    Paper.WithAdministrativeReturns.WithGuardedTablePacking.Eqv false [Pair] (pairSource l)
      (pairReadback l).val [Bit] :=
  Paper.WithAdministrativeReturns.WithGuardedTablePacking.pack false (fun _ : Fin 1 => Pair) flatEntry_typed
    (flatBlock_typed l)

/-- The packed readback of the flat source is the loop on pairs, through
the source: the seed and the native equation. -/
theorem readback_loop (l : Bool) :
    Paper.WithAdministrativeReturns.WithGuardedTablePacking.Eqv false [Pair] (pairReadback l).val
      (loopRegion Pair (pairBody l)) [Bit] :=
  (source_readback l).symm.trans (.paper (source_loop l))

/-- Two packed readbacks are equal exactly when the requests have the same label. -/
theorem readback_eqv_iff (l l' : Bool) :
    Eqv false [Pair] (pairReadback l).val (pairReadback l').val [Bit] ↔ l = l' :=
  ⟨fun e => (source_eqv_iff l l').1
      ((Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.ofTablePacking false
        (source_readback l)).trans (e.trans
        (Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.ofTablePacking false
          (source_readback l')).symm)),
    fun h => h ▸ Paper.Extension.Eqv.refl (pairReadback l).property.hasType⟩

/-- The packed readback is a routed entry followed by a loop on
`ReadbackState`: the captured input paired with the tagged parameter of
the header. Its loop is not a loop on the two Bits. -/
theorem readback_state (l : Bool) :
    ∃ route step : Region signature.Instr,
      ValueBranches [Pair] route [Silmaril.coprod Bit ReadbackState] ∧
      ValueBranches [ReadbackState] step [Silmaril.coprod Bit ReadbackState] ∧
      (pairReadback l).val = seqRegion route
        (.case (.var 0) (.br 0 (.var 0)) ((loopRegion ReadbackState step).renameVars (lift Nat.succ))) :=
  ⟨_, _, entry_route (fun _ : Fin 1 => Pair) flatEntry_typed,
    (dispatcherRep Pair (List.ofFn fun _ : Fin 1 => Pair) (orderedRow (fun _ : Fin 1 => Pair)
      (flatBlock_typed l))).property, rfl⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
