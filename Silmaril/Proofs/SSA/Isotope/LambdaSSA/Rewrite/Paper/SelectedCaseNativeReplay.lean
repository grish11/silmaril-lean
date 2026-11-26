module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Packed.ReplyAgreement.NativeReplay.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.ExitPacking.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Extensional.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Extensional.Selected.Defs

/-! # Replay through the actual selected case and packing contexts -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedCaseNativeReplay

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement (ReadTree)
open CaseTree.ReplyAgreement.NativeReplay
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite (Derivable)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open Finite.Extensional (Source)

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

theorem applyPacked_eqv {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}
    {X A : τ} {L : LCtx τ} {r s : Region Φ}
    (h : Paper.Extension.Eqv Seed [product X A] r s L) :
    Paper.Extension.Eqv Seed [A, X] (Paper.PackedBody.applyPacked r) (Paper.PackedBody.applyPacked s) L :=
  h.substVars (fun {i _} hi => match i with
    | 0 => Option.some.inj hi ▸ .pair (.var (i := 1) rfl) (.var (i := 0) rfl)
    | _ + 1 => by simp [At] at hi)

theorem case_congr {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}
    {X A B : τ} {L : LCtx τ} (a : Term Φ X (coprod A B))
    {l l' : CaseTree Φ (product X A) L} {r r' : CaseTree Φ (product X B) L}
    (hl : Paper.Extension.Eqv Seed [product X A] l.elaborate.val l'.elaborate.val L)
    (hr : Paper.Extension.Eqv Seed [product X B] r.elaborate.val r'.elaborate.val L) :
    Paper.Extension.Eqv Seed [X] (CaseTree.case A B a l r).elaborate.val
      (CaseTree.case A B a l' r').elaborate.val L :=
  .case a.elaborate.property (applyPacked_eqv hl) (applyPacked_eqv hr)

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy

local notation "E" => Paper.Extension.Eqv Seed
local notation "read" => Finite.Expr.read (1 : Fin 2)
local notation "quote" => Finite.Expr.quote 2 (fun env => env 1)

set_option backward.isDefEq.respectTransparency false in
theorem packed_of_terminal {S : VCtx (Ty Empty) → Region signature.Instr → Region signature.Instr →
      LCtx (Ty Empty) → Prop}
    (h₀ : Paper.Extension.Eqv S [TerminalInput]
      (terminal first read).elaborate.val (terminal first quote).elaborate.val Exits)
    (h₁ : Paper.Extension.Eqv S [TerminalInput]
      (terminal second read).elaborate.val (terminal second quote).elaborate.val Exits) :
    Paper.Extension.Singleton.ofRegion S direct.selected.elaborate.property.packExits =
      Paper.Extension.Singleton.ofRegion S table.selected.elaborate.property.packExits := by
  let hd := direct.selected.elaborate.property
  let ht := table.selected.elaborate.property
  have replay : Paper.Extension.Eqv S [Ty.unit] direct.selected.elaborate.val table.selected.elaborate.val Exits := by
    apply case_congr
    · apply case_congr
      · exact .refl (CaseTree.elaborate _).property.hasType
      · apply case_congr
        · exact case_congr _ h₀ (.refl (CaseTree.elaborate _).property.hasType)
        · exact case_congr _ h₁ (.refl (CaseTree.elaborate _).property.hasType)
    · exact .refl (CaseTree.elaborate _).property.hasType
  exact (Paper.Extension.Singleton.ofRegion_eq_iff S hd.packExits ht.packExits).2
    (.lsubstPost replay hd ht (fun _ _ hi => (packExits_valueFamily _ Exits hi).hasType))

/-- Ordinary lowered returns already identify the extra value let. -/
theorem returned_seq_input :
    E [Bit] (CfgEta.TypeCategory.returnRegion (Term.seq .input .input : Term signature.Instr Bit Bit).elaborate.val)
      (CfgEta.TypeCategory.returnRegion (Term.input : Term signature.Instr Bit Bit).elaborate.val) [Bit] := by
  change E [Bit] (.let₁ (.var 0) (.let₁ (.var 0) (.br 0 (.var 0))))
    (.let₁ (.var 0) (.br 0 (.var 0))) [Bit]
  exact .let₁ (.var (i := 0) rfl)
    (.paper (.cfgEta (.native (.letValue (.var (i := 0) rfl) (.br rfl (.var (i := 0) rfl))))))

/-- Native LetCase replay via the witnessed normal forms. -/
theorem witnessed_derivable :
    Derivable false (Finite.Extensional.Selected.equation Bit [Bit] direct table) := by
  apply Finite.Extensional.derive_normal Bit [Bit]
  intro env
  have tableEntry : (Finite.Expr.quote 2 (fun env => env 1)).eval = (Finite.Expr.read (1 : Fin 2)).eval :=
    funext (Finite.Expr.quote_eval 2 (fun env => env 1))
  simp only [direct, table, fixture, Finite.Extensional.Selected.witnessed, Source.normal,
    ReadTree.witnessed, List.foldr_cons, List.foldr_nil, Finite.Tree.normal, tableEntry]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedCaseNativeReplay
