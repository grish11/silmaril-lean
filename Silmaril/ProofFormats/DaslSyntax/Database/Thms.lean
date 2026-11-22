module

public import Silmaril.ProofFormats.DaslSyntax.Database.Defs
public import Silmaril.ProofFormats.DaslSyntax.Thms
public import Silmaril.ProofFormats.DaslSyntax.HOL.Thms
public import Silmaril.Semantics.Naming.Lift.Thms
public import Silmaril.Semantics.Naming.Thms
import Silmaril.Proofs.ProofFormats.DaslSyntax.Database

public section

namespace Silmaril.ProofFormats.DaslSyntax.Database

open Silmaril.Formats.Dasl (Value Recognized Store)
open Silmaril.Semantics.Naming (Binding Relation)
open Silmaril.Semantics.Naming.Lift (Coordinate mem_where_iff)

theorem valueSystem_iff {Context Statement : Type} {contexts : Relation Value Context}
    {statements : Relation Value Statement} {source : Consequence.System Context Statement} {ctx result : Value} :
    valueSystem contexts statements source ctx result ↔
      ∃ context statement, contexts ctx context ∧ statements result statement ∧ source context statement :=
  system_iff

theorem namedSystem_iff {ContextName StatementName Context Statement : Type}
    {contexts : Relation ContextName Context} {statements : Relation StatementName Statement}
    {source : Consequence.System Context Statement} {ctx : ContextName} {result : StatementName} :
    namedSystem contexts statements source ctx result ↔
      ∃ context statement, contexts ctx context ∧ statements result statement ∧ source context statement :=
  system_iff

theorem valueSystem_names {ContextName StatementName Context Statement : Type}
    (contextNames : Relation ContextName Value) (statementNames : Relation StatementName Value)
    (contexts : Relation Value Context) (statements : Relation Value Statement)
    (source : Consequence.System Context Statement) (ctx : ContextName) (result : StatementName) :
    namedSystem contextNames statementNames (valueSystem contexts statements source) ctx result ↔
      namedSystem (Semantics.Naming.push contextNames contexts) (Semantics.Naming.push statementNames statements)
        source ctx result :=
  Proofs.ProofFormats.DaslSyntax.Database.valueSystem_names contextNames statementNames contexts statements source ctx result

/-- The unary lift agrees with the existing full-value DASL language interface. -/
theorem namesWhere_eq_recognized {Name Item : Type} (store : Store Name)
    (decode : Relation Value Item) (predicate : Item → Prop) :
    Formats.Dasl.Lift.namesWhere store decode predicate =
      Recognized store (fun value => ∃ item, decode value item ∧ predicate item) := by
  ext root
  exact mem_where_iff.trans ⟨fun ⟨item, ⟨value, expands, decodes⟩, holds⟩ => ⟨value, expands, item, decodes, holds⟩,
    fun ⟨value, expands, item, decodes, holds⟩ => ⟨item, ⟨value, expands, decodes⟩, holds⟩⟩

theorem typingTable_iff {context term type : Coordinate}
    {checks : context.Meaning → term.Meaning → type.Meaning → Prop}
    {contextInput : context.Surface} {termInput : term.Surface} {typeInput : type.Surface} :
    typingTable context term type checks contextInput termInput typeInput ↔
      ∃ ctx tm ty, context.represents contextInput ctx ∧ term.represents termInput tm ∧
        type.represents typeInput ty ∧ checks ctx tm ty :=
  ⟨fun ⟨⟨ctx, tm, ty, _⟩, ⟨ctxHit, tmHit, tyHit, _⟩, holds⟩ => ⟨ctx, tm, ty, ctxHit, tmHit, tyHit, holds⟩,
    fun ⟨ctx, tm, ty, ctxHit, tmHit, tyHit, holds⟩ => ⟨(ctx, tm, ty, ()), ⟨ctxHit, tmHit, tyHit, trivial⟩, holds⟩⟩

/-- Unresolved inputs supply no row, not a refutation of the source judgment. -/
theorem namedSystem_no_context {ContextName StatementName Context Statement : Type}
    {contexts : Relation ContextName Context} {statements : Relation StatementName Statement}
    {source : Consequence.System Context Statement} {ctx : ContextName} {result : StatementName}
    (unavailable : ¬ ∃ context, contexts ctx context) : ¬ namedSystem contexts statements source ctx result :=
  fun row => let ⟨context, _, hit, _, _⟩ := namedSystem_iff.mp row; unavailable ⟨context, hit⟩

namespace HOL

open Silmaril.Logic.HOLLight

universe u

theorem listAgreement {Name : Type} {terms : Relation Name Tm} (bound : Binding terms)
    {left right : List Name} {leftHyps rightHyps : Hyps}
    (leftHit : listAssumptions terms left leftHyps) (rightHit : listAssumptions terms right rightHyps)
    (same : ∀ name, name ∈ left ↔ name ∈ right) : leftHyps = rightHyps :=
  Proofs.ProofFormats.DaslSyntax.Database.listAgreement bound leftHit rightHit same

theorem listFiniteAgreement {Name : Type} {terms : Relation Name Tm} (bound : Binding terms)
    {listed : List Name} {names : Finset Name} {hyps : Hyps}
    (covers : ∀ name, name ∈ listed ↔ name ∈ names) (known : listAssumptions terms listed hyps) :
    ∀ decoded, finiteAssumptions terms names decoded ↔ decoded = hyps :=
  Proofs.ProofFormats.DaslSyntax.Database.listFiniteAgreement bound covers known

theorem derives_le_entails {ContextName TermName : Type} {hypotheses : Relation ContextName Hyps}
    {terms : Relation TermName Tm} {sig : Signature} {theory : Theory} {model : Model.{u} sig}
    (satisfies : Models model theory) : derives hypotheses terms sig theory ≤ entails hypotheses terms model :=
  system_mono (context := .encoded hypotheses) (conclusion := .encoded terms)
    (left := Derives sig theory) (right := DaslSyntax.HOL.semantic model)
    (fun _ _ proof => ⟨proof.typedHyps, proof.typing, proof.sound model satisfies⟩)

theorem derivesList_iff_finite {Name : Type} {terms : Relation Name Tm} {sig : Signature} {theory : Theory}
    {listed : List Name} {names : Finset Name} {hyps : Hyps} {result : Name}
    (bound : Binding terms) (covers : ∀ name, name ∈ listed ↔ name ∈ names)
    (known : listAssumptions terms listed hyps) :
    derivesList terms sig theory listed result ↔ derivesFinite terms sig theory names result :=
  Proofs.ProofFormats.DaslSyntax.Database.derivesList_iff_finite bound covers known

theorem closedTheorems_subset_propositions {Name : Type} {terms : Relation Name Tm}
    {sig : Signature} {theory : Theory} : closedTheorems terms sig theory ⊆ propositions terms sig :=
  fun _ row => let ⟨term, hit, _, _, proof⟩ := mem_where_iff.mp row
               mem_where_iff.mpr ⟨term, hit, proof.typing⟩

end HOL

end Silmaril.ProofFormats.DaslSyntax.Database
