module

public import Silmaril.Formats.Git.Translate.Defs
import Silmaril.Proofs.Formats.Git.Translate

public section

namespace Silmaril.Formats.Git.Translate

open Silmaril.Semantics

variable {Key Source Target Meta : Type} {algorithm : Native.Algorithm}

theorem translate_root_pair [DecidableEq Key] (profile : Profile algorithm Key Source Target Meta)
    {kind : Kind} (object : Object Key Source Native.CommitMetadata kind) {result : Result Source Target}
    (hit : translate profile object = some result) : result.RootPair kind :=
  Proofs.Formats.Git.translate_root_pair profile object hit

theorem translate_tree_child [DecidableEq Key] (profile : Profile algorithm Key Source Target Meta)
    {keys : Finset Key} {modes : ↥keys → EntryMode}
    {children : (key : ↥keys) → Object Key Source Native.CommitMetadata (modes key).kind}
    {result : Result Source Target} (hit : translate profile (.tree keys modes children) = some result)
    (key : ↥keys) : ∃ child, translate profile (children key) = some child ∧
      child.trace.events ⊆ result.trace.events :=
  Proofs.Formats.Git.translate_tree_child profile hit key

theorem translate_commit_children [DecidableEq Key] (profile : Profile algorithm Key Source Target Meta)
    {tree : Object Key Source Native.CommitMetadata .tree} {count : Nat}
    {parents : Fin count → Object Key Source Native.CommitMetadata .commit} {metadata : Native.CommitMetadata}
    {result : Result Source Target} (hit : translate profile (.commit tree count parents metadata) = some result) :
    (∃ child, translate profile tree = some child ∧ child.trace.events ⊆ result.trace.events) ∧
    (∀ index, ∃ child, translate profile (parents index) = some child ∧ child.trace.events ⊆ result.trace.events) :=
  Proofs.Formats.Git.translate_commit_children profile hit

/-- For any successful fold, the native projection agrees with the independent
native renderer, regardless of which admissible target layout or naming is used. -/
theorem translate_native [DecidableEq Key] (profile : Profile algorithm Key Source Target Meta)
    {kind : Kind} (object : Object Key Source Native.CommitMetadata kind) {result : Result Source Target}
    (hit : translate profile object = some result) :
    ∃ view, Native.renderObject profile.native object = some view ∧
      result.SourceWitness profile.native.assign kind view :=
  Proofs.Formats.Git.translate_native profile object hit

theorem Audit.sameTarget {result : Result Source Target} {observed : Kind → Naming.Relation Source ByteArray}
    {nativeNames : Naming.Relation Source ByteArray} {wire : Wire Target}
    {allowedFrontier : Correspondence Source Target} (audit : Audit result observed nativeNames wire allowedFrontier)
    {kind : Kind} {source : Source} {left right : Target}
    (first : result.trace.pairs kind source left) (second : result.trace.pairs kind source right) : left = right :=
  audit.sharing kind first second

theorem translate_commit_evidence [DecidableEq Key] (profile : Profile algorithm Key Source Target Meta)
    {tree : Object Key Source Native.CommitMetadata .tree} {count : Nat}
    {parents : Fin count → Object Key Source Native.CommitMetadata .commit} {metadata : Native.CommitMetadata}
    {result : Result Source Target} {observed : Kind → Naming.Relation Source ByteArray}
    {nativeNames : Naming.Relation Source ByteArray} {wire : Wire Target}
    {allowedFrontier : Correspondence Source Target}
    (hit : translate profile (.commit tree count parents metadata) = some result)
    (audit : Audit result observed nativeNames wire allowedFrontier) :
    ∃ root ancestors, translate profile tree = some root ∧
      List.Forall₂ (fun parent translated => translate profile parent = some translated) (List.ofFn parents) ancestors ∧
      CommitEvidence profile root ancestors metadata result observed nativeNames wire :=
  Proofs.Formats.Git.translate_commit_evidence profile hit audit

end Silmaril.Formats.Git.Translate
