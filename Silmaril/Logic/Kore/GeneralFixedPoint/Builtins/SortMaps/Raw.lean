module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Institution
public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Institution.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps
open CategoryTheory

/-- Bounded syntactic action only. Variable names and namespaces are retained;
all raw sort annotations are reindexed. An alias occurrence and its declaration
must use the same supplied name action. No successful checking is asserted. -/
def renameRaw (sortMap nameMap : String → String) : Nat → RawPattern → Option RawPattern
  | 0, _ => none
  | _ + 1, .evar name sort => some (.evar name (sortMap sort))
  | _ + 1, .svar name sort => some (.svar name (sortMap sort))
  | _ + 1, .domainValue sort text => some (.domainValue (sortMap sort) text)
  | n + 1, .app name args => do
      return .app (nameMap name) (← args.mapM (renameRaw sortMap nameMap n))
  | _ + 1, .top sort => some (.top (sortMap sort))
  | _ + 1, .bottom sort => some (.bottom (sortMap sort))
  | n + 1, .neg sort p => return .neg (sortMap sort) (← renameRaw sortMap nameMap n p)
  | n + 1, .conj sort p q =>
      return .conj (sortMap sort) (← renameRaw sortMap nameMap n p) (← renameRaw sortMap nameMap n q)
  | n + 1, .disj sort p q =>
      return .disj (sortMap sort) (← renameRaw sortMap nameMap n p) (← renameRaw sortMap nameMap n q)
  | n + 1, .ex sort name bound p =>
      return .ex (sortMap sort) name (sortMap bound) (← renameRaw sortMap nameMap n p)
  | n + 1, .all sort name bound p =>
      return .all (sortMap sort) name (sortMap bound) (← renameRaw sortMap nameMap n p)
  | n + 1, .mu name sort p => return .mu name (sortMap sort) (← renameRaw sortMap nameMap n p)
  | n + 1, .nu name sort p => return .nu name (sortMap sort) (← renameRaw sortMap nameMap n p)

/-- A necessary genuine surface condition missing from semantic Hom. This
condition checks declared sort visibility; it does not assume checker success. -/
structure VisibleMap (A B : Signature) extends Hom A B where
  named : ∀ s, Kore.Modules.Checking.namedSort A.scope s = true →
    Kore.Modules.Checking.namedSort B.scope (native.sorts s) = true

/-- Actual checked receipt for a supported top pattern. The checker equation
is proved by unfolding the real checker, not supplied by the caller. -/
def topReceipt (A : Signature) (s : String)
    (named : Kore.Modules.Checking.namedSort A.scope s = true) :
    @CheckedSentence A.bindings A.scope A.literals A.literalPrefix :=
  @CheckedSentence.mk A.bindings A.scope A.literals A.literalPrefix
    [] 0 1 [] [] s (.top s) (.base Matching.FirstOrder.Pattern.top)
    (by simp [Checking.elaborate, named]) rfl

/-- A small actual source action: target admission is constructed from the
visibility map, rather than demanded as a successful-checker premise. -/
def mapTop {A B : Signature} (f : VisibleMap A B) (s : String)
    (named : Kore.Modules.Checking.namedSort A.scope s = true) :
    @CheckedSentence B.bindings B.scope B.literals B.literalPrefix :=
  topReceipt B (f.native.sorts s) (f.named s named)

theorem mapTop_raw {A B : Signature} (f : VisibleMap A B) (s : String)
    (named : Kore.Modules.Checking.namedSort A.scope s = true) :
    renameRaw f.native.sorts id 1 (@CheckedSentence.raw A.bindings A.scope A.literals A.literalPrefix (topReceipt A s named)) =
      some (@CheckedSentence.raw B.bindings B.scope B.literals B.literalPrefix (mapTop f s named)) := rfl

/-- A genuine small source/reduct satisfaction square on actually constructed
receipts. This is restricted to top syntax; it is not general checker naturality. -/
theorem mapTop_satisfies {A B : Signature} (f : VisibleMap A B) (s : String)
    (named : Kore.Modules.Checking.namedSort A.scope s = true)
    (M : @Model B.bindings B.scope B.literalPrefix B.literals B.hooks) :
    @CheckedSentence.Satisfies B.bindings B.scope B.literals B.literalPrefix B.hooks
      M (mapTop f s named) ↔
    @CheckedSentence.Satisfies A.bindings A.scope A.literals A.literalPrefix A.hooks
      (Hom.reduct f.toHom M) (topReceipt A s named) := by
  constructor
  · intro _
    exact @CheckedSentence.top_satisfies A.bindings A.scope A.literals A.literalPrefix A.hooks
      (Hom.reduct f.toHom M) (topReceipt A s named) rfl
  · intro _
    exact @CheckedSentence.top_satisfies B.bindings B.scope B.literals B.literalPrefix B.hooks
      M (mapTop f s named) rfl

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps
