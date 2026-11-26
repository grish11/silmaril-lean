module

public import Silmaril.SSA.MLIR.SCF.LetIter.FixedProfile.Defs

/-! # Native admission for the fixed-profile one-iteration fragment

The phase-indexed grammar checks which bound value each call can read.
Every phase also admits an administrative identity binding. In particular,
the yield receives the condition payload and cannot read the before state
underneath it.
-/

@[expose] public section

namespace Silmaril.MLIR.SCF.LetIter.FixedProfile

open CategoryTheory
open Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless

/-- The entry, intermediate results, and exit of the one-iteration grammar. -/
inductive Phase
  | initializer | condition | yield | parent | body | loop | program

abbrev Phase.scope : Phase → Nat
  | .initializer | .loop | .program => 0
  | .condition | .parent | .body => 1
  | .yield => 2

open ScalarWhile (Interface)

def Phase.context : (k : Phase) → BoundCtx (Ty Interface) k.scope
  | .initializer | .loop | .program => .nil
  | .condition | .body => .snoc .nil (.base .state)
  | .parent => .snoc .nil (.base .payload)
  | .yield => .snoc (.snoc .nil (.base .state)) (.base .payload)

def Phase.result : Phase → Ty Interface
  | .initializer | .yield => .base .state
  | .condition => .coprod (.base .payload) (.base .payload)
  | .body => .coprod (.base .payload) (.base .state)
  | .loop => .base .payload
  | .parent | .program => .base .result

abbrev Term (P : Profile) (S : Signature) (k : Phase) := Tm Empty (Call P S) k.scope

/-- Admission reads native constructors and typed calls, with wiring rules at every phase. -/
inductive Grammar (P : Profile) (S : Signature) : (k : Phase) → Term P S k → Type where
  | initializer (args : Init P) : Grammar P S .initializer (.op (.init args) .unit)
  | condition (code : Before P S) : Grammar P S .condition (.op (.before code) (.bv 0))
  | yield (code : After P S) : Grammar P S .yield (.op (.yield code) (.bv 0))
  | parent (code : Parent P S) : Grammar P S .parent (.op (.parent code) (.bv 0))
  | branch {test : Term P S .condition} {next : Term P S .yield}
      (hTest : Grammar P S .condition test) (hNext : Grammar P S .yield next) :
      Grammar P S .body (.case test (.inl (.bv 0)) (.inr next))
  | iterate {init : Term P S .initializer} {body : Term P S .body}
      (hInit : Grammar P S .initializer init) (hBody : Grammar P S .body body) :
      Grammar P S .loop (.iter init body)
  | sequence {loop : Term P S .loop} {parent : Term P S .parent}
      (hLoop : Grammar P S .loop loop) (hParent : Grammar P S .parent parent) :
      Grammar P S .program (.let₁ loop parent)
  | wire {k : Phase} {t : Term P S k} (h : Grammar P S k t) :
      Grammar P S k (.let₁ t (.bv 0))

/-- The native syntax with proof-irrelevant admission evidence. -/
abbrev Native (P : Profile) (S : Signature) := {t : Term P S .program // Nonempty (Grammar P S .program t)}

variable {P : Profile} {S T U : Signature}

namespace Grammar

/-- Admission entails exact native typing at each phase. -/
theorem hasType {k : Phase} {t : Term P S k} (h : Grammar P S k t) :
    HasType (Call P S) .nil k.context t k.result := by
  induction h with
  | initializer => exact .op .unit
  | condition | yield | parent => exact .op .newest
  | branch _ _ test next => exact .case test (.inl .newest) (.inr next)
  | iterate _ _ init body => exact .iter init body
  | sequence _ _ loop parent => exact .let₁ loop parent
  | wire _ ih => exact .let₁ ih .newest

/-- Relabel a derivation along the actual native instruction map. -/
def rename (f : S ⟶ T) : {k : Phase} → {t : Term P S k} → Grammar P S k t →
    Grammar P T k (t.mapInstr (renameCall f))
  | _, _, .initializer args => .initializer args
  | _, _, .condition code => .condition (renameCode f code)
  | _, _, .yield code => .yield (renameCode f code)
  | _, _, .parent code => .parent (renameCode f code)
  | _, _, .branch hTest hNext => .branch (rename f hTest) (rename f hNext)
  | _, _, .iterate hInit hBody => .iterate (rename f hInit) (rename f hBody)
  | _, _, .sequence hLoop hParent => .sequence (rename f hLoop) (rename f hParent)
  | _, _, .wire h => .wire (rename f h)

end Grammar

/-- Reindex an admitted term by native instruction relabelling. -/
def Native.rename (f : S ⟶ T) (p : Native P S) : Native P T :=
  ⟨p.val.mapInstr (renameCall f), p.property.map (Grammar.rename f)⟩

theorem Native.rename_id (p : Native P S) : p.rename (𝟙 S) = p := by
  apply Subtype.ext
  simp [Native.rename, renameCall_id]

theorem Native.rename_comp (f : S ⟶ T) (g : T ⟶ U) (p : Native P S) :
    (p.rename f).rename g = p.rename (f ≫ g) := by
  apply Subtype.ext
  simp [Native.rename, renameCall_comp]

/-- The operands and typed region bodies recovered at each phase. -/
abbrev Decoded (P : Profile) (S : Signature) : Phase → Type
  | .initializer => Init P
  | .condition => Before P S
  | .yield => After P S
  | .parent => Parent P S
  | .body => Before P S × After P S
  | .loop => Init P × Before P S × After P S
  | .program => Scalar P S

/-- Read the typed program from its admitted wiring derivation. -/
def Grammar.decode : {k : Phase} → {t : Term P S k} → Grammar P S k t → Decoded P S k
  | _, _, .initializer args => args
  | _, _, .condition code => code
  | _, _, .yield code => code
  | _, _, .parent code => code
  | _, _, .branch test next => (test.decode, next.decode)
  | _, _, .iterate init body => (init.decode, body.decode)
  | _, _, .sequence run post => ⟨run.decode.1, run.decode.2.1, run.decode.2.2, post.decode⟩
  | _, _, .wire h => h.decode

/-- Decode any admitted program. The grammar decoder computes on a derivation. -/
noncomputable def Native.decode (p : Native P S) : Scalar P S :=
  (Classical.choice p.property).decode

/-- Encode a scalar while through the existing lowering, witnessing its grammar. -/
def encode (p : Scalar P S) : Native P S :=
  ⟨(ScalarWhile.toRegionLoop p.toWhile).lower,
    ⟨.sequence (.iterate (.initializer p.init) (.branch (.condition p.before) (.yield p.afterRegion)))
      (.parent p.parent)⟩⟩

theorem encode_rename (f : S ⟶ T) (p : Scalar P S) :
    (encode p).rename f = encode (p.rename f) := by
  apply Subtype.ext
  rfl

end Silmaril.MLIR.SCF.LetIter.FixedProfile
