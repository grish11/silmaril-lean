module

public import Silmaril.SSA.PEG.Simple.Revert.While.Nested.Reindexed.Defs

/-! # Graph-only checked reversion of a renumbered two-level PEG

The probe recovers a candidate structured program from the designated
eval and the scoped loop slices. Its compiled graph supplies the
reference numbering. Every eval in the outer and child bundles is an
anchor, including carried slots that the designated return does not read.
The complete mapped table is checked before the result is returned. -/

@[expose] public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Nested.Reindexed.Automatic

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {outer : List (Ty Data)} {result : Ty Data} {n l : Nat}

structure Accepted (g : Graph P outer [result] n l) where
  inner : List (Ty Data)
  form : Form P outer inner result
  numbering : Silmaril.SSA.PEG.Reindex.Automatic.Certificate form.compile g

def extract [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P outer [result] n l) : Option (Accepted g) := do
  let d ← Nested.Automatic.describe g (numbered := false)
  let reference := d.form.compile
  let cached := Nested.Automatic.cacheRows reference
  let some header := Nested.Automatic.locate cached | none
  let outerExits := Nested.Automatic.bundleIds cached header.outerKey
  let childExits := Nested.Automatic.bundleIds cached header.childKey
  if outerExits.length = d.outerExits.length ∧ childExits.length = d.childExits.length then
    let anchors := outerExits.zip d.outerExits ++ childExits.zip d.childExits
    let some numbering := Silmaril.SSA.PEG.Reindex.Automatic.infer reference g anchors | none
    return ⟨d.inner, d.form, numbering⟩
  else none

variable {g : Graph P outer [result] n l}

def Accepted.revert (a : Accepted g) : Program P true outer result :=
  a.form.source

end Silmaril.SSA.PEG.Simple.Revert.While.Nested.Reindexed.Automatic
