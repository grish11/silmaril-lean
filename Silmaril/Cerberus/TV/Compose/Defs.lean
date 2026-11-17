module

public import Silmaril.Cerberus.TV.Validate.Defs
public import Silmaril.Cerberus.TV.Applicability.Defs

/-!
# Composing whole-program evidence: along the pipeline, and function by function

The first compositional step of C translation validation (docs/projects/c-tv.md, roadmap
milestone "compositional evidence"). Two kinds of composition, both reduced to `TV.Refines`:

* **Vertical** (along a pipeline of translations): refinement is transitive
  (`Refines.trans` in `Thms`), so `C → Core₁ → Core₂ → …` statements compose without re-running a
  validator on the end points; equivalence is symmetric and transitive.
* **Horizontal** (per function, in contexts): `FileBindings.setFunction b f d` replaces the
  definition of the function `f` in the file `b`. `ContextRefines impl ctxs f d d'` says that in
  every context of the list `ctxs`, the program with `f := d'` refines the one with `f := d`. A
  replacement of `f` followed by one of `g` composes (`ContextRefines.then` in `Thms`), and a
  finite list of contexts is validated by `validateContexts`, sound by `validateContexts_sound`.

**Scope.** Contexts are explicit, finite lists of closed programs: this is not contextual
refinement for *all* contexts (that needs a simulation proof over the Core LTS, or contracts at
the function's boundary), not yet expression- or statement-level, and external calls are not yet
specified by contracts. Those are the next obligations of the milestone.
-/

@[expose] public section

namespace Silmaril.Cerberus.TV

/-- Replace the definition of the function whose symbol Lem's equality identifies with `f`. -/
def _root_.Silmaril.Cerberus.Codec.FileBindings.setFunction (b : Codec.FileBindings) (f : Sym)
    (d : Core.FunDecl Codec.wireModel Unit Unit) : Codec.FileBindings :=
  { b with funs := b.funs.map fun e => if e.1.key == f.key then (e.1, d) else e }

/-- The closed program of the file `b` with `f := d`. -/
def Closed.withFunction (b : Codec.FileBindings) (f : Sym)
    (d : Core.FunDecl Codec.wireModel Unit Unit) : Closed :=
  Closed.ofBindings (b.setFunction f d)

/-- **Contextual refinement over listed contexts**: in every context `b ∈ ctxs`, the program with
`f := d'` refines the one with `f := d`. -/
def ContextRefines (impl : Spec.Impl) (ctxs : List Codec.FileBindings) (f : Sym)
    (d d' : Core.FunDecl Codec.wireModel Unit Unit) : Prop :=
  ∀ b ∈ ctxs, Refines impl (Closed.withFunction b f d) (Closed.withFunction b f d')

/-- **The context validator**: `validated` in every listed context. -/
def validateContexts (impl : Spec.Impl) (ctxs : List Codec.FileBindings) (f : Sym)
    (d d' : Core.FunDecl Codec.wireModel Unit Unit) (bounds : Bounds := {}) : Bool :=
  ctxs.all fun b => (validate impl (Closed.withFunction b f d) (Closed.withFunction b f d') bounds).verdict == .validated

end Silmaril.Cerberus.TV
