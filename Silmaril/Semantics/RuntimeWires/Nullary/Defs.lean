module

public import Silmaril.Semantics.RuntimeWires.Computations.Defs

@[expose] public section

/-!
# Nullary effectful generator

The one-generator, empty-object signature tests the trivial-centre assertion
preceding Lemma 5.3 (pp. 9:15–9:16) in Mario Román and Paweł Sobociński,
*String Diagrams for Premonoidal Categories*, arXiv:2305.06075v5.

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.Nullary

open CategoryTheory Presentation

/-- One effectful generator with empty input and output words. -/
def signatureWithScalar : EffectfulPolygraph.{0,0} where
  Obj := PEmpty
  pure := Signature.empty PEmpty
  effect := ⟨Unit, fun _ => [], fun _ => []⟩

/-- The generator at the single-runtime boundary. -/
def generator : Diagram (signature signatureWithScalar) [none] [none] :=
  Diagram.gen (S := signature signatureWithScalar) (Edge.effect (G := signatureWithScalar) ())

/-- The empty value word. This is the sole object of the computation category. -/
def unitWord : Computations signatureWithScalar := ⟨[]⟩

/-- The nullary effect interpreted as an arrow of the computation category. -/
def effectfulScalar : unitWord ⟶ unitWord :=
  Diagram.Presented.ofTerm generator

end Silmaril.RuntimeWires.Nullary
