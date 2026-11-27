module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.ProductState

/-! # A pair of Bits is the packed state of two rows

No seed and no quotient law is added. Nothing is inferred from a model.

## The isomorphism

* `pairDec_pairEnc`: decoding and then encoding is the identity on
  `States 1`. An equation of default Paper: product β and the native case
  on a constructor.
* `pairEnc_pairDec`: encoding and then decoding is the identity on pairs,
  in the opt-in quotient. It uses the native case on a variable, product
  η, and unit η: the decoded first Bit is built on literal unit, and the
  original one on a unit variable. Unit η is an existing seed; this
  direction is not claimed for default Paper.

## Transport of iteration

`Factors.of_conjugate`: let `enc` and `dec` be an encoding and a decoding
between a state type `S` and `States K` with `Retracts S enc dec`. If the
body of a loop on `S`, conjugated by them, is the dispatcher step of a
router table,

`dec ; body ; postRegion enc  =  dispatch K t.rows`,

then the loop factors through the packed loop: `Factors dec (loopRegion S
body) t`. The proof is the roll law of iteration in default Paper, and
the section in the quotient. It is not specific to pairs.

## A body written on pairs: what is proved and what is open

`pairBody l` is written on a pair `(x, y)`: it sends a request with `y`,
returns `x` on the left reply, and repeats with `(r, x)` on the right
reply `r`. Both Bits are used: one is observed in the query, the other is
returned and becomes the second component of the next state.

`Task.pairStep l` is the equation above for this body and `pairRouter l`.
**It is not proved.** It is an equation between two explicit regions on
`States 1`; row by row it needs product β under the request, the encoding
of a pair whose first Bit is a variable, and unit η for the constants of
the router's actions.

* `pairLoop_factors_of`: given `Task.pairStep l`, the loop on pairs
  factors through the packed loop of `pairRouter l`.
* `pairLoop_complete_of`: given it for `l` and `l'`, the two loops on
  pairs are equal at the product-state entry exactly when they are valid
  in every supported model.

So no completeness is established for a loop on pairs here. No source
flat CFG is treated, and nothing is claimed for default Paper.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (seqValueBranches caseValueBranches)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (ofRegion ofType)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking
  (Valid.symm Valid.trans)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity


variable {K : Nat}

/-! ## The isomorphism -/

/-- Decoding and then encoding is the identity on the packed state, in
default Paper. -/
theorem pairDec_pairEnc :
    ofRegion pairDec_typed ≫ ofRegion pairEnc_typed = 𝟙 (ofType (Φ := signature.Instr) (States 1)) :=
  Tables.dec_enc

/-- Encoding and then decoding is the identity on pairs, in the opt-in
quotient. -/
theorem pairEnc_pairDec : Retracts Pair pairEnc pairDec :=
  Tables.enc_dec

/-! ## Transport of iteration -/

/-- A loop whose body, conjugated by an encoding with a section, is the
dispatcher step of a router table factors through its packed loop. -/
theorem Factors.of_conjugate {S : Ty Empty} {enc dec body : Region signature.Instr}
    (he : ValueBranches [S] enc [States K]) (hd : ValueBranches [States K] dec [S])
    (hb : ValueBranches [S] body [Silmaril.coprod Bit S]) (ret : Retracts S enc dec) (t : Router K)
    (hstep : Eqv false [States K] (seqRegion dec (seqRegion body (postRegion enc))) (dispatch K t.rows)
      [Silmaril.coprod Bit (States K)]) : Factors dec (loopRegion S body) t :=
  Tables.conjugate_factors he hd hb ret t hstep

/-! ## A body written on pairs -/

/-- Given the open step equation, the loop on pairs factors through the
packed loop of its router table. -/
theorem pairLoop_factors_of (l : Bool) (h : Task.pairStep l) :
    Factors pairDec (loopRegion Pair (pairBody l)) (pairRouter l) :=
  Factors.of_conjugate pairEnc_typed pairDec_typed (pairBody_typed l) pairEnc_pairDec (pairRouter l) h

/-- Given the open step equations, two loops on pairs are equal at the
product-state entry exactly when they are valid in every supported model. -/
theorem pairLoop_complete_of (l l' : Bool) (h : Task.pairStep l) (h' : Task.pairStep l') :
    Eqv false [Pair] (loopRegion Pair (pairBody l)) (loopRegion Pair (pairBody l')) [Bit] ↔
      Valid (loopRegion_typed (pairBody_typed l)).hasType (loopRegion_typed (pairBody_typed l')).hasType :=
  Tables.pair_complete_of l l' h h'

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
