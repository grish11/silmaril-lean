module

public import Silmaril.Semantics.Calco2019.Maybe.Hyperextensive.Defs
public import Silmaril.Semantics.Calco2019.Maybe.LoopDecomposition.Thms
import Silmaril.Proofs.Semantics.Calco2019.Maybe.Hyperextensive

/-! # Deterministic loop decomposition in hyperextensive categories -/

public section

universe u v

namespace Silmaril.Calco2019.Maybe

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Hyperextensive C] {P : Coproducts C}

/-- Pulling back the return component along the transition gives all exact
finite exit layers. Their complemented union leaves an invariant residual. -/
theorem hyperextensive_decompose {X Y : C} (f : X ⟶ P.sum Y X) :
    Nonempty (LoopDecomposition f) :=
  Proofs.hyperextensive_decompose P f

/-- A total Elgot structure on the Maybe monad over a hyperextensive category
is initial. The hypothesis supplies the total iteration laws on that monad. -/
noncomputable def initialOfHyperextensive {E : C} (terminal : IsTerminal E)
    (S : GuardedElgotMonad P) (hs : S.IsElgot) (hm : S.monad = monad P E) :
    IsInitial (⟨S, hs⟩ : TotalElgot P) :=
  initialOfDecomposition terminal S hs hm fun f => hyperextensive_decompose f

end Silmaril.Calco2019.Maybe
