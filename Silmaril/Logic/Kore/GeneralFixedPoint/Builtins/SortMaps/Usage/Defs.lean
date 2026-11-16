module

import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Institution
import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Forgetful
import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Raw
import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.SurfaceControl
import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Checker.Institution.Defs

open Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps

#check Hom.reduct
#check Hom.reductFunctor
#check nativeInstitution
#check forgetful
#check mapTop_satisfies
#check Silmaril.Logic.Matching.SortMaps.Hom.generalSatisfaction
#check Silmaril.Logic.Matching.SortMaps.fixedSortGeneral
#check SurfaceControl.lower_native

#check Surface.Step.elaborate_forward
#check Surface.SourceSentence.mapPath
#check Surface.SourceSentence.mapPath_lower
#check Surface.sourceInstitution
#check Surface.sourceLowering
