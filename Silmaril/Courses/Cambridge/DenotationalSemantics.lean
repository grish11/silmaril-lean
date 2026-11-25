module

public import Silmaril.Courses.Cambridge.DenotationalSemantics.Adequacy
public import Silmaril.Courses.Cambridge.DenotationalSemantics.Constructions
public import Silmaril.Courses.Cambridge.DenotationalSemantics.Denotation
public import Silmaril.Courses.Cambridge.DenotationalSemantics.FullAbstraction
public import Silmaril.Courses.Cambridge.DenotationalSemantics.Introduction
public import Silmaril.Courses.Cambridge.DenotationalSemantics.LeastFixedPoints
public import Silmaril.Courses.Cambridge.DenotationalSemantics.PCF
public import Silmaril.Courses.Cambridge.DenotationalSemantics.ScottInduction
public import Silmaril.Courses.Cambridge.L1.DenotationalInstitution
public import Silmaril.Courses.Cambridge.L1.EffectfulDenotational.Institution
public import Silmaril.Courses.Cambridge.L1.LetIter.Thms
import Silmaril.Courses.Cambridge.DenotationalSemantics.L1Examples
import Silmaril.Courses.Cambridge.DenotationalSemantics.L1EffectfulExamples
import Silmaril.Courses.Cambridge.DenotationalSemantics.L1LetIterExamples

/-! # Cambridge Part II Denotational Semantics

A chapter-by-chapter index of Meven Lennon-Bertrand's lecture notes,
version of December 5, 2024 [lennonbertrand2024lecture], building on notes by
Pitts, Winskel and Fiore. Numbered wrappers retain the notes' item numbers
and printed pages. They use the reusable domain, typed-lambda, Imp and PCF
libraries; changes to a source statement are identified beside its wrapper.

| Chapter | Module |
| --- | --- |
| §1 Introduction and a factorial loop | `Introduction` |
| §2 Least fixed points | `LeastFixedPoints` |
| §3 Constructions on domains | `Constructions` |
| §4 Scott induction | `ScottInduction` |
| §5 PCF syntax and operational semantics | `PCF` |
| §6 Denotational semantics for PCF | `Denotation` |
| §7 Adequacy and contextual extensionality | `Adequacy` |
| §8 Parallel or and full abstraction | `FullAbstraction` |

The final chapter includes the failure of full abstraction for sequential PCF
and full abstraction for PCF extended with parallel or, including open terms
and the contextual preorder. Its supporting library proves finite-projection
density and definability. The source's later discussions of dI-domain models,
Loader's theorem and game models remain background to this index.

The companion L1 adapters interpret Part IB expressions. The effectful
denotation agrees with finite returns, stuck states, and infinite reduction.

See `docs/courses/cambridge.md` for build commands and a guide to the course
and reusable APIs.
-/
