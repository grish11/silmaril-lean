module

import Silmaril.Cerberus.Core.Dynamics.Defs

open Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics

-- Pinned concrete/impl_mem.ml:1696–1701: both provenance choices agree
-- when addresses differ. Equal-address/different-provenance ambiguity is kept.
example : primitive (.pointerCompare false)
    [.object (.pointer (.allocated 2 65536)), .object (.pointer (.allocated 3 65600))] =
    .ok .false := by cbv
example : primitive (.pointerCompare true)
    [.object (.pointer (.allocated 2 65536)), .object (.pointer (.allocated 3 65600))] =
    .ok .true := by cbv
example : primitive (.pointerCompare false)
    [.object (.pointer (.allocated 2 65536)), .object (.pointer (.allocated 3 65536))] =
    .error (.unsupported "distinct provenance pointer equality choices") := by cbv
example : primitive (.pointerCompare false)
    [.object (.pointer (.allocated 2 65536)), .object (.pointer (.allocated 2 65536))] =
    .ok .true := by cbv
example : primitive (.pointerCompare false)
    [.object (.pointer (.allocated 2 65536)), .object (.pointer (.allocated 2 65600))] =
    .ok .false := by cbv
