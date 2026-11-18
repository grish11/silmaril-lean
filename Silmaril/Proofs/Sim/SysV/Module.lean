module

public import Silmaril.Sim.SysV.Defs

/-!
# The quoted wrapper module

`sysvMaxModule_body`: the body of the quoted `sysv_call_max` is the generated
`wrapperCode 0 maxCode`, so `max_wgoal`/`max_sysv` are statements about that function's code
(in the frame `ArgLocals` describes: seven parameters and eight `i64` locals).
-/

@[expose] public section

namespace Silmaril.Sim.SysV

set_option maxRecDepth 20000 in
theorem sysvMaxModule_body :
    sysvMaxModule.funcs[0].body = wrapperCode 0 Silmaril.Sim.X86.Max.maxCode := rfl

theorem sysvMaxModule_locals : sysvMaxModule.funcs[0].locals.length = 8 := rfl

end Silmaril.Sim.SysV
