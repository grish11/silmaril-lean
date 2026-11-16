# The x86-64 Wasm simulator ABI

This is the interface between an x86-64 simulator written in WebAssembly, the programs that
drive it and the environment that supplies memory, system calls and nondeterminism. It covers
location numbering, imports, exports, status codes and the System V call wrapper. It ends with
the profile that the proved Lean simulator (`Silmaril.Sim.X86.G`) implements, which deviates from
the runtime ABI in a few documented places.

**What is proved and what is tested.** The Lean development proves facts about a *certified
translator*: `Silmaril.Sim.X86.G.emit`/`emitX`/`emitProg` map instructions of a register fragment
of x86-64 to Wasm code over the location globals, and the theorems (`emit_sound`,
`method_valid`, `hwp_transfer`, `xproblem_of_wproblem`, `Silmaril.Sim.X86.Loop.xlproblem_of_lproblem`)
relate that code to `Silmaril.X86.Ext.exec`. The runtime simulator
`examples/wasm-sim/x86/x86-g.wat` (decoder, generic methods, `step`/`run`) implements the ABI
below. It is **tested** by the Rust tools in `tools/wasm-sim`, not proved.

## Locations

A location index `loc : i32` names one register-like piece of state. Registers and addresses
are `i64`; multi-byte values are little-endian.

| loc | x86-64 location |
|---|---|
| `0..15` | GPRs in hardware encoding order: rax rcx rdx rbx rsp rbp rsi rdi r8 … r15 |
| `16` | rip |
| `17` | CF |
| `18` | PF |
| `19` | AF |
| `20` | ZF |
| `21` | SF |
| `22` | OF |
| `23` | DF |

A flag location holds `0` or `1`. In the runtime G representation (one mutable global per
location) the GPRs and rip are `i64` globals and the flags `i32` globals. In the M
representation the state is an exported memory `state` laid out as Linux
`struct user_regs_struct`, with flags packed in `eflags` (CF bit 0, PF 2, AF 4, ZF 6, SF 7,
DF 10, OF 11).

## Imports (the environment)

| import | type | meaning |
|---|---|---|
| `mem.load8/16/32/64` | `(addr i64) -> i64` | zero-extended load; a trap is a fault |
| `mem.store8/16/32/64` | `(addr i64, v i64)` | store the low bits; a trap is a fault |
| `sys.syscall` | `(nr i64, a1..a6 i64) -> i64` | one system call (`syscall`: number in rax; rdi rsi rdx r10 r8 r9; result in rax) |
| `nd.undef` | `(loc i32) -> i64` | value of a location the ISA leaves undefined (e.g. AF after `and`); nondeterminism |
| `ext.call` (optional) | `(target i64) -> i32` | control reached a foreign address (dynamic linking); the import may read and write state through the exports and returns a status |

Imports are opaque. Proofs quantify over every host relation, so a memory model, scheduler or
C library can be supplied later as another Wasm module.

**`ext.call` convention.** The embedder marks an address range as foreign. When rip enters that range,
`step` calls `ext.call(rip)` instead of fetching. The registers and the stack are as the
caller's `call` left them. The import implements the callee's body, reading and writing
state through `get`/`set` and the memory imports. It returns a status. On `0` the simulator
performs the `ret` itself; any other value is returned from `step`.

## Exports

| export | type | meaning |
|---|---|---|
| `get` | `(loc i32) -> i64` | read a location |
| `set` | `(loc i32, v i64)` | write a location |
| `modelled` | `(loc i32) -> i32` | `1` if the simulator models `loc` (constant per simulator) |
| `step` | `() -> i32` | fetch, decode and execute one instruction; returns a status |
| `run` | `(fuel i64) -> i32` | `step` until the status is non-zero or the fuel runs out |
| `halt_reason` | `() -> i32` | why the last `run` stopped (optional) |
| `fuel_left` | `() -> i64` | fuel remaining after the last `run` (optional) |
| `cond` | `(cc i32) -> i32` | condition code `cc` (0..15, Intel `tttn` order) on the current flags |
| `ea` | `(base i32, index i32, scale_shift i32, disp i64) -> i64` | effective address (`-1` = no register) |
| `i_next` | `(len i32)` | `rip += len` |
| `i_<form>` | per form | **methods**: execute one decoded instruction (below) |

**Methods** are generic in operation and width: `i_alu_rr(op, w, d, s)`, `i_alu_ri`,
`i_alu_rm(op, w, d, addr)`, `i_unary_r`, `i_shift_*`, `i_muldiv_r -> status`, … with
`w ∈ {1, 2, 4, 8}`. Memory operands are computed by the program with `ea` and passed as
addresses. Methods do not move rip, except for control transfers (`i_jmp`, `i_call`,
`i_ret`). The program calls `i_next(len)` after an ordinary instruction, and before a
control transfer or `syscall` (so that rip is the next instruction's address).

**Step methods** (target naming scheme). A per-instruction method that performs a whole
step, effect and rip update together, is exported as `s_<form>_<ops>_<len>`. For example,
`s_mov_rax_rdi_3` is `mov rax, rdi` of length 3 and `s_add_rax_rax_3` is `add rax, rax` of
length 3. This is the method granularity of the Lean step specifications
(`Silmaril.Sim.X86.GCert.stepSpec`) and of the P-calls reduction
(`Silmaril.Sim.Reduce.PCalls`). Older modules omit the `_<len>` suffix (`s_mov_rax_rdi`) or use
`i_<form>_<regs>` for effect-only methods.

## Status codes

| code | meaning |
|---|---|
| `0` | ok |
| `1` | halted: returned to the sentinel return address `0xFFFF_FFFF_FFFF_F000`, or an exit system call |
| `2` | unsupported: the instruction is not modelled by this simulator (state unchanged) |
| `3` | fault (a `mem.*` import trapped) |
| `4` | out of fuel |
| `5` | breakpoint |

## Program representations

* **P-calls**: the program is a Wasm module that imports the simulator's methods. Each x86
  function becomes a Wasm function without arguments that calls one method per instruction.
  Control flow is a `loop` dispatcher over basic blocks, branching on `cond`.
* **P-inline**: the method bodies are inlined into the program (`Silmaril.Sim.X86.G.emitProg`;
  the dispatcher `Silmaril.Sim.X86.Loop.dispCode` for code with jumps).
* **P-data / P-mem**: code bytes in the simulator's own memory, or fetched through
  `mem.load*`; `step` decodes them.

## System V call wrapper

`sysv_call(desc i32) -> i64`, in a wrapper module that imports a simulator. The descriptor is
a sequence of little-endian `u64` words:

| byte offset | field |
|---|---|
| `+0` | `target` |
| `+8` | `nint` (≤ 6) |
| `+16` | `int_args[6]` |
| `+64` | `nstack` |
| `+72` | `stack_args[nstack]` |
| `+72 + 8·nstack` | result area: `rax`, `rdx`, `status` (zero in a request) |

The wrapper does the following:

1. It reads the caller's rsp `R` and puts the stack arguments at `S = (R − 8·nstack) & ~15`,
   so `stack_args[j]` is at `S + 8j`.
2. It pushes the sentinel at `S − 8` and sets `rsp := S − 8`, which is ≡ 8 (mod 16).
3. It sets rdi rsi rdx rcx r8 r9 from `int_args` (`Silmaril.X86.sysv64.intArgRegs`).
4. It records rbx rbp r12 r13 r14 r15, sets `rip := target` and runs until the sentinel.
5. It writes `rax`, `rdx` and the status word, and restores the caller's rsp.

The status word is `0` exactly when the call meets the return conditions:

| bit | meaning |
|---|---|
| 0 | the simulator stopped elsewhere than at the sentinel (simulator status in bits 8..15) |
| 1 | rsp after the return differs from the entry rsp + 8 |
| 2..7 | rbx rbp r12 r13 r14 r15 not preserved (one bit each) |
| 16 | malformed descriptor (`nint > 6`) |
| 17 | entry check failed (entry rsp mod 16 ≠ 8, or `[rsp]` ≠ sentinel) |

The Lean model of the wrapper is `Silmaril.Sim.SysV`. It covers the descriptor
(`SysVCall.encode`/`decode`), the entry state (`entryCore`) and the Wasm wrapper code
(`wrapperCode`, status bits 1..7 as `statusOf`). The theorems are `wrapper_sound` and the
reduction `xgoal_of_wgoal`, from the Wasm goal `WGoal` to the x86 goal `XGoal` against
`FnContract` `AbiEntry`/`AbiReturn`. Two differences from the runtime wrapper: argument
registers beyond `nint` are set to zero (the runtime keeps their values), and bit 0 cannot
occur, because the fragment's final `ret` returns to the sentinel exactly when rsp is the
entry rsp.

## The Lean G profile

`Silmaril.Sim.X86.G` implements the location numbering above with these deviations from the
runtime G representation. Each one keeps every method straight-line `i64` code that the
verification-condition generator `wpc` evaluates.

| aspect | runtime ABI (`x86-g.wat`) | Lean G (`Silmaril.Sim.X86.G`) |
|---|---|---|
| flag globals | `i32`, `0`/`1` | `i64`, `0`/`1` (`b64`); `cmov` needs no `i64.extend_i32_u` |
| `i_next` | `(len i32)` | `len` is an `i64` constant (`nextCode len`) |
| DF | location `23`, an `i32` global | no global: the canonical store `encStore` has the 23 globals `0..22` |
| PF, AF | modelled | globals exist but are unmodelled (no method writes them; `Enc` ignores them) |
| jumps | the program calls `i_next(len)`, then `i_jmp`/`cond` | `jcc rel8`/`jmp rel8` methods advance rip themselves (`jccCode`, `jmpCode`: `rip += len + offset`) |
| undefined flags | a value drawn from `nd.undef(loc)` | relational: a flag global holds some bit, and `Enc` admits any bit where `Silmaril.X86.State` leaves the flag undefined (`FlagEnc`, `FlagValue.Admits`) |
| methods | generic in operation, width and registers | one method per instruction instance (`emit i len`; registers fixed, no `br_table`) |
| memory | `mem.*` imports | none in G; `Silmaril.Sim.X86.GM` adds a guest memory window in Wasm memory 0 |

## The RV64 simulators

The RV64 simulators (`examples/wasm-sim/rv64/parts/*.wat`, assembled by `wasm-sim-rv wat` into
`examples/wasm-sim/rv64/gen/rv64-{g,m}-{base,alu,nosys,full}.wat`) follow the same scheme with
RISC-V locations and implement RV64IM. They are **tested** against `qemu-riscv64` and the
executable Lean model, not proved; the proved RV64 results are about the memory-state simulator
`Silmaril.Sim.RV64.Mem.simM` and the reductions in `Silmaril.Sim.RV64`.

- **Locations**: `x1`–`x31` are locations 1–31 and `pc` is location 32. `x0` reads 0 and its
  writes are discarded, as in `Silmaril.RiscV.read`/`write`.
- **State representation G**: one mutable `i64` global per location (`parts/state-g.wat`).
- **State representation M**: an exported memory `state` holding Linux arch/riscv
  `struct user_regs_struct` (32 × u64: byte offset 0 is `pc`, offset `8·i` is `x_i`), followed
  by a u64 valid mask at offset 256 (`parts/state-m.wat`). `Silmaril.Sim.RV64.Mem` uses the
  same layout, with `code_end` at offset 264 and the program from `0x1000`.
- **Imports**: `mem.load*`/`mem.store*` for guest memory (a trap is a fault), `mem.load32` for
  instruction fetch in the P-mem representation, and `sys.syscall` (number `a7`, arguments
  `a0`–`a5`, result in `a0`) for `ecall`.
- **Status codes**: as above: `0` ok, `1` halted (`ebreak`, the sentinel return address
  `0xFFFF_FFFF_FFFF_F000`, or `exit`/`exit_group`), `2` undecodable or unsupported (state
  unchanged), `3` fault (misaligned `pc`, branch or jump target, or a trapping `mem.*` import),
  `4` out of fuel.
- **Lattice points**: `base` ⊑ `alu` ⊑ `nosys` ⊑ `full` (instruction groups `parts/grp-*.wat`);
  `wasm-sim-rv lattice` checks the refinement on random steps.

Commands (crate `tools/wasm-sim`, binary `wasm-sim-rv`):

```sh
cargo build --release --manifest-path tools/wasm-sim/Cargo.toml
B=tools/wasm-sim/target/release/wasm-sim-rv
$B wat g full out.wat                 # assemble a simulator (the gen/ files are its outputs)
$B lattice 100000                     # random-step refinement checks between lattice points
$B lean-oracle 20000 .                # random steps vs Silmaril.RiscV.Ext.MState.step (lake)
examples/wasm-sim/rv64/run-tests.sh   # everything, incl. difftests: needs clang for riscv64,
                                      # ld.lld and qemu-riscv64
```

