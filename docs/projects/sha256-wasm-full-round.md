# Full SHA-256 round compiled to WebAssembly

`Silmaril.Wasm.Examples.Sha256FullRound.Thms` checks the eight updated
working words of FIPS 180-4 §6.2.2 for one round. The C wrapper accepts
an output pointer, eight input working words, a round constant and a
schedule word. It returns void. The reference is the existing public
`Silmaril.Crypto.SHA256.Kernel.round`. [FIPS PUB 180-4](https://doi.org/10.6028/NIST.FIPS.180-4)

## Checked binary and contract

The 328-octet wasm32 binary has three function definitions. The first is
the exact 47-instruction body proved by the earlier round-word pilot.
The second is a 27-instruction body for the new `e`. The 44-instruction
wrapper calls these two functions and writes the six shifted working words
from its locals. `decode_fixture` checks those bodies, their signatures,
the void `sha256_round` export at slot 2, and the two-page memory export
at memory slot 0. The check also establishes empty imports and an absent
start function. [Round-word proof](sha256-wasm-round.md)

`run_e` evaluates the decoded scalar body for every input and preserves
its frame and store. `call_round` uses the earlier proof for `a` and
the new proof for `e` to prove a host-free Core call to the wrapper.
Its hypotheses give the caller slot and exact runtime definitions of
the wrapper and both direct callees. The two arithmetic body entries
must be well typed at the point of invocation. The wrapper's memory 0
must resolve to the supplied memory instance with an in-bounds 32-octet
destination. The destination is the unsigned interpretation of the i32
argument. Effective offsets are added as natural numbers.

The final configuration has the same caller frame and an empty result
stack. The store update replaces only the selected memory instance's
bytes. All eight four-octet little-endian loads at offsets
`0, 4, 8, 12, 16, 20, 24, 28` return the corresponding reference
words, and the memory size and every disjoint byte range are preserved.
This composition follows the binary's actual store order
`12, 8, 4, 0, 28, 24, 20, 16`.

Whole-module instantiation, out-of-bounds calls, C source semantics,
compiler correctness, schedule construction, full SHA-256, and security
are outside this proof. The separate native check instantiates the exact
artifact and invokes its export directly.

## Reproduce

```sh
tests/crypto/sha256-wasm-full-round/check.sh --lean-only
tests/crypto/sha256-wasm-full-round/check.sh
```

The full command uses Debian trixie amd64 Clang/LLD 19.1.7, package version
`1:19.1.7-3+b1`, and Node's Wasm engine. It rebuilds the three
translation units, verifies every byte against the Lean fixture, and audits
the four public theorems. It checks all eight words in each of the first two
published `abc` rounds, once at the beginning and once at the end of the
memory. Another 128 deterministic comparisons check the FIPS equations and
the untouched prefix and suffix in the real engine. [NIST SHA-256 intermediate values, pp. 1–2](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA256.pdf)

| Artifact | SHA-256 |
| --- | --- |
| Existing `a` source | `b9c9c72d2ae9f5e6d121d5434a93a251a87eab44e1c075130ce1c3f2f76e970a` |
| New `e` source | `f6e1413d2e6b7396d83cbe771b434bb19427fbb34250415384fadae43965c309` |
| Wrapper source | `d5a1b3f015524927b46e917bce8bc6e43a2db2ac3f36a966c46340cd10bd2a5f` |
| Linked Wasm module | `ba4cd633daba887fbd53053f57ea5729c6ba96ca5e0c89ae5d877be9ad136c8e` |
