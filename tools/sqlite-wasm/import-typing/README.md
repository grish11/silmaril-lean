# SQLite reactor typed import addresses

`reactorTypedAddressCompatibility` proves that the 23 canonical typed
import entries satisfy Core `ExternAddrOk` in order, for the import
types of any `ModuleOk` proof of the pinned reactor. The proof derives
the unique closed types with the ordinary allocation law, checks
the exact imported-type lookup equation, and uses the soundness
theorem for the ordinary external address checker.
[Original decode](../whole-module/README.md) · [Typed import fixture](../element-init/README.md)

The theorem takes the validated module judgment as a premise.
Its result discharges the separate external-address requirement for
that fixture. The check covers types and addresses.

After the [original decoder check](../whole-module/README.md#reproduce), run

```sh
bash tools/sqlite-wasm/import-typing/check.sh .lake/sqlite-wasm/lean/SqliteWasm
```

The downstream module imports `SqliteWasm.ImportTyping` and uses the
theorem on the result of the original decoder. It prints the public
theorem's axiom dependencies.
[Statements](ImportTyping.lean) · [Downstream check](ImportCheck.lean)
