module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Defs

/-!
# Checked WIT writer imports for Core Wasm

Use `Own.Session.Contract.link` to check the import and resolve memory for `Contract.env`,
or `Contract.traces` to observe the linked host's export sessions. The host decodes the entire selected
schema before it calls the writer or commits any owned moves. `Own.Session.Contract.attempt`
reports the typed reason for rejection at the call; Core sees a trap with the call's store.

`Own.Session.Thms` specifies rejection and move-only state preservation for traced sessions.
`Own.Projection` is a separate analysis of successful legacy traces, not a host or an accepted
tree language theorem for these checked sessions.
-/
