//! Layer 4, rooms: the `room` record, the nodes of the room level of the logic graph
//! ([`super::logic`]).
use super::*;
use serde::Deserialize;

table! {
    /// `silmaril room NAME := R` over silmaril's `Room`, or a family `∀ x⃗, Room` (`arity`
    /// binders, printed in `params`); Lean fills `sen` and `mod` (the pretty-printed sentence type
    /// and model carrier, under the binders), `type`, `levels`, and, when the room is `A.I.obj S`
    /// for a registered institution `A`, the `institution` and the `signature` `S`. A problem
    /// (`silmaril problem N in R`) needs a closed room (`arity` 0). Columns added after v0.1 are
    /// null (`arity` 0) in older dumps.
    Room = "rooms", key("sid"), unique("name") {
        #[serde(skip)] sid: String = "TEXT NOT NULL",
        name: String = "TEXT NOT NULL",
        decl: String = "TEXT NOT NULL",
        sen: String = "TEXT NOT NULL",
        r#mod: String = "TEXT NOT NULL",
        module: String = "TEXT NOT NULL",
        #[serde(skip)] origin: String = "TEXT NOT NULL",
        doc: Option<String> = "TEXT",
        #[serde(default)] arity: i64 = "INTEGER NOT NULL DEFAULT 0",
        params: Option<String> = "TEXT",
        r#type: Option<String> = "TEXT",
        levels: Option<String> = "TEXT",
        institution: Option<String> = "TEXT",
        signature: Option<String> = "TEXT",
        title: Option<String> = "TEXT",
        source: Option<String> = "TEXT",
        scope: Option<String> = "TEXT",
    }
    extra { #[serde(rename = "sid")] sid_override: Option<String>, }
}
