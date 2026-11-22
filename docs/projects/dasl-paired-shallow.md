# DASL links with two spellings

`Silmaril.Formats.Dasl.PairedShallow.Thms` uses `Shallow (Concrete × Abstract)`:
each link occurrence carries two names under a shared object/blob tag. The
concrete and abstract projections discard the other name without changing
the inline shape. `Agrees` checks a caller-chosen relation on the two typed
tagged links, and `AgreesBy` uses the graph of a selected name map.
`ofConcrete` attaches the graph's abstract name to each concrete spelling;
the concrete projection is unchanged and the abstract one is the shallow
name action. `diagonal` retains the same spelling in both projections and
agrees by the identity map.

`AbstractValid` asks for finite `Expands` of the abstract projection in a
binding abstract store. Such an expansion is unique. `FullNames` additionally
requires a separately supplied root binding. Agreement alone checks no store,
and abstract validity says nothing about concrete byte availability, codec
eligibility or hash integrity. An object binding never resolves a blob link.

`lake build --wfail +Silmaril.Formats.Dasl.PairedShallow.Examples` checks two
different name types, both lanes, agreement without resolvability, and failure
of agreement for a mismatched spelling.
