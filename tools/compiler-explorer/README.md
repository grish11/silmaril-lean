# compiler-explorer: source ↔ target links with checked claims

[docs/projects/compiler-explorer.md](../../docs/projects/compiler-explorer.md) is the guide.

| file | what |
| --- | --- |
| `export.lean` | the evidence exporter: `lake env lean --run tools/compiler-explorer/export.lean MANIFEST OUT` decides each obligation from the Lean build (theorem type = statement up to reducible unfolding, standard axioms) |
| `cexplorer.py` | the database (`ingest`, `evidence`, `status`) and the read-only server (`serve`) |
| `fixtures.py` | `build` and `listings` (Docker, the pinned gcc image, `--network none`), `manifests` (deterministic, no Docker) |
| `ui/` | the page (`view.js` holds the pure functions, `app.js` the DOM) |
| `tests/` | database and API tests (`python3 -I tests/test_cexplorer.py`), view tests (`node --test tests/view.test.mjs`) |
| `check.sh` | everything above, end to end |

Python 3.11+ (standard library only) and Node 24+.
