# SQLite Track E checks and replay v1

The [coverage inventory](coverage-v1.md) identifies the public contracts and
their upstream references. The [architecture guide](architecture.md) gives
separate reproduction commands for the original graph increment.

## Local verification

Use the repository's `lean-toolchain` and `lake-manifest.json`. The toolchain
for this increment is `nightly-2026-11-05` at
`67dafde474fbaf278d6d7f822068549bf6e532fa`. Mathlib and CSLib are pinned at
`569134c2fc750d92baa85d50cd925a7e20a93dd2`. Install the Covalence scoper
from the repository's CI action for the scoped make command.
[Toolchain](../../../lean-toolchain) · [Lake manifest](../../../lake-manifest.json) ·
[Scoper binary pin](../../../.github/actions/lake-cache-tool/action.yml)

Run from the repository root with Bash. The aggregate consumer has just
one import, `Silmaril.Machine.SQLite.Architecture.All`. The other check
targets exercise the component and foundation regressions.

```bash
set -euo pipefail
root=Silmaril.Machine.SQLite
lake build --wfail +"$root".Architecture.Checks +"$root".Accessories.Checks \
  +"$root".CommandProcessor.Checks +"$root".CommandProcessor.Execute.Checks \
  +"$root".VirtualMachine.Checks +"$root".VirtualMachine.Traced.Checks \
  +"$root".VirtualMachine.Mutable.Checks +"$root".VirtualMachine.Concurrent.Checks \
  +"$root".BTree.Checks +"$root".Relational.Checks \
  +"$root".Relational.Bridge.Checks +"$root".TrackA.Read.Adapter.Checks \
  +"$root".TrackB.Read.Interaction.Checks +Silmaril.Semantics.SQLite.Relational.Checks
```

To reproduce the PR-scoped source, build, runtime, and integration checks,
set `base` to the PR's main-side base and check out the exact PR head or the
CI merge checkout. On the CI merge checkout, use `base=$(git rev-parse HEAD^1)`.
On an archived merge of the aggregate, its first parent is the main-side base
and its second parent is the PR head. The workflow computes its target list
from the diff against its own main-side base.

```bash
scoped=$(make -s scope BASE="$base")
full=$(make -s scope)
targets=$(python3 scripts/ci-targets.py --scoped "$scoped" --full "$full")
make check CHECK_TARGETS="$targets"
```

The following replays the diagram headers, aggregate, public components,
proofs and fixtures in the build above. Each process replays one olean's
declarations in the kernel against its imported oleans. The list selects the
separate implementation proof modules explicitly.
[Replay driver](../../../tools/compiler-explorer/Replay.lean)

```bash
paths=(
  Silmaril/Machine/SQLite/{Accessories,Backend,BTree,CodeGenerator,CommandProcessor,Compiler}
  Silmaril/Machine/SQLite/{Core,Interface,Pager,Parser,TestCode,Tokenizer,Utilities,VFS,VirtualMachine}
  Silmaril/Proofs/Machine/SQLite/{BTree,CodeGenerator,CommandProcessor,Interface,Pager,Parser,Tokenizer,VFS,VirtualMachine}
  Silmaril/Machine/SQLite/Architecture/{Defs,Thms,All,Checks}.lean
)
rg --files -g '*.lean' "${paths[@]}" | sort |
  while IFS= read -r file; do
    module=${file%.lean}
    SILMARIL_REPLAY_MODULE="${module//\//.}" \
      lake env lean -DwarningAsError=true tools/compiler-explorer/Replay.lean || exit 1
  done
```

The architecture consumer prints all new public theorem dependencies and
representative dependency theorem audits. Check the reported axioms against
`policy.toml`. The source gate applies separately to declarations and uses of
the forbidden decision tactic. [Axiom policy](../../../policy.toml) ·
[Audit declarations](../../../Silmaril/Machine/SQLite/Architecture/Checks.lean)

```bash
audit=$(mktemp)
lake env lean -DautoImplicit=false -DwarningAsError=true \
  Silmaril/Machine/SQLite/Architecture/Checks.lean | tee "$audit"
python3 - "$audit" <<'PY'
import pathlib
import re
import sys
import tomllib

source = pathlib.Path("Silmaril/Machine/SQLite/Architecture/Checks.lean").read_text()
log = pathlib.Path(sys.argv[1]).read_text()
records = re.findall(r"'[^']+' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", log)
expected = len(re.findall(r"^#print axioms ", source, re.M))
if len(records) != expected:
    raise SystemExit(f"found {len(records)} audit results, expected {expected}")
with open("policy.toml", "rb") as policy:
    allowed = set(tomllib.load(policy)["standard"])
used = {name.strip() for record in records for name in record.split(",") if name.strip()}
if used - allowed:
    raise SystemExit(f"unexpected axioms: {sorted(used - allowed)}")
print(f"passed {len(records)} theorem audits")
PY
```

## Landed pins and hosted verification

Each row records the merge on main, the head checked by hosted CI, and the
successful Lean, CI result, and time-budget jobs for that head. Check the
workflow run's `headSha` with `gh run view RUN --json headSha,event,conclusion`.
The budget job enforces the scoped limit outside Lean module compilation.
[CI workflow](../../../.github/workflows/ci.yml) ·
[Budget policy](../../../scripts/check-ci-time.py)

| Increment | Merge SHA | Exact PR head | Hosted jobs at that head |
| --- | --- | --- | --- |
| [A typed read #3572](https://github.com/hiloopai/silmaril-lean/pull/3572) | [`f20bc085ccf72ba77bfd882823a11deb60556a38`](https://github.com/hiloopai/silmaril-lean/commit/f20bc085ccf72ba77bfd882823a11deb60556a38) | `ff47767fed5c53ea9a357b3da53493314fd4287a` | [Lean](https://github.com/hiloopai/silmaril-lean/actions/runs/45760815493/job/139710461026) · [CI](https://github.com/hiloopai/silmaril-lean/actions/runs/45760815493/job/139711469830) · [Time budget](https://github.com/hiloopai/silmaril-lean/actions/runs/45760815493/job/139711653708) |
| [A repeated read #3623](https://github.com/hiloopai/silmaril-lean/pull/3623) | [`26a59ab4f3131bde9cee45053d678fa5b961886f`](https://github.com/hiloopai/silmaril-lean/commit/26a59ab4f3131bde9cee45053d678fa5b961886f) | `4994778f84b9bee57c8624e37b2deb618567881c` | [Lean](https://github.com/hiloopai/silmaril-lean/actions/runs/45762825175/job/139716711340) · [CI](https://github.com/hiloopai/silmaril-lean/actions/runs/45762825175/job/139717320159) · [Time budget](https://github.com/hiloopai/silmaril-lean/actions/runs/45762825175/job/139717402167) |
| [A rollback-mode write #3580](https://github.com/hiloopai/silmaril-lean/pull/3580) | [`f4e150fb9424a0c030c6a662d18d078adbbbdd82`](https://github.com/hiloopai/silmaril-lean/commit/f4e150fb9424a0c030c6a662d18d078adbbbdd82) | `b8981da11ba8ce8a066b9d8895ce34b40e6cc859` | [Lean](https://github.com/hiloopai/silmaril-lean/actions/runs/45769774550/job/139740521097) · [CI](https://github.com/hiloopai/silmaril-lean/actions/runs/45769774550/job/139742442995) · [Time budget](https://github.com/hiloopai/silmaril-lean/actions/runs/45769774550/job/139742860794) |
| [B designated rowid leaf #3574](https://github.com/hiloopai/silmaril-lean/pull/3574) | [`d9e5d55d09a67486e7b36eda29032f0ce1d6f9eb`](https://github.com/hiloopai/silmaril-lean/commit/d9e5d55d09a67486e7b36eda29032f0ce1d6f9eb) | `c27fd1a7ef45e3de07465de3f731c143deef1b62` | [Lean](https://github.com/hiloopai/silmaril-lean/actions/runs/45763048111/job/139717740818) · [CI](https://github.com/hiloopai/silmaril-lean/actions/runs/45763048111/job/139718373110) · [Time budget](https://github.com/hiloopai/silmaril-lean/actions/runs/45763048111/job/139718478799) |
| [C relational foundation #3565](https://github.com/hiloopai/silmaril-lean/pull/3565) | [`611702d27cc6e43cbb7f3ec74013246d39d322ef`](https://github.com/hiloopai/silmaril-lean/commit/611702d27cc6e43cbb7f3ec74013246d39d322ef) | `a5a0a51b6795b74527795a1edfa3c34d55b144bc` | [Lean](https://github.com/hiloopai/silmaril-lean/actions/runs/45752990563/job/139685437061) · [CI](https://github.com/hiloopai/silmaril-lean/actions/runs/45752990563/job/139686346143) · [Time budget](https://github.com/hiloopai/silmaril-lean/actions/runs/45752990563/job/139686916431) |
| [D1 value and affinity #3648](https://github.com/hiloopai/silmaril-lean/pull/3648) | [`448bd85d9dfd7992855badbd4048999f05b4e704`](https://github.com/hiloopai/silmaril-lean/commit/448bd85d9dfd7992855badbd4048999f05b4e704) | `e153b6ff27d768b392ab3529743e93e74e8a5046` | [Lean](https://github.com/hiloopai/silmaril-lean/actions/runs/45756375554/job/139696015664) · [CI](https://github.com/hiloopai/silmaril-lean/actions/runs/45756375554/job/139696568737) · [Time budget](https://github.com/hiloopai/silmaril-lean/actions/runs/45756375554/job/139696605568) |
| [D2 schema and catalog #3688](https://github.com/hiloopai/silmaril-lean/pull/3688) | [`d99abfe5131eec3697fa32e41b7d1b0962bcaac9`](https://github.com/hiloopai/silmaril-lean/commit/d99abfe5131eec3697fa32e41b7d1b0962bcaac9) | `9fd6af51e118f27d364e07b2021f332e4f0a4c30` | [Lean](https://github.com/hiloopai/silmaril-lean/actions/runs/45761682548/job/139713137335) · [CI](https://github.com/hiloopai/silmaril-lean/actions/runs/45761682548/job/139713785544) · [Time budget](https://github.com/hiloopai/silmaril-lean/actions/runs/45761682548/job/139713824088) |
| [D3 generic executor #3645](https://github.com/hiloopai/silmaril-lean/pull/3645) | [`fb129a1cab5eb2108bb24224943538885b87838a`](https://github.com/hiloopai/silmaril-lean/commit/fb129a1cab5eb2108bb24224943538885b87838a) | `eedbe97f3af123fc7f88773daa4115cad1824dfc` | [Lean](https://github.com/hiloopai/silmaril-lean/actions/runs/45756176205/job/139695688999) · [CI](https://github.com/hiloopai/silmaril-lean/actions/runs/45756176205/job/139696171136) · [Time budget](https://github.com/hiloopai/silmaril-lean/actions/runs/45756176205/job/139696223538) |
| [D3 catalog executor #3745](https://github.com/hiloopai/silmaril-lean/pull/3745) | [`86f7e9bb95c5412fe4bd9c9b2ae6684c3151dacd`](https://github.com/hiloopai/silmaril-lean/commit/86f7e9bb95c5412fe4bd9c9b2ae6684c3151dacd) | `2c710eda48f3eebf3bbed580f79fe2fa9fd8a40b` | [Lean](https://github.com/hiloopai/silmaril-lean/actions/runs/45763819075/job/139721121498) · [CI](https://github.com/hiloopai/silmaril-lean/actions/runs/45763819075/job/139722029809) · [Time budget](https://github.com/hiloopai/silmaril-lean/actions/runs/45763819075/job/139722139689) |
| [D4 storage bridge #3774](https://github.com/hiloopai/silmaril-lean/pull/3774) | [`7e7c876bd9132bb70302f02fbe6bea6493eda0ca`](https://github.com/hiloopai/silmaril-lean/commit/7e7c876bd9132bb70302f02fbe6bea6493eda0ca) | `0044819e6bf9e528e7ad755b21f19dbb62bc9ce7` | [Lean](https://github.com/hiloopai/silmaril-lean/actions/runs/45765581548/job/139725853367) · [CI](https://github.com/hiloopai/silmaril-lean/actions/runs/45765581548/job/139727256505) · [Time budget](https://github.com/hiloopai/silmaril-lean/actions/runs/45765581548/job/139727975084) |
| [D aggregate #3810](https://github.com/hiloopai/silmaril-lean/pull/3810) | [`c8b56fe407a733112f059d712f6cac6c0ba0891a`](https://github.com/hiloopai/silmaril-lean/commit/c8b56fe407a733112f059d712f6cac6c0ba0891a) | `0858a4fe6b07f5d318399f94299090cc08988010` | [Lean](https://github.com/hiloopai/silmaril-lean/actions/runs/45768151941/job/139734688951) · [CI](https://github.com/hiloopai/silmaril-lean/actions/runs/45768151941/job/139735723518) · [Time budget](https://github.com/hiloopai/silmaril-lean/actions/runs/45768151941/job/139736814304) |
| [E diagram #3903](https://github.com/hiloopai/silmaril-lean/pull/3903) | [`1ae7691dbab625f88d112ca1147fe876675b10e7`](https://github.com/hiloopai/silmaril-lean/commit/1ae7691dbab625f88d112ca1147fe876675b10e7) | `509bced556ac443801d31c4df581d5b8307c31e8` | [Lean](https://github.com/hiloopai/silmaril-lean/actions/runs/45776439355/job/139761703562) · [CI](https://github.com/hiloopai/silmaril-lean/actions/runs/45776439355/job/139762881550) · [Time budget](https://github.com/hiloopai/silmaril-lean/actions/runs/45776439355/job/139763105215) |
| [E front end #3911](https://github.com/hiloopai/silmaril-lean/pull/3911) | [`322ae3f3cd7e5b362c2f70d6498ee1b148e132a9`](https://github.com/hiloopai/silmaril-lean/commit/322ae3f3cd7e5b362c2f70d6498ee1b148e132a9) | `8f869a5f3fc311abf97e55ae90a3bc8aa0521e25` | [Lean](https://github.com/hiloopai/silmaril-lean/actions/runs/45776974472/job/139763120184) · [CI](https://github.com/hiloopai/silmaril-lean/actions/runs/45776974472/job/139764366252) · [Time budget](https://github.com/hiloopai/silmaril-lean/actions/runs/45776974472/job/139764409715) |
| [E point VM #3905](https://github.com/hiloopai/silmaril-lean/pull/3905) | [`51e35bc7f92cae9c0a2fc28ec29f0d758d6e73cf`](https://github.com/hiloopai/silmaril-lean/commit/51e35bc7f92cae9c0a2fc28ec29f0d758d6e73cf) | `7713b64d75661e79d002e8fdd9639c2888cb472e` | [Lean](https://github.com/hiloopai/silmaril-lean/actions/runs/45776501637/job/139762144507) · [CI](https://github.com/hiloopai/silmaril-lean/actions/runs/45776501637/job/139763241049) · [Time budget](https://github.com/hiloopai/silmaril-lean/actions/runs/45776501637/job/139763691712) |
| [E compiler/VM #3927](https://github.com/hiloopai/silmaril-lean/pull/3927) | [`fdc481d42de1064b826230bf1c4fdc405fa27245`](https://github.com/hiloopai/silmaril-lean/commit/fdc481d42de1064b826230bf1c4fdc405fa27245) | `6bdc08261da0bcf13f72763d4ecc28284cbc1a73` | [Lean](https://github.com/hiloopai/silmaril-lean/actions/runs/45778467214/job/139768330675) · [CI](https://github.com/hiloopai/silmaril-lean/actions/runs/45778467214/job/139769625168) · [Time budget](https://github.com/hiloopai/silmaril-lean/actions/runs/45778467214/job/139769724729) |
| [E backend #3913](https://github.com/hiloopai/silmaril-lean/pull/3913) | [`7d80ceaf976202c154d87d2dc83614f6a73a9e30`](https://github.com/hiloopai/silmaril-lean/commit/7d80ceaf976202c154d87d2dc83614f6a73a9e30) | `0082b172cd0247c7496ce6a55e7c69c32bde9860` | [Lean](https://github.com/hiloopai/silmaril-lean/actions/runs/45777045519/job/139763856510) · [CI](https://github.com/hiloopai/silmaril-lean/actions/runs/45777045519/job/139764739339) · [Time budget](https://github.com/hiloopai/silmaril-lean/actions/runs/45777045519/job/139764924543) |
| [E traced and mutable VM #3917](https://github.com/hiloopai/silmaril-lean/pull/3917) | [`dad8efe2562bfa71e9a3fe32255f95399b07c3da`](https://github.com/hiloopai/silmaril-lean/commit/dad8efe2562bfa71e9a3fe32255f95399b07c3da) | `1c54f6d9a71b4b8b9f75a6e9710ae69dc25854db` | [Lean](https://github.com/hiloopai/silmaril-lean/actions/runs/45778301833/job/139767857313) · [CI](https://github.com/hiloopai/silmaril-lean/actions/runs/45778301833/job/139768962971) · [Time budget](https://github.com/hiloopai/silmaril-lean/actions/runs/45778301833/job/139769266868) |
| [E snapshot concurrency #3919](https://github.com/hiloopai/silmaril-lean/pull/3919) | [`ab1f795428f0e4fffbe44b14a1fd19368e607d7c`](https://github.com/hiloopai/silmaril-lean/commit/ab1f795428f0e4fffbe44b14a1fd19368e607d7c) | `fff5e49cb18b03fbc5b9c032119891b0a2c1173a` | [Lean](https://github.com/hiloopai/silmaril-lean/actions/runs/45779536656/job/139771942499) · [CI](https://github.com/hiloopai/silmaril-lean/actions/runs/45779536656/job/139772736189) · [Time budget](https://github.com/hiloopai/silmaril-lean/actions/runs/45779536656/job/139772818922) |
| [E public integration #3946](https://github.com/hiloopai/silmaril-lean/pull/3946) | [`0a8dd601d199fb46586759cab4189a234481f36c`](https://github.com/hiloopai/silmaril-lean/commit/0a8dd601d199fb46586759cab4189a234481f36c) | `b76b97b1c44f32d6fa6cd9850dda49c85a7542c7` | [Lean](https://github.com/hiloopai/silmaril-lean/actions/runs/45780986692/job/139776372544) · [CI](https://github.com/hiloopai/silmaril-lean/actions/runs/45780986692/job/139777300424) · [Time budget](https://github.com/hiloopai/silmaril-lean/actions/runs/45780986692/job/139777626768) |

The #3946 PR run passed with 158.2 seconds counted against the 300-second
budget. The main-push run at its merge commit was canceled.
[Exact-head PR run](https://github.com/hiloopai/silmaril-lean/actions/runs/45780986692) ·
[Canceled main-push run](https://github.com/hiloopai/silmaril-lean/actions/runs/45781700663)
