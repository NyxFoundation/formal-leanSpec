# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project

Lean 4 formalization of the [leanSpec](https://github.com/leanEthereum/leanSpec) Ethereum consensus specification. Each Lean file extracts propositions from the Python spec and proves them as theorems, ID-tagged against `docs/lean4-proof-propositions.md`.

## Toolchain

- Lean version is pinned in `lean-toolchain` (`leanprover/lean4:v4.29.1`). `elan` will install/select it automatically — do not edit unless intentionally bumping.
- Build system is **Lake** (configured via `lakefile.toml`, not `lakefile.lean`). Single library target `LeanSpec`.

## Commands

```bash
lake build              # build the LeanSpec library (default target)
lake build LeanSpec     # explicit
lake clean              # remove .lake/build artifacts
lake env lean LeanSpec/SSZ/Boolean.lean   # type-check a single file
```

There is no test runner — every `theorem` whose proof type-checks is a passing "test". A successful `lake build` is the proof of correctness for the whole catalog.

## Architecture

The repository is organized around the **proposition catalog** in `docs/lean4-proof-propositions.md`. That file is the source of truth for what needs to be proved; the `LeanSpec/` tree is the proof.

- **Catalog → code mapping.** Each proposition has an ID like `SSZ-1`, `CONT-2`, `ST-3`. The ID prefix maps to a subdirectory:

  | Prefix | Domain | Lean location |
  |---|---|---|
  | `SSZ` | SSZ & primitive types | `LeanSpec/SSZ/` (and `LeanSpec/Types/` when added) |
  | `CONT` | Containers | `LeanSpec/Containers/` |
  | `ST` | State transition | `LeanSpec/Forks/Lstar/State/` |
  | `FC` | Fork choice | `LeanSpec/Forks/Lstar/Store/` |
  | `VAL` | Validator | `LeanSpec/Validator/` |
  | `NET` | Networking | `LeanSpec/Networking/` |
  | `STOR` | Storage | `LeanSpec/Storage/` |
  | `SYNC` | Sync FSM | `LeanSpec/Sync/` |

- **One type/concept per file.** `LeanSpec/SSZ/Boolean.lean` defines `Boolean` (≈ `Bool`) plus its `encode`, `decode`, and the corresponding theorems. `Bytes32.lean` defines the subtype carrying the 32-byte invariant. Files are aggregated into `LeanSpec.lean` at the root, which is what `lake build` compiles.

- **Every file mirrors a Python source.** Each `.lean` file's header docstring cites the corresponding file in `leanSpec` (e.g. `src/lean_spec/types/boolean.py`) and the proposition IDs it discharges. Keep this trace intact — it is how reviewers verify the Lean model matches the Python spec.

- **Cryptographic primitives are out of scope.** Field algebra, KoalaBear, and XMSS live in Arklib. In this repo they appear only as call-site assumptions (e.g. SSZ-7's `hash_tree_root` collision-resistance is modeled as an `axiom`, not a theorem).

## When adding a new proposition

1. Look up the ID in `docs/lean4-proof-propositions.md` and read the heading, `Source`, and `Note`.
2. Cite the Python source file and the proposition ID in the Lean file's leading docstring.
3. Stay close to the catalog's `Sample code` — use the same theorem name when reasonable so the catalog and the proof line up.
4. After proving, you may update the catalog entry's sample code with a `-- ✅ proved in ...` annotation (see `SSZ-4` in the catalog for the pattern). Bump the file's `last_updated` frontmatter date when you do.

## Conventions

- Commits scope by domain: `feat(ssz): prove SSZ-N <summary>` (see `git log`). One proposition per PR is the established cadence.
- Files under `docs/` require YAML frontmatter (`title`, `last_updated`, `tags`) — enforced by the user's global rules. `docs/generated/` and `docs/vendor/` are exempt but neither exists yet.
- Mirror leanSpec naming: `snake_case` Python identifier → `camelCase` Lean identifier (`process_block_header` → `processBlockHeader`, `is_justifiable_after` → `isJustifiableAfter`).
