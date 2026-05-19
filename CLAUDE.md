# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project purpose

Lean 4 formal verification of [`leanEthereum/leanSpec`](https://github.com/leanEthereum/leanSpec) (the Python Ethereum consensus specification). Each Lean module is a port of a specific Python file under `src/lean_spec/`, and the goal is to prove safety propositions about it (`docs/lean4-proof-propositions.md` is the prioritized catalog: Tier 1 = round-trip / range laws, Tier 2 = state-transition invariants, Tier 3 = global safety + cryptographic axioms).

When porting or proving, the file header comment names the Python source (e.g. `Mirrors src/lean_spec/types/boolean.py`). Treat that path as the spec; the Lean version must match its behavior.

## Build and test

Toolchain is pinned in `lean-toolchain` (Lean 4.29.0). Lake reads `lakefile.toml`.

```bash
lake build              # build the LeanSpec library (default target)
lake build Tests        # build the test library
lake exe Test           # run all unit tests; exits non-zero on failure
lake build LeanSpec.Theorems.Uint   # typecheck a single module
```

The `Test` exe runs each test group's `runAll : IO UInt32`, summing failure counts (see `Tests/Main.lean`). Add a new test group by importing it in `Tests/Main.lean` and accumulating its `runAll` into `rc`. NIST/spec test vectors go inline as `def expected... : String` literals (see `Tests/Unit/Sha256Test.lean` for the pattern).

`lakefile.toml` also declares `FixtureCheck` and `AxiomAudit` executables whose source files do not yet exist — `lake exe FixtureCheck` / `lake exe AxiomAudit` will fail until `Tests/FixtureCheck.lean` and `Audits/AxiomAudit.lean` are written. The `Audits/` directory is currently empty.

## Architecture

Layered, bottom-up. Higher layers import lower:

1. `LeanSpec/Crypto/` — SHA-256 (pure Lean, FIPS 180-4, no deps).
2. `LeanSpec/Codec/Endian.lean` — little-endian byte pushers/readers used by every fixed-width encoder.
3. `LeanSpec/Types/Base.lean` — defines `SSZError`, `SSZ.Result`, and the `SSZType` class. **Every encoded type implements `SSZType`** with `isFixedSize`, `fixedByteLength`, `serialize : T → ByteArray → ByteArray` (builder style — appends to an accumulator), and `deserialize : ByteArray → off → sz → SSZ.Result T`.
4. `LeanSpec/Types/{Uint,Boolean,ByteArray,Bitfield,Collection}.lean` — SSZ scalar and collection types.
5. `LeanSpec/SSZ/` — Merkleization, packing, `HasHashTreeRoot` class, constants. The Python `singledispatch` on `hash_tree_root` is replaced by a per-type `HasHashTreeRoot` instance.
6. `LeanSpec/Aliases.lean` — `Slot`, `ValidatorIndex`, `Root`, `AggregationBits` as `abbrev`s over the underlying primitives. **Use `abbrev`, not wrapper structs**, so the upstream `SSZType` instance is reused without re-derivation.
7. `LeanSpec/Containers/` — consensus containers (`Checkpoint`, `Attestation`, `BlockHeader`, …). Composite `SSZType` instances delegate to field-level `SSZType.serialize` / `deserialize`.
8. `LeanSpec/Theorems/` — proved propositions about the layers below. Standard pair per scalar: `length_law` (encoded size = `fixedByteLength`) and `encode_decode` (round-trip). Proofs use `Init` only; **no Mathlib, no `sorry`, no unauthorized `axiom`** in committed theorems.

`LeanSpec.lean` is the umbrella import — add new modules there to expose them as part of the library's public surface.

### Design conventions specific to this port

- **Pure functional decode.** Python's stream-based `deserialize(stream, scope)` is replaced by `(bs : ByteArray) (off sz : Nat)` slicing — explicit offset arithmetic is easier to reason about inductively.
- **Builder-style serialize.** `serialize x out` *appends* to `out` rather than returning fresh bytes, which keeps offset-table construction in variable-size containers straightforward.
- **`SSZError` is structured.** Each constructor carries the data needed for a useful diagnostic — when adding a new failure mode, add a constructor rather than collapsing into `malformed msg`.
- **Uint256 is intentionally absent** as a first-class type; the only consumer (mix-in length/selector) builds it ad hoc from `Nat`.

## Working with the proposition catalog

`docs/lean4-proof-propositions.md` is the source of truth for what to prove next. Each proposition has: Python source path, natural-language statement, semi-formal `∀/⇒` form, and a Lean 4 `theorem ... := by sorry` skeleton. When implementing one:

1. Place the proof in `LeanSpec/Theorems/<Area>.lean` (create the file if needed; mirror the directory structure of the type being proved about).
2. Update the catalog entry: replace the `sorry` skeleton with a link to the proved theorem, or annotate "✅ proved in `<file>`".
3. The catalog is a `docs/` markdown file — it must keep its YAML frontmatter and bump `last_updated` on any non-whitespace edit.

## Documentation

Markdown files under `docs/` (recursive, except `docs/generated/` and `docs/vendor/`) require YAML frontmatter with `title`, `last_updated: YYYY-MM-DD`, and `tags`. See `docs/lean4-proof-propositions.md` for the canonical example.
