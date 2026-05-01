# leanSpec-lean4

Lean4 formal verification of the [leanSpec](https://github.com/leanEthereum/leanSpec) Ethereum
consensus specification.

## Goal

Catalog and prove propositions extracted from leanSpec to support safe client specification design.

## Structure (planned)

```text
LeanSpec/
  Prelude.lean
  SSZ/
  Forks/Lstar/
  Validator/
  Networking/
  Sync/
  Storage/
docs/
  lean4-proof-propositions.md   # Tier 1/2/3 proposition catalog
lakefile.lean
lean-toolchain
```

See `docs/lean4-proof-propositions.md` for the proposition catalog.
