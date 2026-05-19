/-
  leanSpec — Lean4 ネイティブな SSZ 型システム

  Python 版 leanSpec (https://github.com/paradigmxyz/leanSpec) の
  `src/lean_spec/types/` および `src/lean_spec/subspecs/ssz/` を
  Lean4 で再実装し、基礎定理 (Tier 1〜2) を証明する。

  公開 API はモジュール実装の進行に合わせて段階的に拡張する。
-/

import LeanSpec.Crypto.Sha256
import LeanSpec.Codec.Endian
import LeanSpec.Types.Base
import LeanSpec.Types.Uint
import LeanSpec.Types.Boolean
import LeanSpec.Types.ByteArray
import LeanSpec.Types.Bitfield
import LeanSpec.SSZ.Constants
import LeanSpec.SSZ.Utils
import LeanSpec.SSZ.Pack
import LeanSpec.SSZ.Merkleization
import LeanSpec.SSZ.Hash
import LeanSpec.Types.Collection
import LeanSpec.Aliases
import LeanSpec.Containers.Checkpoint
import LeanSpec.Containers.AttestationData
import LeanSpec.Containers.Attestation
import LeanSpec.Containers.AggregatedAttestation
import LeanSpec.Containers.BlockHeader
import LeanSpec.Theorems.Uint
import LeanSpec.Theorems.Boolean
