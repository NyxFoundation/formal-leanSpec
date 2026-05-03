---
title: leanSpec → Lean4 定理証明 命題リスト
last_updated: 2026-05-03
tags:
  - lean4
  - formal-verification
  - propositions
  - safety
  - consensus
---

# leanSpec → Lean4 定理証明 命題リスト

## Context

leanSpec は Lean Ethereum コンセンサスの Python 仕様。
クライアント実装の安全性を担保するため、仕様レベルで成立すべき**命題**を抽出し、Lean4 でこれを定理証明する。

- **目的**: 安全なクライアント仕様の設計
- **方針**: 関数単位の入出力命題から始め、領域横断の不変量へ広げる
- **本文書の役割**: Lean4 化する命題のカタログ
    - 命題のタイトル自体を述語形 (「〜である / 〜になる / 〜する」) で書き、本文は Lean4 サンプルコードを軸にする
    - **領域別** (Lean4 ディレクトリ構成と 1:1 対応) で分類
    - 対象は 8 領域: SSZ・基本型 / Containers / State Transition / Fork Choice / Validator / Networking / Storage / Sync
    - **対象外**: 暗号プリミティブ・KoalaBear 体・XMSS 署名スキームの代数的性質は **Arklib** 側で扱う。本文書では呼び出し側 (e.g. SSZ-7 の `axiom` 化、VAL-5 の鍵準備状態管理) のみカバー。

## アプローチ

### 各命題の項目

命題の主張は **見出し (`### <ID>: ...`) のタイトル文** が述語形でそのまま述べる。各命題ブロックは以下の項目で構成される (出現順)。`出典` / `補足` は省略可、`サンプルコード` は基本的に必須。

- **出典**: 命題の根拠となる leanSpec (Python) の関数名 / 型名 (例: `process_slots`、`Uint64.encode`、`Database.batch_write`)。命題が「Python 仕様のどの挙動を抜き出したものか」を追跡可能にする。1 関数に局所化できない cross-cutting な性質では主要関数 + 注釈 (例: `state_transition` (任意回適用したグローバル不変量)) で示す。
- **補足**: `出典` が指す関数の役割を自然言語で 1 行説明する。関数名だけでは何をする関数か読み取れないため (例: `is_justifiable_after` だけ見ても何の判定か不明) に付ける。`encode`/`decode` のような自明な関数では省略する。
- **サンプルコード**: Lean4 で書いた命題の stub。証明本体は `sorry` で保留:

  ```lean
  -- 命題の Lean4 stub。証明本体は `sorry` で保留。
  theorem foo (s : State) : P s := by sorry
  ```

  実コードでは `Std`, `Mathlib` または独自 `LeanSpec.Prelude` への依存になる想定。SSZ・State・Block 等の型は別ファイル (`LeanSpec.Containers.*`) で別途定義する。

### 命題 ID 規約

`<DOMAIN>-<番号>` の形式。`DOMAIN` は所属する領域の略号:

| Prefix | 領域 | Lean4 配置 |
|---|---|---|
| `SSZ` | SSZ・基本型 | `LeanSpec/Types`, `LeanSpec/SSZ` |
| `CONT` | コンテナ (Checkpoint, Slot algebra 等) | `LeanSpec/Containers` |
| `ST` | State transition | `LeanSpec/Forks/Lstar/State` |
| `FC` | Fork choice | `LeanSpec/Forks/Lstar/Store` |
| `VAL` | Validator duties | `LeanSpec/Validator` |
| `NET` | Networking (req/resp) | `LeanSpec/Networking` |
| `STOR` | Storage | `LeanSpec/Storage` |
| `SYNC` | Sync FSM | `LeanSpec/Sync` |

## SSZ・基本型

**SSZ (Simple Serialize)** は Ethereum コンセンサスレイヤーで使う決定論的シリアライゼーション形式。各値は (1) バイト列への encode、(2) Merkle 化による `hash_tree_root` (32 バイトのコミットメント) の 2 通りで一意に表現される。基本型は `Boolean`, `Uint{8,16,32,64}`, 固定長 `Bytes32`, 可変長 `List`, 固定長 `Vector`, ビット列 `Bitlist/Bitvector`。

ここでの命題は **エンコーダの数学的健全性** を保証する: round-trip (`decode ∘ encode = id`)、長さ不変量 (固定長型は常に N バイトで encode される)、範囲制約 (`Uint64` の値が `[0, 2^64)` に収まる) など。これらが崩れると、上位層 (Container, hash_tree_root, fork choice の入力) が全て信頼できなくなる。実装は `LeanSpec/Types/*`, `LeanSpec/SSZ/*`。

### SSZ-1: Boolean はエンコード/デコードで元に戻る

- 出典: `Boolean.encode` / `Boolean.decode`
- サンプルコード:

```lean
theorem boolean_roundtrip (b : Boolean) :
    Boolean.decode (Boolean.encode b) = some b := by sorry
```

### SSZ-2: Uint64 の値は [0, 2^64) に収まる

- 出典: `Uint64` (型定義)
- サンプルコード:

```lean
theorem uint64_range (v : Uint64) :
    v.toNat < 2 ^ 64 := by sorry
```

### SSZ-3: Uint64 は 8 バイト LE エンコード/デコードで元に戻る

- 出典: `Uint64.encode` / `Uint64.decode`
- サンプルコード:

```lean
theorem uint64_roundtrip (v : Uint64) :
    Uint64.decode (Uint64.encode v) = some v := by sorry

theorem uint64_encode_length (v : Uint64) :
    (Uint64.encode v).length = 8 := by sorry
```

### SSZ-4: Bytes32 は常に 32 バイトである

- 出典: `Bytes32` (型定義)
- サンプルコード:

```lean
theorem bytes32_length (bs : Bytes32) : bs.size = 32 := by sorry
```

### SSZ-5: SSZVector の長さは型パラメータ n に等しい

- 出典: `SSZVector` (型定義)
- サンプルコード:

```lean
theorem sszvector_length {T : Type} {n : Nat} (v : SSZVector T n) :
    v.data.length = n := by sorry
```

### SSZ-6: 2 の冪への切り上げは入力以上の最小値になる

- 出典: `get_power_of_two_ceil`
- 補足: `x` 以上の最小の 2 の冪を返す (Merkle 木のリーフ数を 2 冪に揃えるパディング計算で使う)
- サンプルコード:

```lean
theorem ceil_pow2_minimal (x : Nat) (h : 0 < x) :
    x ≤ ceilPow2 x ∧ ∃ k, ceilPow2 x = 2 ^ k ∧
      (k = 0 ∨ 2 ^ (k - 1) < x) := by sorry
```

### SSZ-7: Merkle root 計算は決定的である

- 出典: `hash_tree_root`
- サンプルコード:

```lean
axiom HashTreeRoot.collisionResistance :
    ∀ x y, hashTreeRoot x = hashTreeRoot y → x = y
-- 注: 厳密な定理ではなく、暗号学的仮定として使う
```

## コンテナ (Containers)

**Container** は SSZ の合成型で、名前付きフィールドを持つ構造体 (Solidity の `struct` 相当)。コンセンサスレイヤーの **on-chain / on-wire データ構造** はすべて Container として定義される: `Checkpoint` (root + slot のチェーン上のポインタ)、`BlockHeader`, `AttestationData`, `Attestation`, `AggregatedAttestation` 等。

特に `Checkpoint` は finality 機構の核 — fork choice は「どの checkpoint を justified / finalized とみなすか」で head を決定するため、Checkpoint 同士の **全順序** や、ある finalized から見て target が **justifiable な距離** (`δ ≤ 5`、`δ = k²`、`δ = k(k+1)` の disjunction) かが命題のターゲットになる。実装は `LeanSpec/Containers/*`。

### CONT-1: Checkpoint の順序は slot で決まる

- 出典: `Checkpoint` (比較演算)
- サンプルコード:

```lean
theorem checkpoint_lt_iff_slot_lt (c1 c2 : Checkpoint) :
    c1 < c2 ↔ c1.slot < c2.slot := by sorry
```

### CONT-2: justifiable は 3 種類の slot 距離のいずれかで成立する

- 出典: `is_justifiable_after`
- 補足: finalized checkpoint slot から見て target slot が justifiable な距離にあるかを判定 (LMD-CASPER の justification 候補性チェック)
- サンプルコード:

```lean
theorem justifiable_iff
    (finalized target : Slot) (h : finalized ≤ target) :
    Slot.isJustifiableAfter finalized target ↔
      let δ := target.toNat - finalized.toNat
      δ ≤ 5 ∨ (∃ k, δ = k * k) ∨ (∃ k, δ = k * (k + 1)) := by sorry
```

## State Transition

**State Transition Function (STF)** は「現在の `BeaconState` + 入力 `Block` → 次の `BeaconState`」を計算する純関数で、コンセンサスの中核。`process_slots` (slot を進める空遷移) と `process_block` (ブロック適用) の合成で表される。

ここでの命題は **STF が想定どおりに状態を前進させる** ことを保証する: `process_slots` 後に `state.slot` が target に達する、`process_block_header` 後に `latest_block_header.slot` がブロックの slot と一致する、justified/finalized の slot は遷移をまたいで単調非減少、`justified.slot ≥ finalized.slot` が常に成立する、最終的に **finalization は不可逆** (一度 finalize した checkpoint より古い slot に巻き戻ることはない) など。これらが崩れると、forking 攻撃や reorg の防御が破れる。実装は `LeanSpec/Forks/Lstar/State/*`。

### ST-1: 空 slot 進行で state.slot は target になる

- 出典: `process_slots`
- 補足: state を target slot まで空 (ブロックなし) で繰り返し前進させる
- サンプルコード:

```lean
theorem process_slots_advances (s : State) (target : Slot)
    (h : s.slot ≤ target) :
    (State.processSlots s target).slot = target := by sorry
```

### ST-2: ブロックヘッダ適用で最新ヘッダ slot はブロック slot と一致する

- 出典: `process_block_header`
- 補足: block のヘッダ部分を state に適用し `latest_block_header` を更新
- サンプルコード:

```lean
theorem process_block_header_slot
    (s : State) (b : Block) (s' : State)
    (h : State.processBlockHeader s b = .ok s') :
    s'.latestBlockHeader.slot = b.slot := by sorry
```

### ST-3: Checkpoint slot は遷移をまたいで単調非減少である

- 出典: `state_transition` (process 全般)
- 補足: `process_slots` と `process_block` の合成。1 ブロック分の状態遷移
- サンプルコード:

```lean
theorem checkpoint_monotone
    (s s' : State) (b : Block)
    (h : State.transition s b = .ok s') :
    s.latestJustified.slot ≤ s'.latestJustified.slot ∧
    s.latestFinalized.slot ≤ s'.latestFinalized.slot := by sorry
```

### ST-4: justified slot は常に finalized slot 以上である

- 出典: `process_justification_and_finalization` (および関連 process_*、複数関数で維持される reachable-state 不変量)
- サンプルコード:

```lean
theorem justified_ge_finalized (s : State) (hreach : Reachable s) :
    s.latestJustified.slot ≥ s.latestFinalized.slot := by sorry
```

### ST-5: 状態遷移関数は純関数である

- 出典: `state_transition` (シグネチャ全体に対するメタ性質)
- 補足: ST-3 と同じ状態遷移関数。同一引数なら必ず同一結果
- サンプルコード: `@[simp]` 補題として書く。

### ST-6: Finalization は不可逆である

- 出典: `state_transition` (任意回適用したグローバル不変量)
- 補足: ST-3 と同義の状態遷移関数
- サンプルコード:

```lean
theorem finalization_irreversible
    (s s' : State) (b : Block)
    (h : State.transition s b = .ok s') :
    s.latestFinalized.slot ≤ s'.latestFinalized.slot := by sorry
```

## Fork Choice

**Fork choice** は複数の有効ブロック候補がある時、どの枝が canonical chain かを決めるアルゴリズム。Lean Ethereum (lstar) では **LMD-GHOST** ベース: 最新の attestation の重みを集計し、justified checkpoint から下流で最も重い枝を head とする。`Store` は fork choice の入力を保持する状態 — ブロック集合、attestation キャッシュ、最新の justified/finalized checkpoint。

ここでの命題は **fork choice の整合性** を保証する: `compute_head` は同じ Store に対し決定的、選ばれた head は必ず latest_justified の子孫、attestation の `source.slot ≤ target.slot ≤ head.slot` という topological 制約、ブロック関係グラフは acyclic (`parent_root` の連鎖に循環なし)、ブロック生成ループは有限ステップで停止する、など。これらが崩れると head が不定になり、ネットワークが split する。実装は `LeanSpec/Forks/Lstar/Store/*`。

### FC-1: head 選択は決定的である (純関数)

- 出典: `compute_head`
- 補足: Store から LMD-GHOST で canonical head の root を計算
- サンプルコード:

```lean
theorem compute_head_deterministic (st : Store) :
    Store.computeHead st = Store.computeHead st := by rfl
-- 実質的には: 純関数として well-formed であることを証明する別 lemma に展開
```

### FC-2: head は最新の justified checkpoint の子孫である

- 出典: `compute_head` (派生性質、FC-1 と同関数)
- 補足: head が justified の子孫であることを `isAncestorOrEqual` (a が b の祖先または同一かを判定する補助関数) で確認する
- サンプルコード:

```lean
theorem head_descends_from_justified (st : Store) (h : Bytes32)
    (hh : Store.computeHead st = h) :
    Store.isAncestorOrEqual st st.latestJustified.root h := by sorry
```

### FC-3: Attestation の source/target/head は slot 順に並ぶ

- 出典: `validate_attestation`
- 補足: attestation の整合性 (slot 順序、参照ブロックの存在等) を検証
- サンプルコード:

```lean
theorem attestation_topology
    (st : Store) (att : Attestation)
    (h : Store.validateAttestation st att = .ok) :
    att.data.source.slot ≤ att.data.target.slot ∧
    att.data.target.slot ≤ att.data.head.slot := by sorry
```

### FC-4: Fork choice tree は acyclic である

- 出典: `Database.add_block` / `parent_root` 規約 (block 挿入時から生じる構造的不変量)
- 補足: 「a が b の真の祖先 (≠ b 自身) か」を判定する `isProperAncestor` を使い、「自分が自分の真の祖先になる」ことを否定して acyclicity を表現する
- サンプルコード:

```lean
theorem fork_choice_acyclic (st : Store) (hwf : Store.WellFormed st) :
    ∀ b ∈ st.blocks.values, ¬ Store.isProperAncestor st b.root b.root := by sorry
```

### FC-5: Fixed-point block building loop は有限ステップで停止する

- 出典: `produce_block_with_signatures`
- 補足: 新ブロック生成の fixed-point ループ (justified slot が更新されなくなるまで反復)
- サンプルコード: WellFoundedRecursion で表現。難度高。

## Validator

**Validator** は ETH をステークしてコンセンサスに参加する主体。各スロットで割り当てられた **duty** を実行する: (1) `proposer` に選ばれたら新ブロックを提案、(2) `attester` として現在の head に投票。Validator service はローカルで自分の鍵 (proposal key と attestation key の dual-key 構成) と署名済み履歴を管理する。

ここでの命題は **duty の正当性と slashing 防止** を保証する: proposer の選出は `slot mod n` の round-robin で各スロットにちょうど 1 人、proposal key と attestation key は別物 (鍵漏洩時の影響を局所化)、同じ slot で 2 回 attest しない (二重投票 = slashable)、XMSS の状態付き署名鍵は使用済み index を逆戻りしない (鍵再利用は秘密鍵漏洩につながる)、など。これらは validator が罰金を食らわず、かつネットワークが安全に進むための条件。実装は `LeanSpec/Validator/*`。

### VAL-1: proposer は round-robin で選出される

- 出典: `proposer_index` (in `process_block_header`)
- 補足: slot と active validator 数 n から、その slot の proposer index を返す (round-robin)
- サンプルコード:

```lean
theorem proposer_index_round_robin (slot : Slot) (n : Nat) (h : 0 < n) :
    ValidatorIndex.proposerFor slot n = ValidatorIndex.mk (slot.toNat % n) := by sorry
```

### VAL-2: proposal key と attestation key は別物である

- 出典: `proposalKey` / `attestationKey` (ValidatorService)
- 補足: validator ごとに block proposal 用と attestation 用の 2 種類の署名鍵を別々に管理する
- サンプルコード:

```lean
theorem dual_key_distinct (vid : ValidatorIndex) (reg : KeyRegistry) :
    reg.proposalKey vid ≠ reg.attestationKey vid := by sorry
```

### VAL-3: 各 slot の提案者はちょうど 1 人である

- 出典: `is_proposer` / `proposer_index` (ValidatorService)
- 補足: validator vid が slot の proposer かを判定 (`vid = slot mod n` と等価)
- サンプルコード:

```lean
theorem unique_proposer (slot : Slot) (n : Nat) (h : 0 < n) :
    ∃! vid : Fin n, ValidatorIndex.isProposerFor vid slot := by sorry
```

### VAL-4: 同一 slot で二重投票はできない

- 出典: `ValidatorService.produce_attestation`
- 補足: ローカル履歴で「該当 slot に既に attest 済みか」を判定し、未投票なら新規 attestation を生成 (二重投票になる場合は失敗)
- サンプルコード:

```lean
theorem no_double_vote
    (svc svc' : ValidatorService) (vid : ValidatorIndex) (slot : Slot)
    (hin : slot ∈ svc.attestedSlots vid)
    (h : ValidatorService.produceAttestation svc vid slot = .ok svc') :
    False := by sorry
```

### VAL-5: XMSS 準備状態は単調増加する

- 出典: `XMSS.advance_preparation` (ValidatorService から呼出)
- 補足: XMSS 秘密鍵の prepared 状態 (使用可能な one-time key 範囲) を 1 ステップ進める。`preparedEnd` は現在準備済みの最後の index
- サンプルコード:

```lean
theorem xmss_advance_monotone (sk : XMSSSecretKey) :
    sk.preparedEnd < (XMSS.advancePreparation sk).preparedEnd := by sorry
```

## Networking

**Networking** はピア間の通信プロトコル。2 系統ある: (1) **req/resp** — `BlocksByRange`, `BlocksByRoot`, `Status` 等の同期型 1 対 1 RPC、(2) **gossipsub** — `beacon_block`, `beacon_attestation` 等の publish/subscribe メッセージ伝搬。両方とも libp2p の上に乗る。

ここでの命題は **DoS 耐性のための境界値** を保証する: `BlocksByRange` の応答は要求された `count` と `MAX_REQUEST_BLOCKS` のうち小さい方を超えない、デコード可能なペイロードは `MAX_PAYLOAD_SIZE` 以下、など。これらが崩れると、悪意あるピアが巨大ペイロードや無限長応答を送り込んで node のメモリ/CPU を枯渇させられる。実装は `LeanSpec/Networking/*`。

### NET-1: BlocksByRange 応答長は上限を超えない

- 出典: `Handler.handle` (BlocksByRange)
- 補足: `BlocksByRange` リクエストを受信し block 列で応答する req/resp ハンドラ
- サンプルコード:

```lean
theorem blocks_by_range_bounded
    (req : BlocksByRangeRequest) (resp : List Block)
    (h : Handler.handle req = .ok resp) :
    resp.length ≤ min req.count MAX_REQUEST_BLOCKS := by sorry
```

### NET-2: デコード可能なペイロードサイズは上限以下である

- 出典: `Codec.decode`
- 補足: req/resp プロトコル上のメッセージペイロードを SSZ デコードして Message 型に変換
- サンプルコード:

```lean
theorem payload_size_bound (payload : ByteArray) (msg : Message)
    (h : Codec.decode payload = .ok msg) :
    payload.size ≤ MAX_PAYLOAD_SIZE := by sorry
```

## Storage

**Storage** は永続化レイヤー — ブロック、state、checkpoint をディスクに保存し、再起動後の復元やプルーニングを担当する。実装上は KV ストア (LevelDB / RocksDB 系) を抽象化した `Database` インタフェース上で、`block_root → Block`、`state_root → BeaconState` のマッピングを管理する。

ここでの命題は **チェーン構造の整合性と書き込みの原子性** を保証する: store に存在するブロックは genesis を除き必ず親もまた store に存在する (孤立ブロック禁止、fork choice の前提)、`batch_write` は全件成功するか全件失敗するかの 2 状態のみ (中途半端な永続化で state と block の参照が食い違わない)、など。これらが崩れると、再起動後に Store が壊れ、fork choice が回らなくなる。実装は `LeanSpec/Storage/*`。

### STOR-1: genesis 以外の Block は親が store に存在する

- 出典: `Database.add_block` (親存在前提)
- 補足: store 上の各 block は親 block root (`parent_root`) を持ち、genesis 以外は親が `store.blocks` (`block_root → Block` マップ) に存在する必要がある
- サンプルコード:

```lean
theorem parent_exists_or_genesis
    (st : Store) (b : Block)
    (hin : b ∈ st.blocks.values) :
    b.parentRoot = ByteArray.zeroes 32 ∨
    st.blocks.contains b.parentRoot := by sorry
```

### STOR-2: バッチ書き込みは原子的である

- 出典: `Database.batch_write`
- 補足: 複数の書き込みを 1 トランザクションで適用 (全成功 or 全失敗の atomic 保証)
- サンプルコード (高水準モデル化):

```lean
theorem batch_atomic
    (db db' : Database) (ws : List Write) :
    Database.batchWrite db ws = .ok db' →
    (∀ w ∈ ws, db'.contains w) ∨ db' = db := by sorry
```

## Sync

**Sync** は node がネットワークの最新 head に追いつくまでのプロセスを管理する有限状態機械 (FSM)。3 状態: `IDLE` (起動直後・停止中、ブロックを処理しない)、`SYNCING` (head から大きく遅れており req/resp で range 取得中)、`SYNCED` (head に追いつき gossip でリアルタイム受信中)。許可される遷移は 4 種類のみ: `IDLE → SYNCING`、`SYNCING → SYNCED`、`SYNCED → SYNCING` (再び遅れた)、任意の状態 → `IDLE` (shutdown / fatal)。

ここでの命題は **FSM の閉性と gossip の gating** を保証する: 実装の `transition` 関数は許可された 4 遷移以外を生成しない、`acceptsGossip ⇔ st ∈ {SYNCING, SYNCED}` (IDLE 中に gossip を受け付けると古い/壊れた payload を再 forward してネットワークを汚染する)、など。実装は `LeanSpec/Sync/*`。

### SYNC-1: sync FSM の遷移は許可された 4 種類のみである

- 出典: `SyncService.transition`
- 補足: sync FSM の現状態から次状態を計算 (許可された 4 遷移のいずれか、または `none`)
- サンプルコード:

```lean
inductive SyncState | idle | syncing | synced
inductive SyncState.canTransitionTo : SyncState → SyncState → Prop
  | idle_to_syncing : canTransitionTo .idle .syncing
  | syncing_to_synced : canTransitionTo .syncing .synced
  | synced_to_syncing : canTransitionTo .synced .syncing
  | any_to_idle (s) : canTransitionTo s .idle

theorem transition_sound (s s' : SyncState)
    (h : SyncService.transition s = some s') :
    s.canTransitionTo s' := by sorry
```

### SYNC-2: Gossip は SYNCING/SYNCED 状態でのみ受け付けられる

- 出典: `SyncService.accepts_gossip`
- 補足: 現状態で gossipsub メッセージを受け付けるかを判定 (`SYNCING` または `SYNCED` のときのみ true)
- サンプルコード:

```lean
theorem accepts_gossip_iff (st : SyncState) :
    SyncService.acceptsGossip st ↔ st = .syncing ∨ st = .synced := by sorry
```

