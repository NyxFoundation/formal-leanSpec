/-
Key-value database and atomic batch writes.

Mirrors `src/lean_spec/node/storage/` in leanSpec:
  - `exceptions.py` — `StorageError` with read / write / corruption
    subclasses.
  - `database.py` — the `Database` protocol: namespaced key-value
    `put_* / get_*` pairs (blocks, states, checkpoints, indices), all
    writes grouped by `batch_write`, "one atomic transaction: commits
    on clean exit, rolls back on any exception".
  - `sqlite.py` — the deployed implementation: `batch_write` yields,
    then commits; every raise (storage errors, sqlite errors, anything)
    triggers `rollback` and re-raises.

The model is the protocol's key-value essence: a `Database` is an
association list over namespaced key bytes, one `Write` per `put_*`
call, and `batchWrite` folds a batch through a working copy — the
commit is returning the fully-written copy, and the rollback is the
error path returning no database at all, so the caller keeps its
pre-batch value untouched (pure-model rollback by construction).
Environmental write failures (`sqlite3.Error`) enter as the `writeOk`
parameter, so the theorems hold whatever the backend rejects.

Proves STOR-2 from `docs/lean4-proof-propositions.md`:
  - STOR-2: batch writes are atomic — a committed batch contains every
    write (`batch_write_commits`, for batches without key collisions;
    a later write to the same key overwrites, as in any store), giving
    the catalog's all-or-nothing disjunction (`batch_atomic`); a failed
    batch changes nothing, by construction of the pure model.
-/

namespace LeanSpec.Storage

/-- Storage failure classes (`exceptions.py`). -/
inductive StorageError where
  /-- Failed to read from storage (`StorageReadError`). -/
  | readError
  /-- Failed to write to storage (`StorageWriteError`). -/
  | writeError
  /-- Stored data is malformed (`StorageCorruptionError`). -/
  | corruptionError
  deriving Repr, DecidableEq, Inhabited

/-- Namespaced key bytes (the `Database` protocol keys its namespaces
by root / slot / fixed tags, uniformly bytes here). -/
abbrev Key := List UInt8

/-- One write in a batch: a `put_*` call, uniformly a key-value pair. -/
structure Write where
  key : Key
  value : List UInt8
  deriving Repr, Inhabited

/-- The key-value essence of the `Database` protocol: an association
list, newest entry first. -/
abbrev Database := List Write

namespace Database

/-- Store a value under a key, replacing any existing entry
(the `put_*` family). -/
def put (db : Database) (w : Write) : Database :=
  w :: db.filter (fun e => !(e.key == w.key))

/-- Retrieve the value under a key, or `none` (the `get_*` family). -/
def get? (db : Database) (k : Key) : Option (List UInt8) :=
  (db.find? (fun e => e.key == k)).map (·.value)

/-- The database holds exactly this write. -/
def contains (db : Database) (w : Write) : Prop :=
  db.get? w.key = some w.value

/-- Group writes into one atomic transaction (`batch_write`): the batch
folds through a working copy, committing by returning the fully-written
copy. A rejected write (`writeOk` false — the backend's
`sqlite3.Error`) aborts with `StorageWriteError`; the caller's database
is untouched on that path by construction, which is the pure-model
rollback. -/
def batchWrite (writeOk : Write → Bool) :
    Database → List Write → Except StorageError Database
  | db, [] => .ok db
  | db, w :: rest =>
    if writeOk w then batchWrite writeOk (db.put w) rest
    else .error .writeError

/-- A lookup at a key another entry was filtered around is unchanged. -/
private theorem find?_filter_ne (wkey k : Key) (hne : k ≠ wkey) :
    ∀ (l : List Write),
    ((l.filter (fun e => !(e.key == wkey))).find? (fun e => e.key == k))
      = l.find? (fun e => e.key == k)
  | [] => rfl
  | e :: t => by
    by_cases hek : (e.key == k) = true
    · have her : (e.key == wkey) = false := by
        have : e.key = k := eq_of_beq hek
        subst this
        exact beq_eq_false_iff_ne.mpr hne
      rw [List.filter_cons_of_pos (by simp [her])]
      rw [List.find?, List.find?]
      simp [hek]
    · by_cases her : (e.key == wkey) = true
      · rw [List.filter_cons_of_neg (by simp [her])]
        rw [List.find?]
        simp only [hek]
        exact find?_filter_ne wkey k hne t
      · rw [List.filter_cons_of_pos (by simp [her])]
        rw [List.find?, List.find?]
        simp only [hek]
        exact find?_filter_ne wkey k hne t

/-- A put answers for its own key. -/
theorem get?_put_self (db : Database) (w : Write) :
    (db.put w).get? w.key = some w.value := by
  unfold put get?
  rw [List.find?]
  simp

/-- A put leaves every other key unchanged. -/
theorem get?_put_ne (db : Database) (w : Write) (k : Key)
    (hne : k ≠ w.key) :
    (db.put w).get? k = db.get? k := by
  unfold put get?
  rw [List.find?]
  have : (w.key == k) = false := by
    exact beq_eq_false_iff_ne.mpr fun hc => hne hc.symm
  simp only [this]
  rw [find?_filter_ne w.key k hne db]

/-- A batch never touches a key none of its writes name. -/
private theorem batchWrite_get?_preserved (writeOk : Write → Bool)
    (k : Key) :
    ∀ (ws : List Write) (db db' : Database),
    (∀ w ∈ ws, w.key ≠ k) →
    batchWrite writeOk db ws = .ok db' →
    db'.get? k = db.get? k
  | [], db, db', _, h => by
    injection h with h'
    rw [h']
  | w :: rest, db, db', hk, h => by
    rw [batchWrite] at h
    split at h
    · have hrest := batchWrite_get?_preserved writeOk k rest (db.put w) db'
        (fun w' hw' => hk w' (List.mem_cons_of_mem w hw')) h
      rw [hrest]
      exact get?_put_ne db w k
        (fun hc => hk w List.mem_cons_self hc.symm)
    · simp at h

/-- STOR-2: a committed batch contains every one of its writes — for a
batch without key collisions (a later write to the same key overwrites,
as in any key-value store). -/
theorem batch_write_commits (writeOk : Write → Bool) :
    ∀ (ws : List Write) (db db' : Database),
    (ws.map (·.key)).Nodup →
    batchWrite writeOk db ws = .ok db' →
    ∀ w ∈ ws, db'.contains w
  | [], _, _, _, _, w, hw => absurd hw (List.not_mem_nil)
  | w :: rest, db, db', hnodup, h, w', hw' => by
    rw [List.map_cons] at hnodup
    have hnd := List.nodup_cons.mp hnodup
    rw [batchWrite] at h
    split at h
    · cases List.mem_cons.mp hw' with
      | inl heq =>
        subst heq
        have hpres := batchWrite_get?_preserved writeOk w'.key rest
          (db.put w') db'
          (fun r hr hc => hnd.1 (hc ▸ List.mem_map.mpr ⟨r, hr, rfl⟩)) h
        unfold contains
        rw [hpres]
        exact get?_put_self db w'
      | inr hmem =>
        exact batch_write_commits writeOk rest (db.put w) db' hnd.2 h w' hmem
    · simp at h

/-- STOR-2, catalog form: a batch is all-or-nothing — on commit every
write is contained (the failure branch never returns a database, so
"nothing" is the caller's untouched value). -/
theorem batch_atomic (writeOk : Write → Bool)
    (db db' : Database) (ws : List Write)
    (hnodup : (ws.map (·.key)).Nodup)
    (h : batchWrite writeOk db ws = .ok db') :
    (∀ w ∈ ws, db'.contains w) ∨ db' = db :=
  .inl (batch_write_commits writeOk ws db db' hnodup h)

end Database
end LeanSpec.Storage
