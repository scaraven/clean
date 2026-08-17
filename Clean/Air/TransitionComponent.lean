/-
Transition AIR tables: a component whose circuit is checked on each *adjacent pair* of rows.

Where a `Air.Flat.Table` checks its circuit independently on each row, a transition table checks it
on each pair `(rows[i], rows[i+1])`. Next-row access is expressed by *widening the environment*
rather than by extending `Expression`: the circuit is evaluated against the concatenation
`curr ++ next`, so that

    cell `i`              is `curr[i]`
    cell `rowWidth + i`   is `next[i]`

Since `Environment.fromArray` already reads a flat `Array F` by index, "next" is just an index
offset. This requires no changes to `Expression`, `Environment`, `eval`, or `circuit_norm`.

The component is the *same* `Air.Flat.Component` the flat kind uses -- a component says nothing
about how many rows its environment spans. Everything shared (the transport lemmas, the
trace-level predicates, interaction collection, `weakSoundness`) comes from `RowEnvs` in
`Clean/Air/Component.lean`. What lives here is only what is genuinely about row *pairs*.
-/
import Clean.Air.Component

namespace Air.Flat.Transition
variable {F : Type} [FiniteField F]
variable {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]

/--
Width of the environment a transition circuit is evaluated against: two rows side by side.

This is *not* the width of a trace row; use `Component.rowWidth` for that. Cells at index
`≥ 2 * rowWidth` are out of range and read as `0` under `Environment.fromArray`.

A transition component is the *same* `Air.Flat.Component` a flat table uses -- the row-pair reading
lives entirely in `Table` below -- so this is a definition about that shared structure rather than
a field of a separate one.
-/
def _root_.Air.Flat.Component.envWidth (component : Component F) : ℕ := 2 * component.rowWidth

@[circuit_norm] lemma _root_.Air.Flat.Component.envWidth_eq (component : Component F) :
  component.envWidth = 2 * component.rowWidth := rfl

/--
A concrete trace for one transition AIR component. Its data environment belongs to the ensemble.

`uniform_width` is stated with `component.rowWidth`, the width of a single row; the circuit's
environment spans twice that.
-/
structure Table (F : Type) [FiniteField F] where
  component : Component F
  table : List (Array F)
  uniform_width : ∀ row ∈ table, row.size = component.rowWidth
  /-- Connects the row-indexed fixed-column declaration to the concrete semantic rows. -/
  fixed_rows_match : component.fixedRowsMatch table := by
    simp [Component.fixedRowsMatch]

/--
The environment for the transition at a given position: the current row followed by the next row.

Cells `[0, rowWidth)` read `curr`, cells `[rowWidth, 2 * rowWidth)` read `next`.
-/
@[circuit_norm]
def pairEnv (curr next : Array F) (data : ProverData F) : Environment F :=
  Environment.fromArray (curr ++ next) data

namespace Table
variable {table : Table F} {data : ProverData F} {channel : RawChannel F}

/--
Adjacent row pairs, each tagged with the index of its *current* row.

The length is `table.length - 1`: a trace of 0 or 1 rows has no adjacent pairs and is therefore
entirely unconstrained, matching `TableOperation.everyRowExceptLast` semantics.

The index is carried explicitly rather than recovered from membership, because `FixedRowAt` and
`DataRowAt` are keyed on the current row's index.
-/
def pairs (t : Table F) : List (ℕ × Array F × Array F) :=
  (t.table.zip t.table.tail).zipIdx.map fun (p, i) => (i, p)

@[circuit_norm] lemma pairs_length (t : Table F) : t.pairs.length = t.table.length - 1 := by
  simp only [pairs, List.length_map, List.length_zipIdx, List.length_zip, List.length_tail]
  omega

/-- A one-row trace has no adjacent pairs, hence no constraints and no interactions. -/
@[circuit_norm] lemma pairs_eq_nil_of_length_le_one (t : Table F) (h : t.table.length ≤ 1) :
    t.pairs = [] := by
  rw [← List.length_eq_zero_iff, pairs_length]
  omega

/-- Membership in `pairs` exposes the index, and both rows, by indexing into `table`. -/
lemma mem_pairs_iff {t : Table F} {i : ℕ} {curr next : Array F} :
    (i, curr, next) ∈ t.pairs ↔
      ∃ (h : i + 1 < t.table.length), t.table[i] = curr ∧ t.table[i + 1] = next := by
  simp only [pairs, List.mem_map, List.mem_zipIdx_iff_getElem?, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro ⟨c, n, j, hj, rfl, rfl, rfl⟩
    rw [List.getElem?_eq_some_iff] at hj
    obtain ⟨hlt, heq⟩ := hj
    simp only [List.length_zip, List.length_tail, lt_inf_iff] at hlt
    have hi : j + 1 < t.table.length := by omega
    refine ⟨hi, ?_, ?_⟩
    · have := congrArg Prod.fst heq
      simp only [List.getElem_zip] at this
      exact this
    · have := congrArg Prod.snd heq
      simp only [List.getElem_zip, List.getElem_tail] at this
      exact this
  · rintro ⟨hi, rfl, rfl⟩
    refine ⟨t.table[i], t.table[i + 1], i, ?_, rfl, rfl, rfl⟩
    rw [List.getElem?_eq_some_iff]
    have hlt : i < (t.table.zip t.table.tail).length := by
      simp only [List.length_zip, List.length_tail, lt_inf_iff]
      omega
    exact ⟨hlt, by simp only [List.getElem_zip, List.getElem_tail]⟩

/-- The current row of any pair is a row of the trace. -/
lemma curr_mem_table {t : Table F} {i : ℕ} {curr next : Array F}
    (h : (i, curr, next) ∈ t.pairs) : curr ∈ t.table := by
  rw [mem_pairs_iff] at h
  obtain ⟨hi, rfl, _⟩ := h
  exact List.getElem_mem (by omega)

/-- The next row of any pair is a row of the trace. -/
lemma next_mem_table {t : Table F} {i : ℕ} {curr next : Array F}
    (h : (i, curr, next) ∈ t.pairs) : next ∈ t.table := by
  rw [mem_pairs_iff] at h
  obtain ⟨hi, _, rfl⟩ := h
  exact List.getElem_mem hi

/-- The index of a pair addresses its current row in the trace. -/
lemma getElem_of_mem_pairs {t : Table F} {i : ℕ} {curr next : Array F}
    (h : (i, curr, next) ∈ t.pairs) :
    ∃ hi : i < t.table.length, t.table[i] = curr := by
  rw [mem_pairs_iff] at h
  obtain ⟨hi, hcurr, _⟩ := h
  exact ⟨by omega, hcurr⟩

/-- A transition table is checked once per adjacent pair, against both rows laid side by side. -/
instance : RowEnvs F (Table F) where
  component table := table.component
  envs table data := table.pairs.map fun p => pairEnv p.2.1 p.2.2 data
  data_eq := by
    intro table data e he
    simp only [List.mem_map] at he
    obtain ⟨p, _, rfl⟩ := he
    rfl

@[circuit_norm] lemma envs_eq (table : Table F) (data : ProverData F) :
    RowEnvs.envs table data = table.pairs.map fun p => pairEnv p.2.1 p.2.2 data := rfl

@[circuit_norm] lemma component_eq (table : Table F) :
    RowEnvs.component (F:=F) table = table.component := rfl

/-- A pair of the trace is one of the environments the table is checked at. -/
lemma mem_envs_of_mem_pairs {p : ℕ × Array F × Array F} (hp : p ∈ table.pairs) :
    pairEnv p.2.1 p.2.2 data ∈ RowEnvs.envs (F:=F) table data := by
  simp only [envs_eq, List.mem_map]
  exact ⟨p, hp, rfl⟩

/-- `proverRows`, and hence `DataConsistency`, are keyed on the trace's rows, not on its pairs,
so that `deriveProverData` semantics are identical to the flat case. -/
def proverRows (table : Table F) (n : ℕ) : Array (Vector F n) :=
  table.component.proverRows table.table n

def DataConsistency (table : Table F) (data : ProverData F) : Prop :=
  table.component.DataConsistency table.table data

abbrev length (t : Table F) : ℕ := t.table.length

theorem ext_iff {table1 table2 : Table F} :
    table1 = table2 ↔
    table1.component = table2.component ∧
    table1.table = table2.table := by
  cases table1
  cases table2
  simp only [mk.injEq]

/-
Trace-level predicates and interaction collection are inherited from `RowEnvs`, exactly as for the
flat kind. As there, they are reducible `abbrev`s preserving the `Table.*` spellings.

Note the interaction counts differ from flat: a transition table of `n` rows emits interactions for
`n - 1` pairs, and a 0- or 1-row table emits nothing at all. Any bound on total interaction count
derived from table heights -- in particular the `< ringChar F` side condition carried by
`BalancedInteractions` -- must use `n - 1` for transition entries.
-/

abbrev channelsWithGuarantees (table : Table F) : List (RawChannel F) :=
  RowEnvs.channelsWithGuarantees (F:=F) table

abbrev channelsWithRequirements (table : Table F) : List (RawChannel F) :=
  RowEnvs.channelsWithRequirements (F:=F) table

@[circuit_norm] lemma channelsWithGuarantees_eq (table : Table F) :
  table.channelsWithGuarantees = table.component.circuit.channelsWithGuarantees := rfl

@[circuit_norm] lemma channelsWithRequirements_eq (table : Table F) :
  table.channelsWithRequirements = table.component.circuit.channelsWithRequirements := rfl

abbrev Constraints (table : Table F) (data : ProverData F) : Prop :=
  RowEnvs.Constraints (F:=F) table data

abbrev Assumptions (table : Table F) (data : ProverData F) : Prop :=
  RowEnvs.Assumptions (F:=F) table data

abbrev Guarantees (table : Table F) (data : ProverData F) : Prop :=
  RowEnvs.Guarantees (F:=F) table data

abbrev ChannelGuarantees (table : Table F) (data : ProverData F) (channel : RawChannel F) : Prop :=
  RowEnvs.ChannelGuarantees (F:=F) table data channel

abbrev InChannelsOrGuarantees (table : Table F) (data : ProverData F)
    (channels : List (RawChannel F)) : Prop :=
  RowEnvs.InChannelsOrGuarantees (F:=F) table data channels

abbrev Requirements (table : Table F) (data : ProverData F) : Prop :=
  RowEnvs.Requirements (F:=F) table data

abbrev ChannelRequirements (table : Table F) (data : ProverData F) (channel : RawChannel F) : Prop :=
  RowEnvs.ChannelRequirements (F:=F) table data channel

abbrev InChannelsOrRequirements (table : Table F) (data : ProverData F)
    (channels : List (RawChannel F)) : Prop :=
  RowEnvs.InChannelsOrRequirements (F:=F) table data channels

abbrev Spec (table : Table F) (data : ProverData F) : Prop :=
  RowEnvs.Spec (F:=F) table data

abbrev interactions (table : Table F) (data : ProverData F) : List (Interaction F) :=
  RowEnvs.interactions (F:=F) table data

noncomputable abbrev interactionsWith (table : Table F) (data : ProverData F)
    (channel : RawChannel F) : List (Interaction F) :=
  RowEnvs.interactionsWith (F:=F) table data channel

noncomputable abbrev interactionssWith (table : Table F) (data : ProverData F)
    (channel : RawChannel F) : List (List (Interaction F)) :=
  RowEnvs.interactionssWith (F:=F) table data channel

/--
The current row's input cells are read identically from the row alone and from the row pair,
because they occupy the low `size Input` indices and `size Input ≤ rowWidth`.

This is the one genuinely new fact the transition kind needs: it is what lets the fixed-row and
derived-data machinery, all of which is stated about a single row, apply unchanged to a pair.
-/
lemma valueFromOffset_pairEnv {t : Table F} {i : ℕ} {curr next : Array F}
    (hmem : (i, curr, next) ∈ t.pairs) (data : ProverData F) :
    valueFromOffset t.component.Input 0 (pairEnv curr next data) =
      valueFromOffset t.component.Input 0 (Environment.fromArray curr data) := by
  have hsize : curr.size = t.component.rowWidth :=
    t.uniform_width curr (curr_mem_table hmem)
  have hinput : size t.component.Input ≤ curr.size := by
    rw [hsize]
    exact Nat.le_add_right _ _
  simp only [valueFromOffset, pairEnv, Environment.fromArray]
  congr 1
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_mapRange, zero_add]
  have hlt : j < curr.size := lt_of_lt_of_le (by simpa using hj) hinput
  rw [Array.getElem?_append_left hlt]

lemma circuitAssumptions (table : Table F) (consistent : table.DataConsistency data)
    (assumptions : table.Assumptions data)
    (p : ℕ × Array F × Array F) (hp : p ∈ table.pairs) :
    table.component.CircuitAssumptions (pairEnv p.2.1 p.2.2 data) := by
  obtain ⟨i, curr, next⟩ := p
  obtain ⟨hi, hcurr⟩ := getElem_of_mem_pairs hp
  have hmemcurr : curr ∈ table.table := curr_mem_table hp
  -- the circuit assumptions only mention the current row's input cells,
  -- which read identically from `curr` and from `curr ++ next`
  show table.component.circuit.Assumptions
    (valueFromOffset table.component.Input 0 (pairEnv curr next data)) data
  rw [valueFromOffset_pairEnv hp]
  apply table.component.assumptions_imply_circuit i curr data
  · cases hcolumns : table.component.fixedColumns with
    | none => simp [FixedRowAt]
    | some fixed =>
      have hmatch := table.fixed_rows_match
      simp only [Component.fixedRowsMatch, hcolumns] at hmatch
      have hlength : table.table.length = fixed.height := by
        simpa using congrArg List.length hmatch
      refine ⟨by omega, ?_⟩
      have hprefix := congrArg (fun rows => rows[i]?) hmatch
      have hleft : i < (table.table.map
          (fun candidate => candidate.extract 0 fixed.width)).length := by
        simp only [List.length_map]
        exact hi
      have hright : i < ((List.range fixed.height).map fixed.row).length := by
        simp only [List.length_map, List.length_range]
        omega
      rw [List.getElem?_eq_getElem hleft, List.getElem?_eq_getElem hright] at hprefix
      simp only [List.getElem_map, List.getElem_range, Option.some.injEq] at hprefix
      rw [hcurr] at hprefix
      exact hprefix
  · simp only [DataRowAt]
    rw [consistent]
    simp [Component.proverRows, hi, hcurr]
  · have h := assumptions _ (mem_envs_of_mem_pairs (data:=data) hp)
    show table.component.Assumptions
      (valueFromOffset table.component.Input 0 (Environment.fromArray curr data)) data
    rw [← valueFromOffset_pairEnv hp]
    exact h

/-- Every environment of a transition table satisfies the circuit's assumptions. -/
lemma circuitAssumptions_envs (table : Table F) (consistent : table.DataConsistency data)
    (assumptions : table.Assumptions data) :
    RowEnvs.CircuitAssumptions (F:=F) table data := by
  intro e he
  simp only [envs_eq, List.mem_map] at he
  obtain ⟨p, hp, rfl⟩ := he
  exact table.circuitAssumptions consistent assumptions p hp

/-- Circuit soundness, lifted to full table level. -/
theorem weakSoundness {table : Table F} (consistent : table.DataConsistency data) :
    table.Assumptions data → table.Constraints data → table.Guarantees data →
    table.Spec data ∧ table.Requirements data := by
  intro assumptions constraints guarantees
  exact RowEnvs.weakSoundness (table.circuitAssumptions_envs consistent assumptions)
    constraints guarantees

end Table

/-- Each named component is the source of its circuit-input rows in `ProverData`. -/
def deriveProverData : List (Table F) → ProverData F
  | [] => fun _ _ => #[]
  | table :: tables => fun name n =>
      if table.component.circuit.name = name then table.component.proverRows table.table n
      else deriveProverData tables name n

lemma deriveProverData_eq_of_mem (tables : List (Table F))
    (hunique : (tables.map (fun table => table.component.circuit.name)).Nodup)
    {table : Table F} (hmem : table ∈ tables) (n : ℕ) :
    deriveProverData tables table.component.circuit.name n =
      table.component.proverRows table.table n := by
  induction tables with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [List.map_cons, List.nodup_cons] at hunique
      obtain ⟨hhead, htail⟩ := hunique
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · simp [deriveProverData]
      · have hne : head.component.circuit.name ≠ table.component.circuit.name := by
          intro heq
          apply hhead
          rw [heq]
          exact List.mem_map.mpr ⟨table, hmem, rfl⟩
        simp [deriveProverData, hne, ih htail hmem]

end Air.Flat.Transition
