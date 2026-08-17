/-
Ensembles mixing both AIR component kinds.

An ensemble's *components* need no generalization: after the `RowEnvs` refactor a flat and a
transition component are the same `Air.Flat.Component`, and everything an `Ensemble` does with its
`tables` field -- names, `circuit.channelsWith*` -- is kind-agnostic. What differs is the *trace*:
a flat trace is checked once per row, a transition trace once per adjacent pair.

So the sum type lives on the witness side:

    EntryTable F := flat (Flat.Table F) | transition (Transition.Table F)

`EntryTable` is itself a `RowEnvs` instance whose `envs` dispatches on the constructor, which is
what lets every trace-level predicate, interaction collection, and `weakSoundness` apply to a mixed
ensemble with no further work.

The ensemble side still has to record *which* kind each component is checked as, via `Entry`. That
is soundness-critical rather than bookkeeping: `Component.width` is defined as `rowWidth` for both
kinds, so a flat and a transition `Table` over the same component impose identical `uniform_width`
obligations and are freely interchangeable. If the ensemble named only the component, a prover
could commit a transition component as a `.flat` entry; its next-row reads would then fall past the
row end and, since `Environment.fromArray` is total, silently read `0` instead of failing --
letting the prover choose the weaker constraint system. `EnsembleWitness.same_circuits` therefore
binds the kind as well as the component.
-/
import Clean.Air.FlatComponent
import Clean.Air.TransitionComponent

namespace Air.Flat
variable {F : Type} [FiniteField F]

/-- Which way an ensemble entry's circuit is checked against its trace. -/
inductive TableKind where
  | flat
  | transition
deriving DecidableEq, Repr

/--
One component of an ensemble, together with the kind of trace it is checked against.

The kind is not derivable from the component -- both kinds share the single `Component` type and
impose the same width obligation -- so it must be recorded here, in the ensemble the verifier
commits to, rather than being left for the prover's witness to choose. See the file header.
-/
structure Entry (F : Type) [FiniteField F] where
  component : Component F
  kind : TableKind

namespace Entry
variable {F : Type} [FiniteField F]

/-- Present a component as a flat entry. -/
abbrev flat (component : Component F) : Entry F := { component, kind := .flat }

/-- Present a component as a transition entry, checked on adjacent row pairs. -/
abbrev transition (component : Component F) : Entry F := { component, kind := .transition }

@[circuit_norm] lemma flat_component (component : Component F) :
  (Entry.flat component).component = component := rfl
@[circuit_norm] lemma transition_component (component : Component F) :
  (Entry.transition component).component = component := rfl

/-- Mapping components to flat entries preserves their names -- the shape `unique_names`
obligations take after an ensemble's `tables` becomes a list of entries. -/
@[circuit_norm] lemma map_flat_map_name (components : List (Component F)) :
    ((components.map Entry.flat).map (·.component.circuit.name)) =
      components.map (·.circuit.name) := by
  simp

end Entry

/--
One committed trace in an ensemble: either a flat table or a transition table.

This is the witness-side counterpart of `Entry`; `EnsembleWitness.same_circuits` requires the two
to agree on both component and `kind`.
-/
inductive EntryTable (F : Type) [FiniteField F] where
  | flat : Table F → EntryTable F
  | transition : Transition.Table F → EntryTable F

namespace EntryTable

/-- The component whose circuit this trace is checked against, whichever kind it is. -/
def component : EntryTable F → Component F
  | .flat table => table.component
  | .transition table => table.component

/-- The kind of trace this is, as an `Entry` records it. -/
def kind : EntryTable F → TableKind
  | .flat _ => .flat
  | .transition _ => .transition

/-- The ensemble entry this trace claims to fill: its component together with its kind. -/
def entry (table : EntryTable F) : Entry F :=
  { component := table.component, kind := table.kind }

/-- The trace rows, whichever kind it is. Note a transition table is constrained on the *pairs*
of these rows, so `rows.length` is not the number of constraint instances; see `envs`. -/
def rows : EntryTable F → List (Array F)
  | .flat table => table.table
  | .transition table => table.table

/-- Number of trace rows. -/
abbrev length (entry : EntryTable F) : ℕ := entry.rows.length

/--
The environments at which the entry's circuit is checked.

This is the *only* place the two kinds differ: a flat table contributes one environment per row,
a transition table one per adjacent pair -- so an `n`-row transition entry contributes `n - 1`
environments, and contributes none at all when `n ≤ 1`.
-/
def envs : EntryTable F → ProverData F → List (Environment F)
  | .flat table, data => RowEnvs.envs (F:=F) table data
  | .transition table, data => RowEnvs.envs (F:=F) table data

@[circuit_norm] lemma component_flat (table : Table F) :
  (EntryTable.flat table).component = table.component := rfl
@[circuit_norm] lemma component_transition (table : Transition.Table F) :
  (EntryTable.transition table).component = table.component := rfl
@[circuit_norm] lemma kind_flat (table : Table F) :
  (EntryTable.flat table).kind = .flat := rfl
@[circuit_norm] lemma kind_transition (table : Transition.Table F) :
  (EntryTable.transition table).kind = .transition := rfl
@[circuit_norm] lemma entry_component (table : EntryTable F) :
  table.entry.component = table.component := rfl
@[circuit_norm] lemma entry_kind (table : EntryTable F) :
  table.entry.kind = table.kind := rfl
@[circuit_norm] lemma rows_flat (table : Table F) :
  (EntryTable.flat table).rows = table.table := rfl
@[circuit_norm] lemma rows_transition (table : Transition.Table F) :
  (EntryTable.transition table).rows = table.table := rfl
@[circuit_norm] lemma envs_flat (table : Table F) (data : ProverData F) :
  (EntryTable.flat table).envs data = RowEnvs.envs (F:=F) table data := rfl
@[circuit_norm] lemma envs_transition (table : Transition.Table F) (data : ProverData F) :
  (EntryTable.transition table).envs data = RowEnvs.envs (F:=F) table data := rfl

/--
An entry presents its trace through whichever kind it holds. Every shared trace-level definition --
`Constraints`, `Assumptions`, `Guarantees`, `Requirements`, `Spec`, the `Channel*` family,
`interactions`, and `weakSoundness` -- therefore applies to entries with no further work.
-/
instance : RowEnvs F (EntryTable F) where
  component := EntryTable.component
  envs := EntryTable.envs
  data_eq := by
    rintro (table | table) data e he
    · exact RowEnvs.data_eq_of_mem (table:=table) he
    · exact RowEnvs.data_eq_of_mem (table:=table) he

@[circuit_norm] lemma rowEnvs_component (entry : EntryTable F) :
  RowEnvs.component (F:=F) entry = entry.component := rfl
@[circuit_norm] lemma rowEnvs_envs (entry : EntryTable F) (data : ProverData F) :
  RowEnvs.envs (F:=F) entry data = entry.envs data := rfl

/-- Prover-data consistency, dispatched to whichever kind the entry holds. -/
def DataConsistency : EntryTable F → ProverData F → Prop
  | .flat table, data => table.DataConsistency data
  | .transition table, data => table.DataConsistency data

@[circuit_norm] lemma dataConsistency_flat (table : Table F) (data : ProverData F) :
  (EntryTable.flat table).DataConsistency data = table.DataConsistency data := rfl
@[circuit_norm] lemma dataConsistency_transition (table : Transition.Table F)
    (data : ProverData F) :
  (EntryTable.transition table).DataConsistency data = table.DataConsistency data := rfl

/--
The circuit's assumptions hold at every environment of the entry.

Each kind proves this from its own `circuitAssumptions`, which is where the fixed-row and
derived-data facts are discharged -- and the only place the row-vs-pair reading matters.
-/
lemma circuitAssumptions_envs {entry : EntryTable F} {data : ProverData F}
    (consistent : entry.DataConsistency data)
    (assumptions : RowEnvs.Assumptions (F:=F) entry data) :
    RowEnvs.CircuitAssumptions (F:=F) entry data := by
  cases entry with
  | flat table =>
    rw [show RowEnvs.Assumptions (F:=F) (EntryTable.flat table) data
      = RowEnvs.Assumptions (F:=F) table data from rfl, ← Table.assumptions_iff] at assumptions
    exact table.circuitAssumptions_envs consistent assumptions
  | transition table =>
    exact table.circuitAssumptions_envs consistent assumptions

/-- Circuit soundness, lifted to a whole entry, whichever kind it is. -/
theorem weakSoundness {entry : EntryTable F} {data : ProverData F}
    (consistent : entry.DataConsistency data) :
    RowEnvs.Assumptions (F:=F) entry data →
    RowEnvs.Constraints (F:=F) entry data →
    RowEnvs.Guarantees (F:=F) entry data →
      RowEnvs.Spec (F:=F) entry data ∧ RowEnvs.Requirements (F:=F) entry data := by
  intro assumptions constraints guarantees
  exact RowEnvs.weakSoundness (circuitAssumptions_envs consistent assumptions)
    constraints guarantees

/--
Number of environments an entry contributes, in terms of its row count.

Flat entries contribute one per row; transition entries one per adjacent pair, hence `n - 1`.
This is what any bound on total interaction count must use -- in particular the `< ringChar F`
side condition carried by `BalancedInteractions`, since a forged balance becomes possible if
`p` copies of a push are allowed to sum to zero.
-/
@[circuit_norm] lemma envs_length (entry : EntryTable F) (data : ProverData F) :
    (entry.envs data).length =
      match entry with
      | .flat _ => entry.length
      | .transition _ => entry.length - 1 := by
  cases entry with
  | flat table => simp [envs, Table.envs_eq, length, rows]
  | transition table =>
    simp only [envs, Transition.Table.envs_eq, List.length_map, length, rows]
    exact table.pairs_length

/-- The circuit-input rows this trace contributes to `ProverData`.

Keyed on rows, not environments: a transition table is constrained on pairs, but its *data* is
still one input row per trace row, so this is identical for both kinds. -/
def proverRows (table : EntryTable F) (n : ℕ) : Array (Vector F n) :=
  table.component.proverRows table.rows n

@[circuit_norm] lemma proverRows_flat (table : Table F) (n : ℕ) :
  (EntryTable.flat table).proverRows n = table.proverRows n := rfl
@[circuit_norm] lemma proverRows_transition (table : Transition.Table F) (n : ℕ) :
  (EntryTable.transition table).proverRows n = table.proverRows n := rfl

/--
For a *flat* entry, the shared environment-shaped predicates specialize back to the row-shaped
spelling, since its environments are exactly its rows. Callers that only ever build flat entries
(VM ensembles, for instance) can keep reasoning about rows.
-/
lemma flat_envs_iff {motive : Environment F → Prop} (table : Table F) (data : ProverData F) :
    (∀ env ∈ RowEnvs.envs (F:=F) (EntryTable.flat table) data, motive env) ↔
      ∀ row ∈ table.table, motive (Environment.fromArray row data) :=
  Table.envs_iff table data

/-- A *flat* entry's environments are exactly its rows. -/
lemma envs_eq_of_kind_flat {table : EntryTable F} {data : ProverData F}
    (hkind : table.kind = .flat) :
    RowEnvs.envs (F:=F) table data = table.rows.map (Environment.fromArray · data) := by
  cases table with
  | flat t => rfl
  | transition t => simp [EntryTable.kind] at hkind

/-- A row of a *flat* entry is one of the environments it is checked at. -/
lemma mem_envs_of_mem_rows_of_kind_flat {table : EntryTable F} {data : ProverData F}
    (hkind : table.kind = .flat) {row : Array F} (hrow : row ∈ table.rows) :
    Environment.fromArray row data ∈ RowEnvs.envs (F:=F) table data := by
  cases table with
  | flat t => exact Table.mem_envs_of_mem_table hrow
  | transition t => simp [EntryTable.kind] at hkind

/-- `DataConsistency` restated through the kind-agnostic accessors, so it can be discharged
without casing on the constructor. Both kinds key their prover data on rows, not environments. -/
lemma dataConsistency_iff (table : EntryTable F) (data : ProverData F) :
    table.DataConsistency data ↔
      data table.component.circuit.name (size table.component.Input) =
        table.proverRows (size table.component.Input) := by
  cases table <;> rfl

/--
Each named component is the source of its circuit-input rows in `ProverData`.

This is the mixed-ensemble counterpart of the per-kind `Flat.deriveProverData` and
`Transition.deriveProverData`, and agrees with both: all three are keyed on
`component.proverRows rows`, which does not depend on the kind.
-/
def deriveProverData : List (EntryTable F) → ProverData F
  | [] => fun _ _ => #[]
  | table :: tables => fun name n =>
      if table.component.circuit.name = name then table.proverRows n
      else deriveProverData tables name n

lemma deriveProverData_eq_of_mem (tables : List (EntryTable F))
    (hunique : (tables.map (fun table => table.component.circuit.name)).Nodup)
    {table : EntryTable F} (hmem : table ∈ tables) (n : ℕ) :
    deriveProverData tables table.component.circuit.name n = table.proverRows n := by
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

end EntryTable

/-- A table subset together with the shared prover-data environment used to interpret it.

Retyped from `List (Table F)` to `List (EntryTable F)` so one context can hold both kinds. Every
operation below is a `RowEnvs` one, so the bodies and proofs are unchanged from the flat-only
version. -/
structure TableContext (F : Type) [FiniteField F] where
  tables : List (EntryTable F)
  data : ProverData F
  data_consistent : ∀ table ∈ tables, table.DataConsistency data

namespace TableContext
def cons (table : EntryTable F) (tables : TableContext F)
    (consistent : table.DataConsistency tables.data) : TableContext F where
  tables := table :: tables.tables
  data := tables.data
  data_consistent := by
    simp [consistent]
    apply tables.data_consistent

@[circuit_norm] lemma cons_tables {table : EntryTable F} {tables : TableContext F} (consistent) :
  (cons table tables consistent).tables = table :: tables.tables := rfl

@[circuit_norm] lemma cons_data {table : EntryTable F} {tables : TableContext F} (consistent) :
  (cons table tables consistent).data = tables.data := rfl

def induct {motive : TableContext F → Sort*}
  (nil : ∀ data, motive ⟨ [], data, by simp ⟩)
  (cons : ∀ table tables consistent, motive tables → motive (cons table tables consistent))
    (tables : TableContext F) : motive tables := by
  rcases tables with ⟨ ts, data, data_consistent ⟩
  induction ts with
  | nil => exact nil data
  | cons table ts ih =>
    have data_consistent' : ∀ table ∈ ts, table.DataConsistency data := by
      intro table h_table
      apply data_consistent
      simp [h_table]
    let tables : TableContext F := ⟨ ts, data, data_consistent' ⟩
    have consistent : table.DataConsistency tables.data := by
      simp [tables]
      exact data_consistent table (by simp)
    apply cons table tables consistent
    exact ih data_consistent'

def append (tables1 tables2 : TableContext F) (data_eq : tables1.data = tables2.data) : TableContext F where
  tables := tables1.tables ++ tables2.tables
  data := tables1.data
  data_consistent := by
    simp [or_imp, forall_and]
    constructor
    · apply tables1.data_consistent
    rw [data_eq]
    apply tables2.data_consistent

@[circuit_norm] lemma append_tables {tables1 tables2 : TableContext F} (data_eq : tables1.data = tables2.data) :
  (append tables1 tables2 data_eq).tables = tables1.tables ++ tables2.tables := rfl

@[circuit_norm] lemma append_data {tables1 tables2 : TableContext F} (data_eq : tables1.data = tables2.data) :
  (append tables1 tables2 data_eq).data = tables1.data := rfl

@[circuit_norm] lemma cons_append {table : EntryTable F} {tables1 tables2 : TableContext F}
  (consistent : table.DataConsistency tables1.data) (data_eq : tables1.data = tables2.data) :
  (cons table tables1 consistent).append tables2 data_eq =
    cons table (append tables1 tables2 data_eq) consistent := rfl

@[circuit_norm]
abbrev components (tables : TableContext F) : List (Component F) :=
  tables.tables.map (·.component)

/-- The ensemble entries this context fills, carrying each table's kind alongside its component. -/
@[circuit_norm]
abbrev entries (tables : TableContext F) : List (Entry F) :=
  tables.tables.map (·.entry)

abbrev Constraints (tables : TableContext F) : Prop :=
  ∀ table ∈ tables.tables, RowEnvs.Constraints (F:=F) table tables.data

abbrev Assumptions (tables : TableContext F) : Prop :=
  ∀ table ∈ tables.tables, RowEnvs.Assumptions (F:=F) table tables.data

noncomputable abbrev interactionsWith (tables : TableContext F) (channel : RawChannel F) : List (Interaction F) :=
  tables.tables.flatMap (RowEnvs.interactionsWith (F:=F) · tables.data channel)

@[circuit_norm] lemma interactionsWith_cons {table : EntryTable F} {tables : TableContext F}
  (consistent : table.DataConsistency tables.data) {channel : RawChannel F} :
  interactionsWith (cons table tables consistent) channel =
    RowEnvs.interactionsWith (F:=F) table tables.data channel ++ interactionsWith tables channel := by
  simp [interactionsWith, circuit_norm]

@[circuit_norm] lemma interactionsWith_append {tables1 tables2 : TableContext F}
  (data_eq : tables1.data = tables2.data) {channel : RawChannel F} :
  interactionsWith (append tables1 tables2 data_eq) channel =
    interactionsWith tables1 channel ++ interactionsWith tables2 channel := by
  simp only [interactionsWith, append, List.flatMap_append]
  rw [data_eq]
end TableContext

end Air.Flat
