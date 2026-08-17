/-
Flat AIR tables: a component whose circuit is checked independently on each row.

The `Component` structure itself, its `instantiate` transport lemmas, and every trace-level
predicate and interaction-collection definition are shared with the transition kind and live in
`Clean/Air/Component.lean`. What is specific to a flat table is only:

* its trace (`Table`), whose environments are the individual rows, and
* `circuitAssumptions`, which supplies the fixed-row and derived-data facts at each row index.
-/
import Clean.Air.Component

namespace Air.Flat
variable {F : Type} [FiniteField F]
variable {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]

namespace Component

/-- Width of a flat trace row: the component's committed cells. -/
abbrev width (component : Component F) : ℕ := component.rowWidth

end Component

/-- A concrete trace for one flat AIR component. Its data environment belongs to the ensemble. -/
structure Table (F : Type) [FiniteField F] where
  component : Component F
  table : List (Array F)
  uniform_width : ∀ row ∈ table, row.size = component.width
  /-- Connects the row-indexed fixed-column declaration to the concrete semantic rows. -/
  fixed_rows_match : component.fixedRowsMatch table := by
    simp [Component.fixedRowsMatch]

/-- A flat table is checked once per row, against that row alone. -/
instance : RowEnvs F (Table F) where
  component table := table.component
  envs table data := table.table.map (Environment.fromArray · data)
  data_eq := by
    intro table data e he
    simp only [List.mem_map] at he
    obtain ⟨row, _, rfl⟩ := he
    rfl

@[circuit_norm] lemma Table.envs_eq (table : Table F) (data : ProverData F) :
    RowEnvs.envs table data = table.table.map (Environment.fromArray · data) := rfl

@[circuit_norm] lemma Table.component_eq (table : Table F) :
    RowEnvs.component (F:=F) table = table.component := rfl

/-- Each named component is the source of its circuit-input rows in `ProverData`. -/
def deriveProverData : List (Table F) → ProverData F
  | [] => fun _ _ => #[]
  | table :: tables => fun name n =>
      if table.component.circuit.name = name then table.component.proverRows table.table n
      else deriveProverData tables name n

lemma deriveProverData_eq_of_mem (tables : List (Table F))
    (hunique : (tables.map (fun table => table.component.circuit.name)).Nodup)
    {table : Table F} (hmem : table ∈ tables) (n : ℕ) :
    deriveProverData tables table.component.circuit.name n = table.component.proverRows table.table n := by
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

namespace Table
variable {table : Table F} {data : ProverData F} {channel : RawChannel F}

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
Trace-level predicates and interaction collection, stated exactly as they were before the shared
`RowEnvs` layer existed: quantified over the trace's *rows*, with each row read as
`Environment.fromArray row data`.

The shared layer quantifies over environments instead, because a transition table constrains a
*pair* of rows and so the two kinds have no common row type. For the flat kind that distinction is
invisible -- its environments are exactly its rows -- so the row-shaped statements are kept here as
the primary spelling, and `envs_iff` below is the single lemma relating the two. Everything proved
over `RowEnvs` is then re-exported in row-shaped form.
-/

/-- Quantifying over a flat table's environments is quantifying over its rows. -/
lemma envs_iff {motive : Environment F → Prop} (table : Table F) (data : ProverData F) :
    (∀ env ∈ RowEnvs.envs (F:=F) table data, motive env) ↔
      ∀ row ∈ table.table, motive (Environment.fromArray row data) := by
  simp only [envs_eq, List.mem_map, forall_exists_index, and_imp]
  constructor
  · intro h row hrow; exact h _ row hrow rfl
  · intro h e row hrow heq; subst heq; exact h row hrow

@[circuit_norm]
def channelsWithGuarantees (table : Table F) : List (RawChannel F) :=
  table.component.circuit.channelsWithGuarantees

@[circuit_norm]
def channelsWithRequirements (table : Table F) : List (RawChannel F) :=
  table.component.circuit.channelsWithRequirements

def Constraints (table : Table F) (data : ProverData F) : Prop :=
  ∀ row ∈ table.table,
    table.component.operations.ConstraintsHold (Environment.fromArray row data)

def Assumptions (table : Table F) (data : ProverData F) : Prop :=
  ∀ row ∈ table.table,
    table.component.RowAssumptions (Environment.fromArray row data)

def Guarantees (table : Table F) (data : ProverData F) : Prop :=
  ∀ row ∈ table.table,
    table.component.operations.FullGuarantees (Environment.fromArray row data)

def ChannelGuarantees (table : Table F) (data : ProverData F) (channel : RawChannel F) : Prop :=
  ∀ row ∈ table.table,
    table.component.operations.ChannelGuarantees channel (Environment.fromArray row data)

def InChannelsOrGuarantees (table : Table F) (data : ProverData F)
    (channels : List (RawChannel F)) : Prop :=
  ∀ row ∈ table.table,
    table.component.operations.InChannelsOrGuaranteesFull channels (Environment.fromArray row data)

def Requirements (table : Table F) (data : ProverData F) : Prop :=
  ∀ row ∈ table.table,
    table.component.operations.FullRequirements (Environment.fromArray row data)

def ChannelRequirements (table : Table F) (data : ProverData F) (channel : RawChannel F) : Prop :=
  ∀ row ∈ table.table,
    table.component.operations.ChannelRequirements channel (Environment.fromArray row data)

def InChannelsOrRequirements (table : Table F) (data : ProverData F)
    (channels : List (RawChannel F)) : Prop :=
  ∀ row ∈ table.table,
    table.component.operations.InChannelsOrRequirementsFull channels (Environment.fromArray row data)

def Spec (table : Table F) (data : ProverData F) : Prop :=
  ∀ row ∈ table.table,
    table.component.Spec (Environment.fromArray row data)

def interactions (table : Table F) (data : ProverData F) : List (Interaction F) :=
  table.table.flatMap fun row =>
    table.component.operations.interactionValues (Environment.fromArray row data)

noncomputable def interactionsWith (table : Table F) (data : ProverData F)
    (channel : RawChannel F) : List (Interaction F) :=
  table.table.flatMap fun row =>
    table.component.operations.interactionValuesWith channel (Environment.fromArray row data)

noncomputable def interactionssWith (table : Table F) (data : ProverData F)
    (channel : RawChannel F) : List (List (Interaction F)) :=
  table.table.map fun row =>
    table.component.operations.interactionValuesWith channel (Environment.fromArray row data)

/-
Each row-shaped definition above agrees with its `RowEnvs` counterpart. These are what let the
shared proofs be re-exported below; they are `rfl`-free (they go through `envs_iff`) but cheap.
-/

lemma constraints_iff (table : Table F) (data : ProverData F) :
    table.Constraints data ↔ RowEnvs.Constraints (F:=F) table data := by
  rw [RowEnvs.Constraints, envs_iff]; rfl

lemma assumptions_iff (table : Table F) (data : ProverData F) :
    table.Assumptions data ↔ RowEnvs.Assumptions (F:=F) table data :=
  by rw [RowEnvs.Assumptions, envs_iff]; rfl

lemma guarantees_iff' (table : Table F) (data : ProverData F) :
    table.Guarantees data ↔ RowEnvs.Guarantees (F:=F) table data :=
  by rw [RowEnvs.Guarantees, envs_iff]; rfl

lemma channelGuarantees_iff (table : Table F) (data : ProverData F) (channel : RawChannel F) :
    table.ChannelGuarantees data channel ↔ RowEnvs.ChannelGuarantees (F:=F) table data channel :=
  by rw [RowEnvs.ChannelGuarantees, envs_iff]; rfl

lemma inChannelsOrGuarantees_iff (table : Table F) (data : ProverData F)
    (channels : List (RawChannel F)) :
    table.InChannelsOrGuarantees data channels ↔
      RowEnvs.InChannelsOrGuarantees (F:=F) table data channels :=
  by rw [RowEnvs.InChannelsOrGuarantees, envs_iff]; rfl

lemma requirements_iff' (table : Table F) (data : ProverData F) :
    table.Requirements data ↔ RowEnvs.Requirements (F:=F) table data :=
  by rw [RowEnvs.Requirements, envs_iff]; rfl

lemma channelRequirements_iff (table : Table F) (data : ProverData F) (channel : RawChannel F) :
    table.ChannelRequirements data channel ↔ RowEnvs.ChannelRequirements (F:=F) table data channel :=
  by rw [RowEnvs.ChannelRequirements, envs_iff]; rfl

lemma inChannelsOrRequirements_iff (table : Table F) (data : ProverData F)
    (channels : List (RawChannel F)) :
    table.InChannelsOrRequirements data channels ↔
      RowEnvs.InChannelsOrRequirements (F:=F) table data channels :=
  by rw [RowEnvs.InChannelsOrRequirements, envs_iff]; rfl

lemma spec_iff (table : Table F) (data : ProverData F) :
    table.Spec data ↔ RowEnvs.Spec (F:=F) table data :=
  by rw [RowEnvs.Spec, envs_iff]; rfl

lemma interactions_eq_rowEnvs (table : Table F) (data : ProverData F) :
    table.interactions data = RowEnvs.interactions (F:=F) table data := by
  simp only [interactions, RowEnvs.interactions_def, envs_eq, component_eq, List.flatMap_map]

lemma interactionsWith_eq_rowEnvs (table : Table F) (data : ProverData F)
    (channel : RawChannel F) :
    table.interactionsWith data channel = RowEnvs.interactionsWith (F:=F) table data channel := by
  simp only [interactionsWith, RowEnvs.interactionsWith_def, envs_eq, component_eq,
    List.flatMap_map]

lemma interactionssWith_eq_rowEnvs (table : Table F) (data : ProverData F)
    (channel : RawChannel F) :
    table.interactionssWith data channel = RowEnvs.interactionssWith (F:=F) table data channel := by
  simp only [interactionssWith, RowEnvs.interactionssWith_def, envs_eq, component_eq, List.map_map,
    Function.comp_def]

/-
The trace-level lemmas are likewise inherited, restated in row-shaped form. Each is the shared
`RowEnvs` result transported across the `*_iff` / `*_eq_rowEnvs` bridges above, so the statements
here are identical to what they were before the shared layer existed.
-/

open Classical in lemma interactionsWith_eq_filter :
    table.interactionsWith data channel = (table.interactions data).filter (·.channel = channel) := by
  rw [interactionsWith_eq_rowEnvs, interactions_eq_rowEnvs]
  exact RowEnvs.interactionsWith_eq_filter

lemma channel_eq_of_mem_interactionsWith {i : Interaction F} :
    i ∈ table.interactionsWith data channel → i.channel = channel := by
  rw [interactionsWith_eq_rowEnvs]
  exact RowEnvs.channel_eq_of_mem_interactionsWith

lemma interactionsWith_nil_of_channel_not_mem :
    channel ∉ table.component.circuit.channels → table.interactionsWith data channel = [] := by
  rw [interactionsWith_eq_rowEnvs]
  exact RowEnvs.interactionsWith_nil_of_channel_not_mem (table:=table) (data:=data) (channel:=channel)

lemma guarantees_iff_forall (table : Table F) (data : ProverData F) :
    table.Guarantees data ↔ ∀ i ∈ table.interactions data, i.Guarantees data := by
  rw [guarantees_iff', interactions_eq_rowEnvs]
  exact RowEnvs.guarantees_iff_forall table data

lemma channelGuarantees_iff_forall (table : Table F) (data : ProverData F)
    (channel : RawChannel F) :
    table.ChannelGuarantees data channel ↔
    ∀ i ∈ table.interactionsWith data channel, i.Guarantees data := by
  rw [channelGuarantees_iff, interactionsWith_eq_rowEnvs]
  exact RowEnvs.channelGuarantees_iff_forall table data channel

lemma guarantees_iff_channelGuarantees (table : Table F) (data : ProverData F) :
    table.Guarantees data ↔
    ∀ channel ∈ table.channelsWithGuarantees, table.ChannelGuarantees data channel := by
  rw [guarantees_iff']
  rw [show table.channelsWithGuarantees = RowEnvs.channelsWithGuarantees (F:=F) table from rfl]
  simp only [channelGuarantees_iff]
  exact RowEnvs.guarantees_iff_channelGuarantees table data

lemma channelGuarantees_of_requirements (table : Table F) (data : ProverData F)
    {channel : RawChannel F} :
    table.Guarantees data → table.ChannelGuarantees data channel := by
  rw [guarantees_iff', channelGuarantees_iff]
  exact RowEnvs.channelGuarantees_of_requirements table data

lemma requirements_iff_forall (table : Table F) (data : ProverData F) :
    table.Requirements data ↔ ∀ i ∈ table.interactions data, i.Requirements data := by
  rw [requirements_iff', interactions_eq_rowEnvs]
  exact RowEnvs.requirements_iff_forall table data

lemma channelRequirements_iff_forall (table : Table F) (data : ProverData F)
    (channel : RawChannel F) :
    table.ChannelRequirements data channel ↔
    ∀ i ∈ table.interactionsWith data channel, i.Requirements data := by
  rw [channelRequirements_iff, interactionsWith_eq_rowEnvs]
  exact RowEnvs.channelRequirements_iff_forall table data channel

lemma requirements_iff_channelRequirements_of_constraints (table : Table F)
    (data : ProverData F) :
    table.Constraints data →
    (table.Requirements data ↔
    ∀ channel ∈ table.channelsWithRequirements, table.ChannelRequirements data channel) := by
  rw [constraints_iff, requirements_iff']
  rw [show table.channelsWithRequirements = RowEnvs.channelsWithRequirements (F:=F) table from rfl]
  simp only [channelRequirements_iff]
  exact RowEnvs.requirements_iff_channelRequirements_of_constraints table data

lemma channelRequirements_of_requirements (table : Table F) (data : ProverData F)
    {channel : RawChannel F} :
    table.Requirements data → table.ChannelRequirements data channel := by
  rw [requirements_iff', channelRequirements_iff]
  exact RowEnvs.channelRequirements_of_requirements table data

lemma inChannelsOrRequirements_of_constraints (table : Table F) (data : ProverData F) :
    table.Constraints data →
    table.InChannelsOrRequirements data table.channelsWithRequirements := by
  rw [constraints_iff, inChannelsOrRequirements_iff]
  rw [show table.channelsWithRequirements = RowEnvs.channelsWithRequirements (F:=F) table from rfl]
  exact RowEnvs.inChannelsOrRequirements_of_constraints table data

lemma requirements_of_not_mem_of_constraints (table : Table F) (data : ProverData F)
    {channel : RawChannel F} :
    table.Constraints data →
    channel ∉ table.channelsWithRequirements → table.ChannelRequirements data channel := by
  rw [constraints_iff, channelRequirements_iff]
  rw [show table.channelsWithRequirements = RowEnvs.channelsWithRequirements (F:=F) table from rfl]
  exact RowEnvs.requirements_of_not_mem_of_constraints table data

lemma inChannelsOrGuarantees (table : Table F) (data : ProverData F) :
    table.InChannelsOrGuarantees data table.channelsWithGuarantees := by
  rw [inChannelsOrGuarantees_iff]
  rw [show table.channelsWithGuarantees = RowEnvs.channelsWithGuarantees (F:=F) table from rfl]
  exact RowEnvs.inChannelsOrGuarantees table data

lemma guarantees_of_not_mem (table : Table F) (data : ProverData F) {channel : RawChannel F} :
    channel ∉ table.channelsWithGuarantees → table.ChannelGuarantees data channel := by
  rw [channelGuarantees_iff]
  rw [show table.channelsWithGuarantees = RowEnvs.channelsWithGuarantees (F:=F) table from rfl]
  exact RowEnvs.guarantees_of_not_mem table data

lemma forall_interactions_iff (table : Table F) (data : ProverData F)
    (motive : Interaction F → Prop) :
    (∀ i ∈ table.interactions data, motive i) ↔
    ∀ row ∈ table.table, ∀ i ∈ table.component.operations.interactions,
      motive (i.eval (Environment.fromArray row data)) := by
  rw [interactions_eq_rowEnvs, RowEnvs.forall_interactions_iff]
  exact envs_iff table data

lemma forall_interactionsWith_iff (table : Table F) (data : ProverData F)
    (channel : RawChannel F) (motive : Interaction F → Prop) :
    (∀ i ∈ table.interactionsWith data channel, motive i) ↔
    ∀ row ∈ table.table, ∀ i ∈ table.component.operations.interactions,
      (i.channel = channel → motive (i.eval (Environment.fromArray row data))) := by
  rw [interactionsWith_eq_rowEnvs, RowEnvs.forall_interactionsWith_iff]
  exact envs_iff table data

/-- The row-level phrasing of `Constraints`. Now definitional, since `Constraints` is row-shaped. -/
lemma constraints_iff_forall_row :
    table.Constraints data ↔ ∀ row ∈ table.table,
      table.component.operations.ConstraintsHold (Environment.fromArray row data) := Iff.rfl

lemma circuitAssumptions (table : Table F) (consistent : table.DataConsistency data)
    (assumptions : table.Assumptions data)
    (row : Array F) (hrow : row ∈ table.table) :
    table.component.CircuitAssumptions (Environment.fromArray row data) := by
  obtain ⟨i, hi⟩ := List.get_of_mem hrow
  apply table.component.assumptions_imply_circuit i.val row data
  · cases hcolumns : table.component.fixedColumns with
    | none => simp [FixedRowAt]
    | some fixed =>
      have hmatch := table.fixed_rows_match
      simp only [Component.fixedRowsMatch, hcolumns] at hmatch
      have hlength : table.table.length = fixed.height := by
        simpa using congrArg List.length hmatch
      refine ⟨by omega, ?_⟩
      have hprefix := congrArg (fun rows => rows[i.val]?) hmatch
      have hleft : i.val < (table.table.map
          (fun candidate => candidate.extract 0 fixed.width)).length := by
        simp only [List.length_map]
        exact i.isLt
      have hright : i.val < ((List.range fixed.height).map fixed.row).length := by
        simp only [List.length_map, List.length_range]
        omega
      rw [List.getElem?_eq_getElem hleft, List.getElem?_eq_getElem hright] at hprefix
      simp only [List.getElem_map, List.getElem_range, Option.some.injEq] at hprefix
      have hi' : table.table[i.val] = row := hi
      rw [hi'] at hprefix
      exact hprefix
  · simp only [DataRowAt]
    rw [consistent]
    have hi' : table.table[i.val] = row := hi
    simp [Component.proverRows, i.isLt, hi']
  · exact assumptions row hrow

/-- Every environment of a flat table satisfies the circuit's assumptions. -/
lemma circuitAssumptions_envs (table : Table F) (consistent : table.DataConsistency data)
    (assumptions : table.Assumptions data) :
    RowEnvs.CircuitAssumptions (F:=F) table data := by
  intro e he
  simp only [envs_eq, List.mem_map] at he
  obtain ⟨row, hrow, rfl⟩ := he
  exact table.circuitAssumptions consistent assumptions row hrow

/-- Circuit soundness, lifted to full table level. -/
theorem weakSoundness {table : Table F} (consistent : table.DataConsistency data) :
    table.Assumptions data → table.Constraints data → table.Guarantees data →
    table.Spec data ∧ table.Requirements data := by
  intro assumptions constraints guarantees
  rw [spec_iff, requirements_iff']
  rw [constraints_iff] at constraints
  rw [guarantees_iff'] at guarantees
  exact RowEnvs.weakSoundness (table.circuitAssumptions_envs consistent assumptions)
    constraints guarantees

/-- A row of the trace is one of the environments the table is checked at. -/
lemma mem_envs_of_mem_table {row : Array F} (hrow : row ∈ table.table) :
    Environment.fromArray row data ∈ RowEnvs.envs (F:=F) table data := by
  simp only [envs_eq, List.mem_map]
  exact ⟨row, hrow, rfl⟩

/--
If we know constraints and _some_ of the guarantees unconditionally, we can remove them from the
per-row assumptions.

This lemma is tailored to VM-like channels where there remains a single channel that we need to
prove guarantees for.
-/
lemma requirements_of_partial_guarantees_of_constraints {table : Table F}
  {finished : List (RawChannel F)} {unfinished : RawChannel F} :
  table.DataConsistency data →
  table.Assumptions data →
  table.Constraints data →
  table.channelsWithGuarantees ⊆ unfinished :: finished →
  (∀ channel ∈ finished, table.ChannelGuarantees data channel) →
    ∀ row ∈ table.table,
      table.component.operations.ChannelGuarantees unfinished (Environment.fromArray row data) →
      table.component.operations.ChannelRequirements unfinished (Environment.fromArray row data) := by
  intro consistent assumptions constraints subset finished_grts row h_row
  rw [constraints_iff] at constraints
  simp only [channelGuarantees_iff] at finished_grts
  exact RowEnvs.requirements_of_partial_guarantees_of_constraints
    (table.circuitAssumptions_envs consistent assumptions) constraints subset finished_grts
    _ (mem_envs_of_mem_table h_row)

end Table

end Air.Flat
