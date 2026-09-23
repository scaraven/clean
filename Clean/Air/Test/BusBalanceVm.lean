import Clean.Air.VmWith
import Clean.Air.Test.BusBalance

/-!
# Bus balance: a fixed-step VM over a binary field

Evidence for roadmap Layer 4 (A9, A10): a small VM with a fixed, nontrivial expected result,
proved through the directed VM chain of `Clean/Air/VmWith.lean` under the multiset model, over
any field and instantiated at `F 2`, where the legacy relation admits at most one interaction
per channel (`legacy_length_le_one_over_F2`).

The machine is a counter. Its state is a program counter and an accumulator, both `0`
initially; one step advances the program counter by one and replaces the accumulator by its
successor, taken from a lookup channel. After `k` steps the state is `(k, k)`. The verifier
provides the initial state and receives the state at program counter `N`, a constant of the
verifier, and its spec is that the accumulator it receives is the counter after `N` steps,
`(N : F)`. Nothing else is assumed: the result is carried by the guarantees of the two
channels through the ensemble proof.

`N` is fixed as a field element, not as a number of steps: the theorem is about the output only,
and it holds over every field without a characteristic bound. Over `F 2` with `N = 1` the
one-step run from `0` to `1` is accepted (`counterEnsemble_one_step_over_F2`: one step, one
successor row and the verifier, four interactions on the state channel and two on the successor
channel), and so is the three-step run `0 → 1 → 0 → 1` with the same output
(`counterEnsemble_three_steps_over_F2`), since a program counter read into `F 2` records only
the parity of the step count; the output `0` is rejected under the same statement
(`counterEnsemble_rejects_zero_over_F2`); and the legacy relation rejects every witness of the
ensemble, whatever `N` (`legacy_rejects_every_run`). The accumulator of a counter equals its
program counter on every reachable state; the example demonstrates the bus argument over a
binary field, not an arithmetic one.

The counter VM of `Clean/Air/Test/BusBalanceEnsemble.lean` has a free guarantee and exercises
the builders; this file is the VM specification that section defers to.
-/

namespace BusBalanceVmTests
open Air.Flat
open BusBalanceTests (legacy_length_le_one_over_F2)

/-! ## The machine: channels, step, successor provider and verifier -/

/-- The state channel of the counter. A state `(pc, acc)` is reachable when it is the state after
some number `k` of steps from `(0, 0)`, that is `(k, k)` as field elements. -/
def StateChannel (F : Type) [FiniteField F] : DirectedChannel F fieldPair where
  name := "state"
  Guarantees
  | (pc, acc), _ => ∃ k : ℕ, pc = (k : F) ∧ acc = (k : F)

/-- The successor lookup channel: a provider of `(x, y)` establishes `y = x + 1`. -/
def SuccChannel (F : Type) [FiniteField F] : DirectedChannel F fieldPair where
  name := "succ"
  Guarantees
  | (x, y), _ => y = x + 1

/-- The successor provider: one row per successor the machine consumes. Its content is the
requirement of its provide, so the channel is listed as one with requirements; the row spec is
trivial. -/
def succProvider (F : Type) [FiniteField F] : GeneralFormalCircuit F field unit where
  main x := (SuccChannel F).push (x, x + 1)
  Spec _ _ _ := True
  channelsWithRequirements := [(SuccChannel F).toRaw]
  soundness := by circuit_proof_start [SuccChannel]
  completeness := by circuit_proof_start [SuccChannel]

/-- A row of the step table: the gate, the current state and the successor of the accumulator. -/
structure StepRow (F : Type) where
  enabled : F
  pc : F
  acc : F
  next : F
deriving ProvableStruct

/-- One step of the counter, gated by a boolean `enabled`: receive the state `(pc, acc)`, look up
the successor `next` of `acc`, provide the state `(pc + 1, next)`. Its content is the requirement
of its provide, reachability of the next state; the row spec is trivial, as in the Fibonacci
example. -/
def counterStep (F : Type) [FiniteField F] : GeneralFormalCircuit F StepRow unit where
  main row := do
    assertZero (row.enabled * (row.enabled - 1))
    (StateChannel F).pullIf row.enabled (row.pc, row.acc)
    (SuccChannel F).pullIf row.enabled (row.acc, row.next)
    (StateChannel F).pushIf row.enabled (row.pc + 1, row.next)
  exposedChannels
  | { enabled, pc, acc, next }, _ =>
    (StateChannel F).expose [(StateChannel F).pulledIf enabled (pc, acc),
      (StateChannel F).pushedIf enabled (pc + 1, next)]
  exposedChannels_eq input i₀ := by
    obtain ⟨enabled, pc, acc, next⟩ := input
    simp only [circuit_norm, StateChannel, SuccChannel]
  ProverAssumptions row _ _ :=
    row.enabled = 0 ∨
      (row.enabled = 1 ∧ (∃ k : ℕ, row.pc = (k : F) ∧ row.acc = (k : F)) ∧
        row.next = row.acc + 1)
  Spec _ _ _ := True
  channelsWithRequirements := [(StateChannel F).toRaw]
  requirementsChannelsLawful input i₀ := by
    obtain ⟨enabled, pc, acc, next⟩ := input
    simp only [circuit_norm, StateChannel, SuccChannel]
    intro env h
    rw [mul_eq_zero, sub_eq_zero] at h
    exact h
  soundness := by
    circuit_proof_start [StateChannel, SuccChannel]
    obtain ⟨h_bool, h_state, h_succ⟩ := h_holds
    rw [mul_eq_zero, sub_eq_zero] at h_bool
    refine ⟨h_bool, h_bool, h_bool, fun h_on => ?_⟩
    obtain ⟨k, rfl, rfl⟩ := h_state h_on
    exact ⟨k + 1, by simp, by simp [h_succ h_on]⟩
  completeness := by
    circuit_proof_start [StateChannel, SuccChannel]
    rcases h_assumptions with rfl | ⟨rfl, h_state, h_succ⟩
    · simp
    · simp [h_state, h_succ]

/-- The verifier of the `N`-step run: it receives the state at program counter `N` and provides
the initial state `(0, 0)`. Its spec is the fixed-step result: the accumulator it receives is the
counter after `N` steps. -/
def counterVerifier (F : Type) [FiniteField F] (N : ℕ) : GeneralFormalCircuit F field unit where
  main output := do
    (StateChannel F).pull ((N : F), output)
    (StateChannel F).push (0, 0)
  exposedChannels
  | output, _ =>
    (StateChannel F).expose [(StateChannel F).pulled ((N : F), output),
      (StateChannel F).pushed (0, 0)]
  ProverAssumptions output _ _ := output = (N : F)
  Spec output _ _ := output = (N : F)
  channelsWithRequirements := [(StateChannel F).toRaw]
  soundness := by
    circuit_proof_start [StateChannel]
    obtain ⟨k, hk, rfl⟩ := h_holds
    exact ⟨hk.symm, 0, Nat.cast_zero.symm⟩
  completeness := by
    circuit_proof_start [StateChannel]
    exact ⟨N, rfl, h_assumptions⟩

/-- The counter as a directed VM: the state channel, the step table and the verifier. -/
def counterVm (F : Type) [FiniteField F] [DecidableEq F] (N : ℕ) : DirectedVmTables F field where
  channel := StateChannel F
  tables := [⟨ counterStep F ⟩]
  verifier := counterVerifier F N
  verifier_length_zero := by simp [circuit_norm, counterVerifier]
  tables_channel := by simp [circuit_norm, counterStep, sub_eq_zero]
  verifier_channel := by simp [circuit_norm, counterVerifier]
  verifier_requirements env := by
    simp [circuit_norm, counterVerifier, StateChannel]
    exact ⟨0, Nat.cast_zero.symm⟩

/-- The ensemble of the `N`-step run under the multiset model: the successor provider, then the
successor channel finished, then the VM, closed by `toFormal` with no extra assumption. Its spec
is the verifier's, `output = (N : F)`. -/
def counterEnsemble (F : Type) [FiniteField F] [DecidableEq F] (N : ℕ) :
    FormalEnsembleWith F (.multiset F) field :=
  SoundEnsembleWith.empty F (.multiset F) field
    |>.addTable ⟨ succProvider F ⟩
      (by simp [circuit_norm, succProvider]) (by simp [circuit_norm, succProvider])
    |>.addFinishedChannel (SuccChannel F)
    |>.addVm (counterVm F N)
      (by simp +instances [circuit_norm, counterVm, succProvider, SuccChannel, StateChannel])
      (by simp +instances [circuit_norm, counterVm, counterStep, counterVerifier])
      (by simp [circuit_norm, counterVm, counterStep, counterVerifier, SuccChannel, StateChannel])
    |>.toFormal (fun _ _ => True)
      (by simp [circuit_norm, counterVm, counterStep, succProvider])

/-! ## A10: the fixed-step result, over any field -/

/-- The fixed-step result: over any field, every proof of the statement of the `N`-step run
carries the counter after `N` steps as its output. No assumption on the output, the field or the
characteristic. -/
theorem counterEnsemble_output_eq (F : Type) [FiniteField F] [DecidableEq F] (N : ℕ)
    (output : F) :
    (counterEnsemble F N).ensemble.StatementWith (.multiset F) output → output = (N : F) := by
  intro statement
  have h := (counterEnsemble F N).soundness output ?_ statement
  · simp only [counterEnsemble, circuit_norm, counterVm, counterVerifier] at h
    obtain ⟨_, h⟩ := h
    exact h
  · simp [counterEnsemble, circuit_norm, counterVm, counterVerifier]

/-! ## A9, A10 over `F 2`: the one-step run from `0` to `1`, and the rejection of `0` -/

/-- The step table over `F 2`: one enabled step from `(0, 0)` with successor `1`, the row
`(enabled, pc, acc, next) = (1, 0, 0, 1)`. -/
def stepTable : Table (F 2) where
  component := ⟨ counterStep (F 2) ⟩
  width := 4
  table := [#[1, 0, 0, 1]]
  data := fun _ _ => #[]
  uniform_width := by simp

/-- The successor table over `F 2`: one row providing the successor of `0`. -/
def succTable : Table (F 2) where
  component := ⟨ succProvider (F 2) ⟩
  width := 1
  table := [#[0]]
  data := fun _ _ => #[]
  uniform_width := by simp

/-- The witness of the one-step run: the step row, the successor row, and the output `1`. -/
def counterWitness : EnsembleWitness (counterEnsemble (F 2) 1).ensemble where
  tables := [stepTable, succTable]
  data := fun _ _ => #[]
  publicInput := 1
  same_length := rfl
  same_circuits := by
    intro i hi
    match i with
    | 0 => rfl
    | 1 => rfl
  same_data := by
    intro table ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> rfl

/-- The four interactions of the witness on the state channel: the verifier receives `(1, 1)`
and provides `(0, 0)`, the step receives `(0, 0)` and provides `(1, 1)`. -/
theorem counterWitness_state_interactions :
    counterWitness.allTablesWitness.interactionsWith (StateChannel (F 2)).toRaw =
      [ (StateChannel (F 2)).emittedValue .receive 1 (1, 1) true,
        (StateChannel (F 2)).emittedValue .provide 1 (0, 0) false,
        (StateChannel (F 2)).emittedValue .receive 1 (0, 0) true,
        (StateChannel (F 2)).emittedValue .provide 1 (1, 1) false ] := by
  have hv : (counterEnsemble (F 2) 1).ensemble.verifier = counterVerifier (F 2) 1 := rfl
  rw [EnsembleWitness.interactionsWith_allTablesWitness]
  simp only [EnsembleWitness.interactionsWith, EnsembleWitness.allTables, List.flatMap_cons,
    Table.interactionsWith, EnsembleWitness.verifierTable_flatMap,
    EnsembleWitness.verifierTable_component, EnsembleWitness.verifierTable_environment,
    Operations.interactionValuesWith_eq_map, Ensemble.verifierTable_interactionsWith,
    Ensemble.verifierOperations, hv]
  simp only [counterWitness, stepTable, succTable, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, Component.interactionsWith_eq]
  simp [circuit_norm, counterStep, succProvider, counterVerifier, StateChannel, SuccChannel,
    DirectedChannel.eval_toRaw, Table.environment, Environment.fromArray, Environment.fromInput,
    Component.rowOperations]
  rfl

/-- The two interactions of the witness on the successor channel: the step receives `(0, 1)`
and the provider provides it. -/
theorem counterWitness_succ_interactions :
    counterWitness.allTablesWitness.interactionsWith (SuccChannel (F 2)).toRaw =
      [ (SuccChannel (F 2)).emittedValue .receive 1 (0, 1) true,
        (SuccChannel (F 2)).emittedValue .provide 1 (0, 1) false ] := by
  have hv : (counterEnsemble (F 2) 1).ensemble.verifier = counterVerifier (F 2) 1 := rfl
  rw [EnsembleWitness.interactionsWith_allTablesWitness]
  simp only [EnsembleWitness.interactionsWith, EnsembleWitness.allTables, List.flatMap_cons,
    Table.interactionsWith, EnsembleWitness.verifierTable_flatMap,
    EnsembleWitness.verifierTable_component, EnsembleWitness.verifierTable_environment,
    Operations.interactionValuesWith_eq_map, Ensemble.verifierTable_interactionsWith,
    Ensemble.verifierOperations, hv]
  simp only [counterWitness, stepTable, succTable, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, Component.interactionsWith_eq]
  simp [circuit_norm, counterStep, succProvider, counterVerifier, StateChannel, SuccChannel,
    DirectedChannel.eval_toRaw, Table.environment, Environment.fromArray, Environment.fromInput,
    Component.rowOperations]

/-- A9: over `F 2`, the statement of the one-step run with output `1` is satisfied by
`counterWitness`, six interactions in all, four on the state channel and two on the successor
channel. -/
theorem counterEnsemble_one_step_over_F2 :
    (counterEnsemble (F 2) 1).ensemble.StatementWith (.multiset (F 2)) 1 := by
  refine ⟨counterWitness, rfl, ?_, ?_⟩
  · rw [EnsembleWitness.Constraints, EnsembleWitness.forall_mem_allTables_iff]
    refine ⟨ ?_, ?_ ⟩
    · rw [← EnsembleWitness.verifierConstraints_iff_verifierTable_constraints]
      simp [Ensemble.VerifierConstraints, circuit_norm, counterEnsemble, counterVm,
        counterVerifier]
    · simp [counterWitness, stepTable, succTable, Table.Constraints, Component.constraints_eq,
        Component.lookups_eq, circuit_norm, counterStep, succProvider, Table.environment,
        Environment.fromArray]
  · intro channel h_channel
    simp only [counterEnsemble, counterVm, circuit_norm, List.mem_cons, List.not_mem_nil,
      or_false] at h_channel
    rcases h_channel with rfl | rfl
    · rw [counterWitness_state_interactions, BalanceModel.multiset_balanced_iff]
      simp [activePayloads, circuit_norm]
      decide
    · rw [counterWitness_succ_interactions, BalanceModel.multiset_balanced_iff]
      simp [activePayloads, circuit_norm]

/-- A10 over `F 2`: every proof of the one-step statement carries the output `1` ... -/
theorem counterEnsemble_output_one_over_F2 (output : F 2) :
    (counterEnsemble (F 2) 1).ensemble.StatementWith (.multiset (F 2)) output → output = 1 :=
  fun h => (counterEnsemble_output_eq (F 2) 1 output h).trans Nat.cast_one

/-- ... so the output `0` is rejected under the same statement. -/
theorem counterEnsemble_rejects_zero_over_F2 :
    ¬ (counterEnsemble (F 2) 1).ensemble.StatementWith (.multiset (F 2)) 0 :=
  fun h => absurd (counterEnsemble_output_one_over_F2 0 h) (by decide)

/-- The three-step run `0 → 1 → 0 → 1` over `F 2`: rows `(1, 0, 0, 1)`, `(1, 1, 1, 0)`,
`(1, 0, 0, 1)`. -/
def stepTable3 : Table (F 2) where
  component := ⟨ counterStep (F 2) ⟩
  width := 4
  table := [#[1, 0, 0, 1], #[1, 1, 1, 0], #[1, 0, 0, 1]]
  data := fun _ _ => #[]
  uniform_width := by simp

/-- Its three successor rows: the successors of `0`, `1` and `0`. -/
def succTable3 : Table (F 2) where
  component := ⟨ succProvider (F 2) ⟩
  width := 1
  table := [#[0], #[1], #[0]]
  data := fun _ _ => #[]
  uniform_width := by simp

/-- The witness of the three-step run, with the same output `1`. -/
def counterWitness3 : EnsembleWitness (counterEnsemble (F 2) 1).ensemble where
  tables := [stepTable3, succTable3]
  data := fun _ _ => #[]
  publicInput := 1
  same_length := rfl
  same_circuits := by
    intro i hi
    match i with
    | 0 => rfl
    | 1 => rfl
  same_data := by
    intro table ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> rfl

/-- The statement with `N = 1` also accepts the three-step run, with the same output: `N` fixes
the final program counter as a field element, which over `F 2` is the parity of the number of
steps. Its eight state-channel and six successor-channel interactions are balanced. -/
theorem counterEnsemble_three_steps_over_F2 :
    (counterEnsemble (F 2) 1).ensemble.StatementWith (.multiset (F 2)) 1 := by
  refine ⟨counterWitness3, rfl, ?_, ?_⟩
  · rw [EnsembleWitness.Constraints, EnsembleWitness.forall_mem_allTables_iff]
    refine ⟨ ?_, ?_ ⟩
    · rw [← EnsembleWitness.verifierConstraints_iff_verifierTable_constraints]
      simp [Ensemble.VerifierConstraints, circuit_norm, counterEnsemble, counterVm,
        counterVerifier]
    · simp [counterWitness3, stepTable3, succTable3, Table.Constraints, Component.constraints_eq,
        Component.lookups_eq, circuit_norm, counterStep, succProvider, Table.environment,
        Environment.fromArray]
  · have hv : (counterEnsemble (F 2) 1).ensemble.verifier = counterVerifier (F 2) 1 := rfl
    intro channel h_channel
    simp only [counterEnsemble, counterVm, circuit_norm, List.mem_cons, List.not_mem_nil,
      or_false] at h_channel
    rw [BalanceModel.multiset_balanced_iff, EnsembleWitness.interactionsWith_allTablesWitness]
    simp only [EnsembleWitness.interactionsWith, EnsembleWitness.allTables, List.flatMap_cons,
      Table.interactionsWith, EnsembleWitness.verifierTable_flatMap,
      EnsembleWitness.verifierTable_component, EnsembleWitness.verifierTable_environment,
      Operations.interactionValuesWith_eq_map, Ensemble.verifierTable_interactionsWith,
      Ensemble.verifierOperations, hv]
    simp only [counterWitness3, stepTable3, succTable3, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, Component.interactionsWith_eq]
    rcases h_channel with rfl | rfl <;>
      simp [circuit_norm, counterStep, succProvider, counterVerifier, StateChannel, SuccChannel,
        DirectedChannel.eval_toRaw, Table.environment, Environment.fromArray,
        Environment.fromInput, Component.rowOperations, activePayloads] <;>
      decide

/-- What the legacy relation makes of this ensemble over `F 2`: no witness of it, for any `N`,
is LogUp-balanced on the state channel, since the verifier alone puts two interactions there
and the no-wrap guard `length < ringChar (F 2) = 2` admits at most one
(`legacy_length_le_one_over_F2`). Generalised from the one-step witness in review. -/
theorem legacy_rejects_every_run (N : ℕ)
    (witness : EnsembleWitness (counterEnsemble (F 2) N).ensemble) :
    ¬ BalancedInteractions
      (witness.allTablesWitness.interactionsWith (StateChannel (F 2)).toRaw) := by
  intro h
  have hlen := legacy_length_le_one_over_F2 _ h
  have hv : (counterEnsemble (F 2) N).ensemble.verifier = counterVerifier (F 2) N := rfl
  rw [EnsembleWitness.interactionsWith_allTablesWitness] at hlen
  simp only [EnsembleWitness.interactionsWith, EnsembleWitness.allTables, List.flatMap_cons,
    Table.interactionsWith, EnsembleWitness.verifierTable_flatMap,
    EnsembleWitness.verifierTable_component, EnsembleWitness.verifierTable_environment,
    Operations.interactionValuesWith_eq_map, Ensemble.verifierTable_interactionsWith,
    Ensemble.verifierOperations, hv, List.length_append, List.length_map] at hlen
  simp [circuit_norm, counterVerifier, StateChannel] at hlen
  omega

end BusBalanceVmTests
