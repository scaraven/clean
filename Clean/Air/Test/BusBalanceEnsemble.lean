import Clean.Air.VmWith
import Clean.Air.BusProtocol
import Clean.Air.Test.BusBalance

/-!
# Bus balance: the models through ensemble soundness

Evidence for roadmap Layer 3, which connects the balance models to ensemble soundness
through the model-aware builders: the typed channel gate (a channel of the kind the model does
not read is a type error at the line that adds it); an ordered ensemble on a directed channel
built and closed under the multiset model over any field, with a nonempty witness of its
statement over `F 2` (the legacy relation admits at most one interaction there); a directed
VM built through `addVm` and `toFormal`; and the necessity fixtures of the hypotheses of the
directed VM theorem and of the count adapter behind it.

As in `Clean/Air/Test/BusBalance.lean`, an `example` whose type is `Prop` or a record is a
typechecking test only; every semantic claim is a proved statement or a `#guard`. The channel
fixtures `OneChannel`, `NeverDirected`, `LegacyChannel` and the empty prover data `noData` are
those of `BusBalance.lean`.
-/

namespace BusBalanceEnsembleTests
open Air.Flat
open BusBalanceTests (OneChannel NeverDirected LegacyChannel noData)

/-- A directed channel whose guarantee is free. -/
def AnyDirected (F : Type) [FiniteField F] : DirectedChannel F field where
  name := "any-directed"
  Guarantees _ _ := True

/-! ## The typed gate: a model accepts only the channel kind it reads -/
section Gate
variable {K : Type} [FiniteField K] [DecidableEq K]

/-- The correct pairings elaborate over any field: a directed channel under the multiset
model, a legacy channel under LogUp (over any prime field, as `LegacyChannel` is stated),
whether added or added and finished. -/
example : SoundEnsembleWith K (.multiset K) unit :=
  SoundEnsembleWith.empty K (.multiset K) unit |>.addChannel (OneChannel K)
example : SoundEnsembleWith K (.multiset K) unit :=
  SoundEnsembleWith.empty K (.multiset K) unit |>.addFinishedChannel (OneChannel K)
example {p : ℕ} [Fact p.Prime] : SoundEnsembleWith (F p) (.logUp (F p)) unit :=
  SoundEnsembleWith.empty (F p) (.logUp (F p)) unit |>.addFinishedChannel (LegacyChannel (p := p))

-- A channel of the other kind is a type error at the line that adds it, in both directions.
-- `#check_failure` succeeds exactly when elaboration fails; its report is dropped.
#guard_msgs (drop info) in
#check_failure (SoundEnsembleWith.empty (F 2) (.logUp (F 2)) unit |>.addChannel (OneChannel (F 2)))
#guard_msgs (drop info) in
#check_failure (SoundEnsembleWith.empty (F 5) (.multiset (F 5)) unit
  |>.addFinishedChannel (LegacyChannel (p := 5)))

/-- The escape hatch takes a raw channel with a consistency instance ... -/
example : SoundEnsembleWith K (.multiset K) unit :=
  SoundEnsembleWith.empty K (.multiset K) unit |>.addFinishedRawChannel (OneChannel K).toRaw

-- ... which instance search declares for neither mismatch, so the raw entry rejects them too
-- unless an instance is written by hand.
#guard_msgs (drop info) in
#check_failure (SoundEnsembleWith.empty (F 5) (.logUp (F 5)) unit
  |>.addFinishedRawChannel (OneChannel (F 5)).toRaw)
#guard_msgs (drop info) in
#check_failure (SoundEnsembleWith.empty (F 5) (.multiset (F 5)) unit
  |>.addFinishedRawChannel (LegacyChannel (p := 5)).toRaw)

/-- The erasure the builders record is the channel's own `toRaw`, as `circuit_norm` sees it. -/
example :
    (SoundEnsembleWith.empty K (.multiset K) unit |>.addFinishedChannel (OneChannel K)).channels
      = [(OneChannel K).toRaw] := by
  simp only [circuit_norm]
end Gate

/-! ## An ordered ensemble on a directed channel, closed under the multiset model (A14, A15) -/
section Ordered

/-- Provides the message `1`, which is what `OneChannel` guarantees. -/
def oneProvider (F : Type) [FiniteField F] : GeneralFormalCircuit F unit unit where
  main _ := (OneChannel F).push 1
  Spec _ _ _ := True
  channelsWithRequirements := [(OneChannel F).toRaw]
  soundness := by circuit_proof_start [OneChannel]
  completeness := by circuit_proof_start [OneChannel]

/-- Receives a message and assumes the guarantee for it: the row's spec is what the channel
guarantees, which the ensemble argument has to justify. -/
def oneConsumer (F : Type) [FiniteField F] : GeneralFormalCircuit F field unit where
  main x := (OneChannel F).pull x
  Spec x _ _ := x = 1
  ProverAssumptions x _ _ := x = 1
  soundness := by
    circuit_proof_start [OneChannel]
    exact h_holds
  completeness := by
    circuit_proof_start [OneChannel]
    exact h_assumptions

/-- The provider, then the channel finished, then the consumer: the consumer may assume what
the provider proved. The channel enters through the typed gate, and `markFinished` finds it by
`circuit_norm`. -/
def oneEnsemble (F : Type) [FiniteField F] [DecidableEq F] :
    SoundEnsembleWith F (.multiset F) unit :=
  SoundEnsembleWith.empty F (.multiset F) unit
    |>.addChannel (OneChannel F)
    |>.addTable ⟨ oneProvider F ⟩
      (by simp [circuit_norm, oneProvider]) (by simp [circuit_norm, oneProvider])
    |>.markFinished (OneChannel F).toRaw
    |>.addTable ⟨ oneConsumer F ⟩
      (by simp [circuit_norm, oneConsumer]) (by simp [circuit_norm, oneConsumer])

/-- A15, the full chain: over any field, every witness of the ensemble that satisfies its
constraints and is balanced under the multiset model satisfies the spec of every table, so
every consumer row carries `1`. The multiset balance feeds the consistency of the channel,
which transports the provider's requirement to the consumer's guarantee. -/
theorem oneEnsemble_tableSoundness (F : Type) [FiniteField F] [DecidableEq F] :
    (oneEnsemble F).TableSoundnessWith (.multiset F) :=
  Ensemble.tableSoundnessWith_of_soundChannelsWith
    ⟨ _, (oneEnsemble F).finished_subset, (oneEnsemble F).soundChannelsWith ⟩

/-- The bundle, with the `consistent` field filled by the builders. Its spec is trivial: with
no verifier the public input says nothing; the content is `oneEnsemble_tableSoundness`. -/
def oneFormal (F : Type) [FiniteField F] [DecidableEq F] :
    FormalEnsembleWith F (.multiset F) unit :=
  (oneEnsemble F).toFormal (fun _ => True) (fun _ => True)
    (by
      intro witness _
      simp only [EnsembleWitness.Assumptions, EnsembleWitness.forall_mem_allTables_iff]
      refine ⟨ EnsembleWitness.verifierTable_assumptions_of_verifier_empty rfl, ?_ ⟩
      intro table h_table
      have h := EnsembleWitness.mem_tables_component_of_mem_tables h_table
      simp only [oneEnsemble, circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
      intro row _
      show table.component.Assumptions (table.environment row)
      rcases h with h | h <;> rw [h] <;> simp [Component.Assumptions, oneConsumer, oneProvider])
    (fun _ _ => trivial)

/-- The provider table over `F 2`: one row, which has no input. -/
def providerTable : Table (F 2) where
  component := ⟨ oneProvider (F 2) ⟩
  width := 0
  table := [#[]]
  data := fun _ _ => #[]
  uniform_width := by simp

/-- The consumer table over `F 2`: one row reading `1`. -/
def consumerTable : Table (F 2) where
  component := ⟨ oneConsumer (F 2) ⟩
  width := 1
  table := [#[1]]
  data := fun _ _ => #[]
  uniform_width := by simp

/-- A witness with one provider row and one consumer row. -/
def oneWitness : EnsembleWitness (oneEnsemble (F 2)).ensemble where
  tables := [consumerTable, providerTable]
  data := fun _ _ => #[]
  publicInput := ()
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

/-- The two interactions the witness puts on the channel: the consumer's receive of `1` and
the provider's provide of `1`. -/
theorem oneWitness_interactions :
    oneWitness.allTablesWitness.interactionsWith (OneChannel (F 2)).toRaw =
      [ (OneChannel (F 2)).emittedValue .receive 1 1 true,
        (OneChannel (F 2)).emittedValue .provide 1 1 false ] := by
  rw [EnsembleWitness.interactionsWith_allTablesWitness,
    EnsembleWitness.interactionsWith_of_verifier_empty rfl]
  simp only [oneWitness, consumerTable, providerTable, Table.interactionsWith, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, Operations.interactionValuesWith_eq_map,
    Component.interactionsWith_eq]
  simp [circuit_norm, oneConsumer, oneProvider, DirectedChannel.eval_toRaw, Table.environment,
    Environment.fromArray]

/-- A9 at ensemble level, in miniature: over `F 2` the statement of the ordered ensemble under
the multiset model is satisfied by `oneWitness`, whose two interactions on the channel are
more than the legacy relation admits there (`legacy_length_le_one_over_F2` in
`BusBalance.lean`). -/
theorem oneEnsemble_statement_over_F2 :
    (oneEnsemble (F 2)).ensemble.StatementWith (.multiset (F 2)) () := by
  refine ⟨oneWitness, rfl, ?_, ?_⟩
  · rw [EnsembleWitness.Constraints, EnsembleWitness.forall_mem_allTables_iff]
    refine ⟨ EnsembleWitness.verifierTable_constraints_of_verifier_empty rfl, ?_ ⟩
    simp [oneWitness, consumerTable, providerTable, Table.Constraints, Component.constraints_eq,
      Component.lookups_eq, circuit_norm, oneConsumer, oneProvider]
  · intro channel h_channel
    simp only [oneEnsemble, circuit_norm, List.mem_singleton] at h_channel
    subst h_channel
    rw [oneWitness_interactions, BalanceModel.multiset_balanced_iff]
    simp [activePayloads, circuit_norm]
end Ordered

/-! ## A directed VM through `addVm` and `toFormal` (A14; A9 in miniature) -/
section Vm

/-- A counter state channel with a free guarantee: this section exercises the VM builders,
not a VM specification (roadmap Layer 4). -/
def CounterChannel (F : Type) [FiniteField F] : DirectedChannel F field where
  name := "counter"
  Guarantees _ _ := True

structure StepInput (F : Type) where
  enabled : F
  n : F
deriving ProvableStruct

/-- One VM step: receive `n` and provide `n + 1`, gated by a boolean `enabled`. -/
def counterStep (F : Type) [FiniteField F] : GeneralFormalCircuit F StepInput unit where
  main input := do
    assertZero (input.enabled * (input.enabled - 1))
    (CounterChannel F).pullIf input.enabled input.n
    (CounterChannel F).pushIf input.enabled (input.n + 1)
  exposedChannels
  | { enabled, n }, _ =>
    (CounterChannel F).expose [(CounterChannel F).pulledIf enabled n,
      (CounterChannel F).pushedIf enabled (n + 1)]
  exposedChannels_eq input i₀ := by
    obtain ⟨enabled, n⟩ := input
    simp only [circuit_norm, CounterChannel]
  ProverAssumptions input _ _ := input.enabled = 0 ∨ input.enabled = 1
  Spec _ _ _ := True
  channelsWithRequirements := [(CounterChannel F).toRaw]
  soundness := by
    circuit_proof_start [CounterChannel]
    rw [mul_eq_zero, sub_eq_zero] at h_holds
    simp_all
  completeness := by
    circuit_proof_start [CounterChannel]
    rcases h_assumptions with h | h <;> simp [h]

/-- The verifier receives the final state and provides the initial state `0`. -/
def counterVerifier (F : Type) [FiniteField F] : GeneralFormalCircuit F field unit where
  main input := do
    (CounterChannel F).pull input
    (CounterChannel F).push 0
  exposedChannels
  | n, _ => (CounterChannel F).expose [(CounterChannel F).pulled n, (CounterChannel F).pushed 0]
  Spec _ _ _ := True
  channelsWithRequirements := [(CounterChannel F).toRaw]
  soundness := by circuit_proof_start [CounterChannel]
  completeness := by circuit_proof_start [CounterChannel]

def counterVm (F : Type) [FiniteField F] [DecidableEq F] : DirectedVmTables F field where
  channel := CounterChannel F
  tables := [⟨ counterStep F ⟩]
  verifier := counterVerifier F
  verifier_length_zero := by simp [circuit_norm, counterVerifier]
  tables_channel := by simp [circuit_norm, counterStep, sub_eq_zero]
  verifier_channel := by simp [circuit_norm, counterVerifier]
  verifier_requirements env := by simp [circuit_norm, counterVerifier, CounterChannel]

/-- A14: the directed VM survives `addVm` and `toFormal` over any field, with the multiset
model fixed from the empty ensemble through the bundle; nothing falls back to LogUp. -/
def counterEnsemble (F : Type) [FiniteField F] [DecidableEq F] :
    FormalEnsembleWith F (.multiset F) field :=
  SoundEnsembleWith.empty F (.multiset F) field
    |>.addVm (counterVm F)
      (by simp [circuit_norm, counterVm])
      (by simp +instances [circuit_norm, counterVm, counterStep, counterVerifier])
      (by simp [circuit_norm, counterVm, counterStep, counterVerifier])
    |>.toFormal (fun _ _ => True) (by simp [circuit_norm, counterVm, counterStep])

example : FormalEnsembleWith (F 2) (.multiset (F 2)) field := counterEnsemble (F 2)

/-- One enabled step over `F 2`, from `0` to `1`: the row is `(enabled, n) = (1, 0)`. -/
def stepTable : Table (F 2) where
  component := ⟨ counterStep (F 2) ⟩
  width := 2
  table := [#[1, 0]]
  data := fun _ _ => #[]
  uniform_width := by simp

/-- The witness with that one step and the final state `1` as public input. -/
def counterWitness : EnsembleWitness (counterEnsemble (F 2)).ensemble where
  tables := [stepTable]
  data := fun _ _ => #[]
  publicInput := 1
  same_length := rfl
  same_circuits := by
    intro i hi
    match i with
    | 0 => rfl
  same_data := by
    intro table ht
    simp only [List.mem_singleton] at ht
    subst ht
    rfl

/-- Its four interactions on the state channel: the verifier receives `1` and provides `0`,
the step receives `0` and provides `1`. -/
theorem counterWitness_interactions :
    counterWitness.allTablesWitness.interactionsWith (CounterChannel (F 2)).toRaw =
      [ (CounterChannel (F 2)).emittedValue .receive 1 1 true,
        (CounterChannel (F 2)).emittedValue .provide 1 0 false,
        (CounterChannel (F 2)).emittedValue .receive 1 0 true,
        (CounterChannel (F 2)).emittedValue .provide 1 1 false ] := by
  have hv : (counterEnsemble (F 2)).ensemble.verifier = counterVerifier (F 2) := rfl
  rw [EnsembleWitness.interactionsWith_allTablesWitness]
  simp only [EnsembleWitness.interactionsWith, EnsembleWitness.allTables, List.flatMap_cons,
    Table.interactionsWith, EnsembleWitness.verifierTable_flatMap,
    EnsembleWitness.verifierTable_component, EnsembleWitness.verifierTable_environment,
    Operations.interactionValuesWith_eq_map, Ensemble.verifierTable_interactionsWith,
    Ensemble.verifierOperations, hv]
  simp only [counterWitness, stepTable, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Component.interactionsWith_eq]
  simp [circuit_norm, counterStep, counterVerifier, DirectedChannel.eval_toRaw, Table.environment,
    Environment.fromArray, Environment.fromInput, Component.rowOperations]
  rfl

/-- A9 for the VM path, in miniature: the statement of the counter ensemble under the multiset
model is satisfied over `F 2` by a nonempty witness, one step from `0` to `1` with the final
state `1` as public input and four interactions on the state channel (added in review). -/
theorem counterEnsemble_statement_over_F2 :
    (counterEnsemble (F 2)).ensemble.StatementWith (.multiset (F 2)) 1 := by
  refine ⟨counterWitness, rfl, ?_, ?_⟩
  · rw [EnsembleWitness.Constraints, EnsembleWitness.forall_mem_allTables_iff]
    refine ⟨ ?_, ?_ ⟩
    · rw [← EnsembleWitness.verifierConstraints_iff_verifierTable_constraints]
      simp [Ensemble.VerifierConstraints, circuit_norm, counterEnsemble, counterVm,
        counterVerifier]
    · simp [counterWitness, stepTable, Table.Constraints, Component.constraints_eq,
        Component.lookups_eq, circuit_norm, counterStep, Table.environment, Environment.fromArray]
  · intro channel h_channel
    simp only [counterEnsemble, counterVm, circuit_norm, List.mem_singleton] at h_channel
    subst h_channel
    rw [counterWitness_interactions, BalanceModel.multiset_balanced_iff]
    simp [activePayloads, circuit_norm]
    decide
end Vm

/-! ## Necessity of the hypotheses of the directed VM theorem (A7, A8 for Layer 3) -/
section Necessity
variable {K : Type} [FiniteField K] [DecidableEq K]

/-- A receive of `x` that assumes the guarantee, a provide of `x`, a disabled provide and a
disabled receive, on `OneChannel` over `F 2`. -/
def rec1 (x : F 2) : Interaction (F 2) := (OneChannel (F 2)).emittedValue .receive 1 x true
def prov1 (x : F 2) : Interaction (F 2) := (OneChannel (F 2)).emittedValue .provide 1 x false
def off1 : Interaction (F 2) := (OneChannel (F 2)).emittedValue .provide 0 0 false
def recOff : Interaction (F 2) := (OneChannel (F 2)).emittedValue .receive 0 0 true

/-- The lists of `pull_role_necessary`: a provide has been put among the pulls. -/
def badPulls : List (Interaction (F 2)) := [prov1 0, rec1 0, rec1 1]
def badPushes : List (Interaction (F 2)) := [prov1 1, off1, off1]

/-- `pulls_receive` is load-bearing in the directed VM theorem: with a provide among the pulls,
the lists are count-balanced, of equal length, on the channel, every push is a provide, every
row satisfies `G pulls[i] → R pushes[i]` (the provide among the pulls assumes nothing, so it
forces the requirement of the provide of `1` opposite it, which holds), the second push is
disabled and owes nothing, yet the second pull assumed `0 = 1`. The provide among the pulls
supplied that receive without any push owing its guarantee. Each fixture of this section
states the hypotheses it keeps, so that it is a counterexample to dropping exactly one. -/
theorem pull_role_necessary :
    CountBalanced Interaction.directedEvent (badPulls ++ badPushes) ∧
    badPulls.length = 3 ∧ badPushes.length = 3 ∧
    (∀ a ∈ badPulls, a.channel = (OneChannel (F 2)).toRaw) ∧
    (∀ b ∈ badPushes, b.channel = (OneChannel (F 2)).toRaw) ∧
    (∀ b ∈ badPushes, b.directedEvent.direction = .provide) ∧
    (∀ (i : ℕ) (hi : i < 3),
      badPulls[i].Guarantees (noData (F 2)) → badPushes[i].Requirements (noData (F 2))) ∧
    badPushes[1].Requirements (noData (F 2)) ∧ ¬ badPulls[1].Guarantees (noData (F 2)) := by
  refine ⟨?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply countBalanced_of_perm_activePayloads
    simp [activePayloads, badPulls, badPushes, prov1, rec1, off1, circuit_norm]
  · simp [badPulls, prov1, rec1, circuit_norm]
  · simp [badPushes, prov1, off1, circuit_norm]
  · simp [badPushes, prov1, off1, circuit_norm]
  · intro i hi
    match i with
    | 0 => simp [badPulls, badPushes, prov1, rec1, off1, OneChannel,
        DirectedChannel.emittedValue_guarantees_iff, DirectedChannel.emittedValue_requirements_iff]
    | 1 => simp [badPulls, badPushes, prov1, rec1, off1, OneChannel,
        DirectedChannel.emittedValue_guarantees_iff, DirectedChannel.emittedValue_requirements_iff]
    | 2 => simp [badPulls, badPushes, prov1, rec1, off1, OneChannel,
        DirectedChannel.emittedValue_guarantees_iff, DirectedChannel.emittedValue_requirements_iff]
  · simp [badPushes, off1, OneChannel, DirectedChannel.emittedValue_requirements_iff]
  · simp [badPulls, rec1, OneChannel, DirectedChannel.emittedValue_guarantees_iff]

/-- `balance` is load-bearing: an unbalanced pair, a receive of `0` that assumes against a
disabled provide, both on the channel and in their roles, satisfies the row implication
vacuously and the disabled provide owes nothing, yet the receive assumed `0 = 1`. -/
theorem balance_necessary :
    ¬ CountBalanced Interaction.directedEvent ([rec1 0] ++ [off1]) ∧
    (rec1 0).channel = (OneChannel (F 2)).toRaw ∧ off1.channel = (OneChannel (F 2)).toRaw ∧
    (rec1 0).directedEvent.direction = .receive ∧ off1.directedEvent.direction = .provide ∧
    ((rec1 0).Guarantees (noData (F 2)) → off1.Requirements (noData (F 2))) ∧
    off1.Requirements (noData (F 2)) ∧ ¬ (rec1 0).Guarantees (noData (F 2)) := by
  refine ⟨?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have := h (toElements (0 : field (F 2))).toArray
    rw [activeCount_eq_countP_activePayloads, activeCount_eq_countP_activePayloads] at this
    revert this
    simp [activePayloads, rec1, off1, circuit_norm]
  · simp [rec1, circuit_norm]
  · simp [off1, circuit_norm]
  · simp [rec1, off1, OneChannel, DirectedChannel.emittedValue_guarantees_iff,
      DirectedChannel.emittedValue_requirements_iff]
  · simp [off1, OneChannel, DirectedChannel.emittedValue_requirements_iff]
  · simp [rec1, OneChannel, DirectedChannel.emittedValue_guarantees_iff]

/-- An active provide of `0` on the channel whose guarantee is free. -/
def anyProv : Interaction (F 2) := (AnyDirected (F 2)).emittedValue .provide 1 0 false

/-- `pushes_channel` is load-bearing: the directed reading is channel-blind, so a provide of
`0` on the channel whose guarantee is free balances a receive of `0` on `OneChannel`, in their
roles, with the pull on the channel; that provide owes nothing, the row implication holds, and
the receive assumed `0 = 1`. -/
theorem pushes_channel_necessary :
    CountBalanced Interaction.directedEvent ([rec1 0] ++ [anyProv]) ∧
    (rec1 0).channel = (OneChannel (F 2)).toRaw ∧
    (rec1 0).directedEvent.direction = .receive ∧ anyProv.directedEvent.direction = .provide ∧
    ((rec1 0).Guarantees (noData (F 2)) → anyProv.Requirements (noData (F 2))) ∧
    anyProv.Requirements (noData (F 2)) ∧ ¬ (rec1 0).Guarantees (noData (F 2)) := by
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · apply countBalanced_of_perm_activePayloads
    simp [activePayloads, rec1, anyProv, circuit_norm]
  · simp [rec1, circuit_norm]
  · simp [anyProv, circuit_norm]
  · simp [anyProv, AnyDirected, DirectedChannel.emittedValue_requirements_iff]
  · simp [anyProv, AnyDirected, DirectedChannel.emittedValue_requirements_iff]
  · simp [rec1, OneChannel, DirectedChannel.emittedValue_guarantees_iff]

/-- An active receive of `1`, assuming the guarantee, on the channel whose guarantee is
`False`. -/
def neverRec : Interaction (F 2) := (NeverDirected (F 2)).emittedValue .receive 1 1 true

/-- `pulls_channel` is load-bearing: a receive of `1` on the channel whose guarantee is `False`
balances a provide of `1` on `OneChannel`, in their roles, with the push on the channel; that
provide meets its requirement, the row implication holds, and the receive assumed `False`. -/
theorem pulls_channel_necessary :
    CountBalanced Interaction.directedEvent ([neverRec] ++ [prov1 1]) ∧
    (prov1 1).channel = (OneChannel (F 2)).toRaw ∧
    neverRec.directedEvent.direction = .receive ∧ (prov1 1).directedEvent.direction = .provide ∧
    (neverRec.Guarantees (noData (F 2)) → (prov1 1).Requirements (noData (F 2))) ∧
    (prov1 1).Requirements (noData (F 2)) ∧ ¬ neverRec.Guarantees (noData (F 2)) := by
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · apply countBalanced_of_perm_activePayloads
    simp [activePayloads, prov1, neverRec, circuit_norm]
  · simp [neverRec, circuit_norm]
  · simp [prov1, circuit_norm]
  · simp [neverRec, NeverDirected, DirectedChannel.emittedValue_guarantees_iff]
  · simp [prov1, OneChannel, DirectedChannel.emittedValue_requirements_iff]
  · simp [neverRec, NeverDirected, DirectedChannel.emittedValue_guarantees_iff]

/-- The hypotheses of the count adapter `count_eq_of_countBalanced`: without equal lengths, an
inactive push has no partner ... -/
theorem count_eq_len_necessary :
    CountBalanced Interaction.directedEvent (([] : List (Interaction (F 2))) ++ [off1]) ∧
    ([] : List (Interaction (F 2))).countP (fun a => a.directedEvent.key = none) ≠
      [off1].countP (fun b => b.directedEvent.key = none) := by
  refine ⟨?_, ?_⟩
  · apply countBalanced_of_perm_activePayloads
    simp [activePayloads, off1, circuit_norm]
  · simp [off1, circuit_norm]

/-- ... without `pulls_receive`, a provide among the pulls balances a receive among the pulls
and the pushes count nothing ... -/
theorem count_eq_pulls_receive_necessary :
    CountBalanced Interaction.directedEvent ([prov1 0, rec1 0] ++ [off1, off1]) ∧
    ([prov1 0, rec1 0] : List (Interaction (F 2))).length = [off1, off1].length ∧
    (∀ b ∈ [off1, off1], b.directedEvent.direction = .provide) ∧
    [prov1 0, rec1 0].countP
        (fun a => a.directedEvent.key = some (toElements (0 : field (F 2))).toArray) ≠
      [off1, off1].countP
        (fun b => b.directedEvent.key = some (toElements (0 : field (F 2))).toArray) := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · apply countBalanced_of_perm_activePayloads
    simp [activePayloads, prov1, rec1, off1, circuit_norm]
  · simp [off1, circuit_norm]
  · simp [prov1, rec1, off1, circuit_norm]

/-- ... and without `pushes_provide`, an active receive among the pushes is counted on the push
side under its payload key: two disabled receives against a provide and a receive of `0` are
count-balanced, of equal length, and all pulls are receives, yet the key `[0]` counts `0` on
the pull side and `2` on the push side. (The first version of this fixture put two disabled
provides among the pulls, which drops `pulls_receive` as well; corrected in review.) -/
theorem count_eq_pushes_provide_necessary :
    CountBalanced Interaction.directedEvent ([recOff, recOff] ++ [prov1 0, rec1 0]) ∧
    ([recOff, recOff] : List (Interaction (F 2))).length = [prov1 0, rec1 0].length ∧
    (∀ a ∈ [recOff, recOff], a.directedEvent.direction = .receive) ∧
    [recOff, recOff].countP
        (fun a => a.directedEvent.key = some (toElements (0 : field (F 2))).toArray) ≠
      [prov1 0, rec1 0].countP
        (fun b => b.directedEvent.key = some (toElements (0 : field (F 2))).toArray) := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · apply countBalanced_of_perm_activePayloads
    simp [activePayloads, prov1, rec1, recOff, circuit_norm]
  · simp [recOff, circuit_norm]
  · simp [prov1, rec1, recOff, circuit_norm]
end Necessity

/-! ## The bus export protocol (A19) -/
section Protocol
variable {K : Type} [FiniteField K] [DecidableEq K]

-- A19: the schema of a directed channel identifies the interpretation the interaction bytes
-- do not carry: the relation, the tag index, the two tags, the gate and the malformed-tag
-- rule; its arity is the raw arity the interactions carry.
#guard (Lean.toJson (OneChannel (F 5)).schema).compress ==
  "{\"arity\":2,\"channel\":\"one\",\"malformed_tag\":\"reject\",\"multiplicity\":\"gate\"," ++
  "\"payload_arity\":1,\"relation\":\"multiset\",\"tag_index\":1," ++
  "\"tags\":{\"provide\":0,\"receive\":1}}"

-- A legacy channel's schema names the signed layout and the LogUp relation.
#guard (Lean.toJson (LegacyChannel (p := 5)).schema).compress ==
  "{\"arity\":1,\"channel\":\"legacy\",\"multiplicity\":\"signed\",\"relation\":\"logup\"}"

-- The protocol object binds the version and the ensemble's model to its channels.
#guard (Lean.toJson (BusProtocol.ofModel (.multiset (F 5)) [(OneChannel (F 5)).schema])).compress ==
  "{\"balance\":\"multiset\",\"channels\":[{\"arity\":2,\"channel\":\"one\"," ++
  "\"malformed_tag\":\"reject\",\"multiplicity\":\"gate\",\"payload_arity\":1," ++
  "\"relation\":\"multiset\",\"tag_index\":1,\"tags\":{\"provide\":0,\"receive\":1}}]," ++
  "\"protocol\":\"clean-bus\",\"version\":1}"
#guard (Lean.toJson
    (BusProtocol.ofModel (.logUp (F 5)) [(LegacyChannel (p := 5)).schema])).compress ==
  "{\"balance\":\"logup\",\"channels\":[{\"arity\":1,\"channel\":\"legacy\"," ++
  "\"multiplicity\":\"signed\",\"relation\":\"logup\"}],\"protocol\":\"clean-bus\",\"version\":1}"

/-- A protocol is well-formed when every channel has the layout its model reads, decided by
`decide`: the two supported pairings ... -/
example : (BusProtocol.ofModel (.multiset (F 5)) [(OneChannel (F 5)).schema]).WellFormed := by
  decide
example : (BusProtocol.ofModel (.logUp (F 5)) [(LegacyChannel (p := 5)).schema]).WellFormed := by
  decide

/-- ... and neither mismatch, the same two the static tie `BalanceModel.Reads` rejects. -/
example : ¬ (BusProtocol.ofModel (.logUp (F 5)) [(OneChannel (F 5)).schema]).WellFormed := by
  decide
example :
    ¬ (BusProtocol.ofModel (.multiset (F 5)) [(LegacyChannel (p := 5)).schema]).WellFormed := by
  decide

/-- The schema's arity is the raw arity the interactions carry, and its layout is the one the
multiset model exports, over any field. -/
example : (OneChannel K).schema.arity = (OneChannel K).toRaw.arity := rfl
example : (OneChannel K).schema.layout = BalanceModel.Protocol.layout (BalanceModel.multiset K) :=
  rfl

/-- The protocol of the ordered test ensemble `oneEnsemble`: one directed channel under the
multiset model. -/
def oneProtocol (F : Type) [FiniteField F] [DecidableEq F] : BusProtocol :=
  BusProtocol.ofModel (.multiset F) [(OneChannel F).schema]

example : (oneProtocol (F 2)).WellFormed := by decide
end Protocol

end BusBalanceEnsembleTests
