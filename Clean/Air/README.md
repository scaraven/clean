# Clean.Air

> :warning: This is partially LLM-written and subject to future human polish

`Clean.Air` contains the row-oriented proof-system layer that sits on top of the core circuit DSL. It is the home for AIR-like objects: components, trace tables, channel balance, ensembles, and formal end-to-end statements.

Two AIR styles are supported, and a single ensemble may mix them.

In **flat AIR**, one circuit is checked independently on each row of a table. The circuit does not directly refer to adjacent rows; all communication between rows and between components is expressed through channel interactions. This matches the modern layout where lookups, VM state transitions, and public API links are modeled by balanced channels rather than by next-row constraints.

In **transition AIR**, one circuit is checked on each *adjacent pair* of rows, and may read cells of both. This is the classic AIR transition constraint, and is the Air-side answer to `TableOperation.everyRowExceptLast`.

Which to reach for:

- **Channels** for cross-*component* communication, and for cross-row structure that is unordered or non-local (a lookup, a VM state handoff, a public API link).
- **Transition constraints** for dense, local, same-table row-to-row structure, where routing through a channel would cost a full lookup argument for what is really just "the next row continues this one".

A **component** says nothing about how many rows it spans; it merely packages a circuit. What differs between the two styles is only *which environments that circuit is checked against* — individual rows, or adjacent pairs. That distinction lives in the trace, not the component, and is captured by the `RowEnvs` class (see `Component.lean`). The style is recorded per ensemble entry as a `TableKind`; see `Entry.lean` for why that tag is soundness-critical.

In this terminology, a `Flat.Component` is an AIR component: it packages the circuit whose constraints are applied to every row (flat) or every row pair (transition). A `Flat.Table` is the concrete trace table for a flat component, and a `Flat.Transition.Table` the concrete trace for a transition component. A `Flat.TableContext` is a bundle of multiple concrete tables, of either kind, that share the same prover data object.

## Organization

`Circuit.lean` contains shared helpers for using `GeneralFormalCircuit`s as AIR components.

`Component.lean` defines what is shared by both AIR styles:

- `Flat.Component`: the static component, backed by a `GeneralFormalCircuit`. It records no row span.
- `Flat.RowEnvs`: the class that maps a trace to the list of environments its circuit is checked at. This is the single point at which the two styles differ.
- Every trace-level predicate (`Constraints`, `Assumptions`, `Guarantees`, `Requirements`, `Spec`, the `Channel*` family), interaction collection, and `weakSoundness`, all stated once over `RowEnvs` and therefore applying to both kinds.

It also proves the component-level transport lemmas: instantiated component operations agree with row operations, and component soundness lifts to whole-trace soundness.

`FlatComponent.lean` defines the flat trace layer:

- `Flat.Table`: concrete list of rows for one component, whose environments are the individual rows.
- `Flat.Table.circuitAssumptions`: supplies the fixed-row and derived-data facts at each row index.

Its predicates are stated in row-shaped form (`∀ row ∈ table.table`) rather than over environments, with `envs_iff` as the single bridge to the shared `RowEnvs` results.

`TransitionComponent.lean` defines the transition trace layer:

- `Flat.Transition.Table`: concrete list of rows, checked on adjacent pairs.
- `pairs` / `pairEnv`: the adjacent-row pairing, where a pair is evaluated as the concatenated environment `curr ++ next`. Cell `i` is `curr[i]` and cell `rowWidth + i` is `next[i]`, so "next row" is just an index offset — no new `Expression` node, and no changes to `eval` or `circuit_norm`.
- `valueFromOffset_pairEnv`: the current row's input cells read identically from `curr` alone and from `curr ++ next`. This is what lets the fixed-column and `ProverData` machinery, all stated about a single row, apply unchanged to a pair.

Note an `n`-row transition table imposes `n - 1` constraint instances, and a table of 0 or 1 rows is entirely unconstrained. Any bound on interaction count derived from table heights must use `n - 1` for transition entries.

`Entry.lean` connects the two kinds to the ensemble:

- `Flat.TableKind` and `Flat.Entry`: a component together with the kind of trace it is checked against. The kind is *not* derivable from the component — both kinds share one `Component` type, and since `Component.width` is defined as `rowWidth`, a flat and a transition table over the same component impose identical width obligations. It must therefore be recorded in the ensemble the verifier commits to, rather than left for the prover's witness to choose; `EnsembleWitness.same_circuits` binds it.
- `Flat.EntryTable`: the committed trace, either kind. It is itself a `RowEnvs` instance whose `envs` dispatches on the constructor, which is what lets every shared predicate apply to a mixed ensemble with no further work.
- `Flat.TableContext`: a bundle of committed tables, of either kind, sharing one prover data object.

`Balance.lean` contains the channel multiset theory. It defines `BalancedInteractions`, proves permutation and counting lemmas, and provides the channel-level implication principles used by higher-level soundness proofs. It also defines `RawChannel.Consistent` and `RawChannel.Normal`; typed channels are normal by construction, and normal channels are consistent, so both properties are satisfied in practice. A highlight in `Balance.lean` is the "guarantees-to-requirements-reversal" theorem which provides the basis for soundness of VM channels.

`FlatEnsemble.lean` defines AIR ensembles, `Flat.Ensemble` and their witnesses, `Flat.EnsembleWitness`. An ensemble has entries (each a component plus its kind, so flat and transition tables mix freely), channels, and an append-only verifier program. Entries are added with `addTable` or `addTransitionTable`. The verifier contributes public interactions directly; its operation type cannot create witnesses, constraints, lookups, or a synthetic table. Its `Statement` is the raw proof-system relation: there exists a witness whose table constraints hold and whose table and verifier interactions are balanced. The ensemble file also defines soundness and completeness and the `FormalEnsemble` structure which bundles an ensemble with its `Spec`, `Assumptions` and the soundness proof (completeness is TODO).

**Ensemble-level soundness** is more than a simple lifting of per-circuit soundness: it requires that channel guarantees, which were _assumed_ as part of local circuit proofs, are shown to hold unconditionally from global channel balance and constraints.

The library currently provides two distinct arguments to establish soundness, covering two prominent ways of using channels:

`OrderedChannel.lean` contains a staged channel construction for ordinary lookup-like channels. The defining property is a strict hierarchy on the list of component tables: any table that pushes to a channel must come before every table that pulls from it. From little more than this property, we prove ensemble-level soundness, as encapsulated in the `SoundEnsemble` structure. On the way, we introduce a relaxed notion of channel balance called `PartialBalancedChannels` that allows the balanced interaction list to contain additional interactions from tables added later. This makes it suitable for an inductive argument or gradual addition of tables to an existing sound ensemble.

Both channel soundness theories are stated over *interaction lists*, with no notion of which row produced what, so a transition entry changes only how a table's interaction list is produced and not its type. Consequently they apply to either kind unchanged: `SoundEnsemble.addTable` and `SoundEnsemble.addTransitionTable` carry the same channel side conditions, since ordering is about which channels a component uses, not how often it is checked.

`Vm.lean` contains a construction aimed at "VM-like" components that perform one transition per row. Since VM components both pull from and push to one distinguished state channel, they cannot follow the theory of ordered lookup-channel soundness. Instead, we prove a dedicated soundness theorem that applies to a set of VM components added to an existing hierarchical ensemble; a typical modern zkVMs layout.

`WitnessGeneration.lean` constructs ensemble witnesses from public input and a separately typed
runtime prover input. Demand-driven components allocate rows from channel messages. Preallocated
components initialize their prover-owned cells from constants or strided positions in the prover
input, while the generic builder supplies any verifier-fixed prefix. Preallocated channel handlers
identify an existing component interaction and a generated multiplicity column; messages and row
indices are derived from completed rows rather than duplicated in generation metadata.

The prover input is only an input to honest witness construction. Semantic `ProverData` is always
derived from the final committed component inputs. Export currently permits `dataGet` only from
stable cells of preallocated components and rejects reads from demand-generated or mutable cells.
This makes the initial data snapshot used by witness generation agree with the final derived data
at every readable location.

## Current limits of the transition kind

Transition entries are supported by the Lean model and its soundness theory, but not yet by the
executable layers:

- **Witness generation** refuses them. Generation is row-independent, whereas a transition table
  needs row `i+1` to be produced from row `i` (see `Clean/Table/WitnessGeneration.lean`'s
  `generateNextRow` for prior art). `assembleTables` throws rather than committing a flat trace
  against a transition entry.
- **Extraction** covers same-row operations only. `Air/Extraction/IR.lean`'s `ComponentProgram`
  needs a transition variant, and `Lower.lean`'s `expressionsBadVariable component.width` bound
  must become `2 * rowWidth` for transition entries (`Component.envWidth` already exists for
  this). The backend target is Plonky3's `builder.main().row_slice(1)`.
- **No worked example** yet. The natural one is Fibonacci with next-row constraints in place of
  the state channel used by `Clean/Examples/FibonacciWithChannels.lean`.

## Relation To Clean/Table

`Clean/Table` is the older table infrastructure. Its `InductiveTable` interface models classic AIRs where a row transition may directly relate adjacent rows, by putting the output of one VM step in the same relative position as the input of the next step.

The transition component is the `Clean.Air` answer to `TableOperation.everyRowExceptLast`: it recovers adjacent-row constraints without giving up the channel balance argument, so an ensemble can use next-row constraints where they are natural and channels everywhere else.

Not ported from `Clean/Table`:

- **Boundary constraints** (`TableOperation.boundary`). Until they exist, a transition ensemble must pin its boundaries through the verifier's public channel interactions. This is workable — it is how `Vm.lean` already seeds and terminates the VM state channel — but it is a genuine difference, and it is why a 0- or 1-row transition table being unconstrained is safe rather than a soundness hole.
- **Windows wider than two rows.** `RowEnvs` itself is agnostic, so a 3-row window would be a new instance rather than a redesign, but nothing currently builds one.
- **`InductiveTable`** and its `Spec`-carrying inductive interface.

The two layers remain independent, but `Clean.Air` is intended to become the common home for AIR-style infrastructure, including future support for the older inductive table style now living under `Clean/Table`.
