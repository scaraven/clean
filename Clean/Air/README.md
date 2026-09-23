# Clean.Air

> :warning: This is partially LLM-written and subject to future human polish

`Clean.Air` contains the row-oriented proof-system layer that sits on top of the core circuit DSL. It is the home for AIR-like objects: components, trace tables, channel balance, ensembles, and formal end-to-end statements.

The first supported AIR style is **flat AIR**. In a flat AIR, one circuit is checked independently on each row of a table. The circuit does not directly refer to adjacent rows. All communication between rows and between components is expressed through channel interactions. This matches the modern layout where lookups, VM state transitions, and public API links are modeled by balanced channels rather than by next-row constraints.

In this terminology, a `Flat.Component` is a one-row AIR component: it packages the circuit whose constraints are applied to every row. A `Flat.Table` is the concrete trace table and prover data for such a component. A `Flat.Tables` value is a lightweight bundle of multiple concrete tables that share the same prover data object.

## Organization

`Circuit.lean` contains shared helpers for using `GeneralFormalCircuit`s as AIR components.

`FlatComponent.lean` defines the flat AIR component layer:

- `Flat.Component`: the static one-row component, backed by a `GeneralFormalCircuit`.
- `Flat.Table`: concrete array of rows for one component, together with the prover data used to evaluate constraints and channel interactions.
- `Flat.Tables`: a bundle of tables sharing one prover data object.

It also proves the basic row-level transport lemmas: instantiated component operations agree with row operations, component soundness lifts to table soundness, and table interactions can be collected per channel.

`Balance.lean` contains the channel multiset theory. It defines `BalancedInteractions`, proves permutation and counting lemmas, and provides the channel-level implication principles used by higher-level soundness proofs. It also defines `RawChannel.Consistent` and `RawChannel.Normal`; legacy typed channels (`Channel`) are normal by construction, and normal channels are consistent, so both properties are satisfied in practice (both are tied to the LogUp relation; the consistency of directed channels is `RawChannel.ConsistentWith` in `BalanceModel.lean`). A highlight in `Balance.lean` is the "guarantees-to-requirements-reversal" theorem which provides the basis for soundness of VM channels. That theorem is now a wrapper around a characteristic-free kernel: `Event` is the proof-facing view of an interaction (payload, direction, activity), `PullsSupported` and `CountBalanced` are the two facts the soundness arguments consume, stated over natural-number counts, and `guarantees_of_requirements_of_count_eq` is the reversal argument with no field structure at all. `Interaction.legacyEvent` reads direction off the sign convention, and the legacy bridges derive both kernel facts from `BalancedInteractions`.

`BalanceModel.lean` packages what a proof-system verifier establishes per channel as a `BalanceModel`: the verified relation, its side conditions, the reading of interactions as events, and the derivations of the kernel facts. It is an abstract count/support interface: the structure does not relate a model's reading to the raw channel contract, so a model is only usable in a channel soundness argument together with a proved correspondence law for the encoding it reads. `BalanceModel.logUp` is `BalancedInteractions` under the legacy reading; `BalanceModel.multiset` is the permutation of active provided and received payloads under the directed reading `Interaction.directedEvent`, with no characteristic bound, and its correspondence law is `directedEvent_emittedValue` together with `guarantees_of_requirements_of_pullsSupported`. A model only fits the channel encoding it reads: the multiset model on a legacy channel strips a payload element as if it were a tag and accepts messages that never matched, and the LogUp model on a directed channel is met only by traces with no active interaction. `RawChannel.ConsistentWith model` is the per-channel soundness obligation under a model, the legacy `RawChannel.Consistent` with the model as a parameter; it is declared for legacy channels under `logUp` and for directed channels under `multiset` only and is demanded of every channel by `FormalEnsembleWith`. It is false for the multiset model on a legacy channel with a refutable guarantee, but true for the LogUp model on every directed channel (that relation admits nothing active), so by itself it does not exclude that pairing. `BalanceModel.Reads model Ch` records the typed channel constructor each model reads (`logUp` reads `Channel`, `multiset` reads `DirectedChannel`); the model-aware builders take channels through it, so a channel of the wrong kind is a type error. The model-aware statements `Ensemble.StatementWith`, `SoundnessWith`, `CompletenessWith` and `FormalEnsembleWith` take the model explicitly, and there is no default model; the legacy `Statement` is their LogUp instance by definition. Directed channels themselves live in `Clean/Circuit/DirectedChannel.lean`: a `DirectedChannel` stores the direction of each interaction as the last raw message element, keeps the activation gate as the multiplicity, requires a well-formed tag, and keeps `assumeGuarantees` independent of direction, so that a receive can decline the guarantee. The raw JSON of a directed interaction is the legacy shape with one more message element and does not identify the directed interpretation; the opt-in export protocol is future work.

`OrderedChannelWith.lean` and `VmWith.lean` connect the models to ensemble soundness. The first restates the ordered-channel construction with the balance model as an explicit parameter (`PartialBalancedChannelWith`, `SoundChannelsWith`, `Ensemble.TableSoundnessWith`) and provides `SoundEnsembleWith F model PublicIO` with builders that take typed channels through `BalanceModel.Reads` (`addChannel`, `addFinishedChannel`) or raw channels gated on `RawChannel.ConsistentWith` (`addRawChannel`, `addFinishedRawChannel`), and a `toFormal` that fills `FormalEnsembleWith.consistent` from the consistency the record carries for every channel. The legacy notions are its `logUp` instances (`SoundEnsemble.withLogUp`, `SoundEnsembleWith.toSoundEnsemble`), and its module docstring says where a capacity premise (Clean issue #452) enters the LogUp side condition. The second is the VM construction for a directed state channel under the multiset model: `DirectedVmTables`, the directed VM theorem `DirectedChannel.guarantees_of_requirements_of_requirements_of_guarantees` (an instance of the kernel, with count equality from `count_eq_of_countBalanced`), `SoundVmEnsembleWith` and `SoundEnsembleWith.addVm`.

`FlatEnsemble.lean` defines flat AIR ensembles, `Flat.Ensemble` and their witnesses, `Flat.EnsembleWitness`. An ensemble has components, channels, and a verifier circuit. Its `Statement` is the raw proof-system relation: there exists a witness whose table constraints hold and whose channel interactions are balanced. The ensemble file also soundness and completeness and the `FormalEnsemble` structure which bundles an ensemble with its `Spec`, `Assumptions` and the soundness proof (completeness is TODO).

**Ensemble-level soundness** is more than a simple lifting of per-circuit soundness: it requires that channel guarantees, which were _assumed_ as part of local circuit proofs, are shown to hold unconditionally from global channel balance and constraints.

The library currently provides two distinct arguments to establish soundness, covering two prominent ways of using channels:

`OrderedChannels.lean` contains a staged channel construction for ordinary lookup-like channels. The defining property is a strict hierarchy on the list of component tables: any table that pushes to a channel must come before every table that pulls from it. From little more than this property, we prove ensemble-level soundness, as encapsulated in the `SoundEnsemble` structure. On the way, we introduce a relaxed notion of channel balance called `PartialBalancedChannels` that allows the balanced interaction list to contain additional interactions from tables added later. This makes it suitable for an inductive argument or gradual addition of tables to an existing sound ensemble.

`Vm.lean` contains a construction aimed at "VM-like" components that perform one transition per row. Since VM components both pull from and push to one distinguished state channel, they cannot follow the theory of ordered lookup-channel soundness. Instead, we prove a dedicated soundness theorem that applies to a set of VM components added to an existing hierarchical ensemble; a typical modern zkVMs layout.

## Channel contracts and the bus export protocol

Clean has two kinds of typed channel. They differ in how a row's interaction carries its
direction, in what a row must prove and may assume, and in the relation the verifier enforces
on the bus. Legacy channels are the default; directed channels are opt-in and exist because the
legacy contract says nothing useful over a field of characteristic two (`−1 = 1`, so a signed
multiplicity cannot tell a provide from a receive, and `1 + 1 = 0`, so two unmatched sends
cancel).

### Legacy channels (`Channel`, `Clean/Circuit/Channel.lean`)

An interaction has a signed multiplicity `m` and a message. The sign is the direction: `−1` is a
receive, any other nonzero value a provide. For a channel with guarantee `G`, evaluated at a
row:

| operation | bus contribution | may assume `G msg`? | must prove locally |
| --- | --- | --- | --- |
| `push msg` | `+1` | no | `G msg` |
| `pull msg` | `−1` | yes | nothing |
| `emit m msg` | `m` | no | `G msg` if `m ∉ {0, −1}` |
| `emit 0 msg` | zero | no | nothing |

`emit (−1) msg` is a receive that assumes nothing and owes nothing; sp1-lean's memory readers use
`emit (±is_real)` in this style. The raw requirement is `m ≠ −1 → m ≠ 0 → G msg`; the `−1`
exemption does not extend to other negative weights. The verifier enforces the LogUp relation:
for every message, the field sum of the multiplicities is `0`, under the no-wrap guard that the
channel's interaction list is shorter than the characteristic (`BalancedInteractions`,
`BalanceModel.logUp`). A weighted `emit` participates in that sum with its weight; only unit
multiplicities give a count of events.

### Directed channels (`DirectedChannel`, `Clean/Circuit/DirectedChannel.lean`)

An interaction has a direction, a gate and a message. The direction is stored as one extra raw
message element, the tag (`0` provide, `1` receive); the gate is the raw multiplicity and must
be `0` or `1`; one enabled interaction is one bus event. Permission to use the guarantee is
separate from the direction:

| operation | direction | may assume `G msg`? | must prove locally |
| --- | --- | --- | --- |
| `pushIf enabled msg` | provide | no | `enabled ∈ {0, 1}`, and `G msg` if `enabled ≠ 0` |
| `pullIf enabled msg` | receive | yes, if `enabled ≠ 0` | `enabled ∈ {0, 1}` |
| `emit .receive enabled msg` | receive | no | `enabled ∈ {0, 1}` |
| `emit .provide enabled msg` | provide | no | as `pushIf` |
| any, with `enabled = 0` | either | no | nothing beyond the gate |

`push`/`pull` are the `enabled = 1` cases. A receive that declines the guarantee still counts on
the receiving side of the bus. The verifier enforces the multiset relation: the payloads of the
active provides are a permutation of the payloads of the active receives, counted in the
natural numbers, with the tag removed before payloads of opposite direction are compared
(`BalanceModel.multiset` under the reading `Interaction.directedEvent`). There is no
characteristic condition. A raw interaction whose tag is neither value fails the channel's
requirements, so no sound row produces one.

### Ensemble soundness, per kind

A lookup-style ensemble on either kind is built with the model-aware builders of
`OrderedChannelWith.lean` (`SoundEnsembleWith F model PublicIO`), which accept a channel only
of the kind the model reads (`BalanceModel.Reads`); a VM on a directed state channel with
`VmWith.lean`. The legacy `SoundEnsemble` and `VmTables` remain for LogUp ensembles. In both
cases the soundness theorem's premise is "every channel is balanced under the model", so it
holds of a deployed system only if the backend enforces that model's relation on that
channel's interactions.

A worked directed VM is `Clean/Air/Test/BusBalanceVm.lean`: a counter whose state channel
carries reachability of the state, a successor lookup channel, and a verifier that fixes the
final program counter `N`. Its ensemble theorem, over any field and without a characteristic
bound, is that the output is the counter after `N` steps; over `F 2` the one-step run from `0`
to `1` has an explicit witness (four interactions on the state channel, two on the successor
channel) and the output `0` is rejected under the same statement, while the legacy relation
admits no such run at all.

### The bus export protocol (`Clean/Air/BusProtocol.lean`)

The JSON of an interaction (`Clean/Circuit/Json.lean`) is the same for both kinds: a channel
name, a multiplicity and a message, with a directed interaction's tag as the last message
element. Those bytes are unchanged and do not say which relation applies. The bus export
protocol, version 1, binds the interpretation beside them:

- a `ChannelSchema` per channel: its name, its raw arity, and its layout, `signed` (legacy: the
  message is the payload, the multiplicity a signed weight, relation `logup`) or `directed`
  (the message is the payload followed by the tag at index `arity − 1`, tags `provide = 0` and
  `receive = 1`, the multiplicity a `0`/`1` gate, relation `multiset` on the tag-stripped
  payloads, a tag outside `{0, 1}` rejected);
- a `BusProtocol` per ensemble: the version, the balance model (by its layout, one model per
  ensemble), and the channel schemas; `WellFormed` checks by `decide` that every channel has
  the layout the model reads.

Schemas come from the typed channels (`Channel.schema`, `DirectedChannel.schema`), the model's
layout from `BalanceModel.Protocol`, and each clause of the directed layout is a proved fact
about the encoding (tag index, payload size, gate and tag rules; see the module). A backend
that implements the schema enforces exactly the relation the Lean proofs assume.

## Relation To Clean/Table

`Clean/Table` is the older table infrastructure. Its `InductiveTable` interface models classic AIRs where a row transition may directly relate adjacent rows, by putting the output of one VM step in the same relative position as the input of the next step. `Clean.Air.Flat` instead models the modern one-row style: each component checks a single row in isolation, and all cross-row or cross-component structure is mediated by channels. The two layers are currently independent, but `Clean.Air` is intended to become the common home for AIR-style infrastructure, including future support for the older inductive table style now living under `Clean/Table`.
