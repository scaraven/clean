import Clean.Air.BalanceModel
import Clean.Circuit.Json

/-!
# The bus export protocol, version 1

What a backend has to know, per channel, to enforce the balance relation that the Lean
soundness proofs assume. The proofs of `Clean.Air.OrderedChannelWith` and `Clean.Air.VmWith`
conclude soundness from `Ensemble.StatementWith model`, "every channel's interactions are
`model.Balanced`". That premise is only worth anything if the verifier actually enforces the
model's relation on the interactions it receives. The exported interactions do not say which
relation that is: a directed interaction serializes to the legacy channel/message/multiplicity
object with the direction tag as one more message element, byte for byte the JSON of a legacy
interaction with a one-element-longer payload (pinned in `Clean/Air/Test/BusBalance.lean`).
Over a binary field the two readings disagree on real traces: two provides of the same payload
sum to zero under the LogUp relation and are rejected by the multiset relation.

The protocol therefore binds the interpretation *beside* the interactions, not inside them, so
that the bytes of every existing interaction are unchanged (roadmap decision on the export,
2026-09-23):

* `ChannelSchema`: for one channel, its name, its raw arity and its `ChannelLayout`. A `signed`
  channel is a legacy `Channel`: the message is the payload, the multiplicity a signed weight,
  and the verifier enforces the field-sum relation with its no-wrap guard (`BalanceModel.logUp`).
  A `directed` channel is a `DirectedChannel`: the message is the payload followed by the
  direction tag at index `arity - 1` (`0` provide, `1` receive), the multiplicity is a `0`/`1`
  gate, and the verifier enforces the natural-number multiset relation on the payloads with the
  tag removed (`BalanceModel.multiset`); an interaction whose tag is neither value is rejected.
* `BusProtocol`: the protocol version, the balance model of the ensemble (by its layout, since
  an ensemble is balanced under one model), and the schemas of its channels. `WellFormed` says
  every channel has the layout the model reads; it is decidable, so an export is checked by
  `decide`.

The schema is produced from the typed channels (`Channel.schema`, `DirectedChannel.schema`),
which is where the encoding is known; after erasure to `RawChannel` nothing records it. The
model's layout comes from `BalanceModel.Protocol`, declared for the two models like
`BalanceModel.Reads`, so that a model and the channel kind it reads export the same layout
(`Channel.schema_layout_logUp`, `DirectedChannel.schema_layout_multiset`).

## What the clauses of the protocol mean in Lean

Each clause of the directed layout is a fact about the encoding of `Clean.Circuit.DirectedChannel`
and the reading `Interaction.directedEvent` of `Clean.Air.BalanceModel`, stated below:

* tag position: `Interaction.directedEvent_direction_eq_provide_iff_tagIndex`, the reading
  looks at index `arity - 1`;
* tag removal: `Interaction.directedEvent_payload_size`, the payload the relation compares
  has `arity - 1` elements (`directedEvent_payload` in `BalanceModel.lean` says it is the
  message with its last element removed);
* gate handling: `DirectedChannel.gate_of_requirements`, a sound row's gate is `0` or `1`;
* malformed tags: `DirectedChannel.tag_of_requirements`, a sound row's tag is one of the two.

The last two are the local contract's obligations, so a backend that rejects a gate outside
`{0, 1}` or a tag outside `{0, 1}` rejects only traces that no sound row produces.

What the protocol does not do: it does not change `AbstractInteraction`'s JSON, it does not add
a field to any public record, and it does not by itself make a backend enforce anything. It is
the document a backend implements and the object an ensemble export includes next to its
operations. The integration with a consumer (leanerVM) is separate work.
-/

open Lean

/-- How a channel's raw messages are laid out and which relation the verifier enforces on
them. -/
inductive ChannelLayout where
  /-- A legacy `Channel`: message = payload, signed multiplicity, field-sum relation with the
  no-wrap guard (`BalanceModel.logUp`). -/
  | signed
  /-- A `DirectedChannel`: message = payload followed by the direction tag at the last index,
  `0`/`1` gate, natural-number multiset relation on tag-stripped payloads
  (`BalanceModel.multiset`), tags outside `{0, 1}` rejected. -/
  | directed
  deriving DecidableEq, Repr

namespace ChannelLayout
/-- The name of the relation the backend enforces, as exported. -/
def relationName : ChannelLayout → String
  | .signed => "logup"
  | .directed => "multiset"
end ChannelLayout

/-- The exported description of one channel. -/
structure ChannelSchema where
  name : String
  /-- The raw arity, as the interactions carry it: the payload arity plus one for a directed
  channel. -/
  arity : ℕ
  layout : ChannelLayout
  deriving DecidableEq, Repr

namespace ChannelSchema
def toJson (s : ChannelSchema) : Json :=
  match s.layout with
  | .signed => Json.mkObj [
      ("channel", s.name),
      ("arity", s.arity),
      ("relation", ChannelLayout.signed.relationName),
      ("multiplicity", "signed") ]
  | .directed => Json.mkObj [
      ("channel", s.name),
      ("arity", s.arity),
      ("relation", ChannelLayout.directed.relationName),
      ("payload_arity", Lean.toJson (s.arity - 1)),
      ("tag_index", Lean.toJson (s.arity - 1)),
      ("tags", Json.mkObj [("provide", (0 : ℕ)), ("receive", (1 : ℕ))]),
      ("multiplicity", "gate"),
      ("malformed_tag", "reject") ]

instance : ToJson ChannelSchema := ⟨ChannelSchema.toJson⟩
end ChannelSchema

/-- The exported bus protocol of one ensemble: the version, the layout of the model the
ensemble is balanced under, and its channels. -/
structure BusProtocol where
  layout : ChannelLayout
  channels : List ChannelSchema
  deriving DecidableEq, Repr

namespace BusProtocol
/-- The protocol version this module specifies. -/
def version : ℕ := 1

/-- Every channel has the layout the ensemble's model reads. -/
def WellFormed (p : BusProtocol) : Prop := ∀ c ∈ p.channels, c.layout = p.layout

instance (p : BusProtocol) : Decidable p.WellFormed :=
  inferInstanceAs (Decidable (∀ c ∈ p.channels, c.layout = p.layout))

instance : ToJson BusProtocol where
  toJson p := Json.mkObj [
    ("protocol", "clean-bus"),
    ("version", version),
    ("balance", p.layout.relationName),
    ("channels", Lean.toJson p.channels) ]
end BusProtocol

variable {F : Type} [FiniteField F] [DecidableEq F]
variable {Message : TypeMap} [ProvableType Message]

/-- The schema of a legacy typed channel. -/
def Channel.schema (channel : Channel F Message) : ChannelSchema :=
  ⟨ channel.name, size Message, .signed ⟩

/-- The schema of a directed channel: one more raw element than the payload, for the tag. -/
def DirectedChannel.schema (channel : DirectedChannel F Message) : ChannelSchema :=
  ⟨ channel.name, size Message + 1, .directed ⟩

omit [DecidableEq F] in
@[circuit_norm] lemma Channel.schema_arity (channel : Channel F Message) :
    channel.schema.arity = channel.toRaw.arity := rfl
omit [FiniteField F] [DecidableEq F] in
@[circuit_norm] lemma Channel.schema_layout (channel : Channel F Message) :
    channel.schema.layout = .signed := rfl
omit [DecidableEq F] in
@[circuit_norm] lemma DirectedChannel.schema_arity (channel : DirectedChannel F Message) :
    channel.schema.arity = channel.toRaw.arity := rfl
omit [FiniteField F] [DecidableEq F] in
@[circuit_norm] lemma DirectedChannel.schema_layout (channel : DirectedChannel F Message) :
    channel.schema.layout = .directed := rfl

/-- The layout a balance model exports. Declared for the two models only, like
`BalanceModel.Reads`. -/
class BalanceModel.Protocol (model : BalanceModel F) where
  layout : ChannelLayout

instance : (BalanceModel.logUp F).Protocol := ⟨.signed⟩
instance : (BalanceModel.multiset F).Protocol := ⟨.directed⟩

/-- The protocol object of an ensemble under a model, with the schemas of its channels. -/
def BusProtocol.ofModel (model : BalanceModel F) [model.Protocol] (channels : List ChannelSchema) :
    BusProtocol :=
  ⟨ BalanceModel.Protocol.layout model, channels ⟩

/-- A model and the channel kind it reads export the same layout: legacy channels under LogUp
... -/
theorem Channel.schema_layout_logUp (channel : Channel F Message) :
    channel.schema.layout = BalanceModel.Protocol.layout (BalanceModel.logUp F) := rfl

/-- ... and directed channels under the multiset model. -/
theorem DirectedChannel.schema_layout_multiset (channel : DirectedChannel F Message) :
    channel.schema.layout = BalanceModel.Protocol.layout (BalanceModel.multiset F) := rfl

/-! ## The clauses of the directed layout, as facts about the encoding -/

/-- Tag position: the directed reading looks at the last raw element, index `arity - 1`. -/
theorem Interaction.directedEvent_direction_eq_provide_iff_tagIndex (i : Interaction F) :
    i.directedEvent.direction = .provide ↔
      i.msg[i.channel.arity - 1]? = some Direction.provide.tag := by
  rw [Interaction.directedEvent_direction_eq_provide, ← i.same_size]
  rfl

/-- Tag removal: the payload the relation compares has `arity - 1` elements. -/
theorem Interaction.directedEvent_payload_size (i : Interaction F) :
    i.directedEvent.payload.size = i.channel.arity - 1 := by
  rw [Interaction.directedEvent_payload, Array.size_pop, i.same_size]

omit [DecidableEq F] in
/-- Gate handling: a sound row's gate is `0` or `1`. -/
theorem DirectedChannel.gate_of_requirements (channel : DirectedChannel F Message) (mult : F)
    (msg : Vector F channel.toRaw.arity) (data : ProverData F) :
    channel.toRaw.Requirements mult msg data → mult = 0 ∨ mult = 1 :=
  fun h => h.1

omit [DecidableEq F] in
/-- Malformed tags: a sound row's tag is the provide tag or the receive tag. -/
theorem DirectedChannel.tag_of_requirements (channel : DirectedChannel F Message) (mult : F)
    (msg : Vector F channel.toRaw.arity) (data : ProverData F) :
    channel.toRaw.Requirements mult msg data →
      msg.toArray.back? = some Direction.provide.tag ∨
        msg.toArray.back? = some Direction.receive.tag :=
  fun h => h.2.1
