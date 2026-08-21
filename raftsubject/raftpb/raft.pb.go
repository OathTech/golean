// Code DERIVED from etcd-io/raft raftpb/raft.pb.go by
// tools/raftsubject/derive.py. DO NOT EDIT — edit the derivation.
//
// This is the `plainpb` shim ruled on 2026-08-19
// (docs/2026-08-15_raft-push-p0-scoping.md §8.6): raft's WIRE TYPES,
// DECLARED rather than generated, so the current library's LOGIC can be
// verified without the protobuf runtime (reflect / unsafe / sync) entering
// the trust surface.
//
// Upstream: deps/raft @ 56e3200, protoc-gen-go v1.36.11, syntax proto2.
// Kept: 9 message structs (field numbers preserved in the struct tags),
// 4 enums with their constants and name/value maps, every generated getter
// (verbatim, shape-checked by the derivation), Enum(), ProtoMessage(),
// Reset() reduced to its plain-Go half.
// Fail-closed stubs: 26 (message String, Descriptor, EnumDescriptor,
// UnmarshalJSON). Enum String is REAL (W4.3 item 1): the _name map plus
// the decimal fallback, mirroring the runtime's EnumStringOf.
// Dropped: the file-descriptor machinery and ProtoReflect (see the log's
// subject-delta ledger for the itemised list and the reasoning).
//
// WIRE CODEC (W4.1, H-1 discharged — docs/raft-w41-log.md item 1): the
// per-type Marshal/Unmarshal/Size live in the generated plain_codec.go
// (AppendMessage / SizeMessage / UnmarshalMessage), derived from the field
// numbers and wire types pinned in the struct tags below. The byte-format
// contract is protobuf wire compatibility for exactly these nine messages;
// the differential obligation is difftest.py section 7 (vs the real
// protobuf runtime) plus the in-sandbox codeccheck.py battery.
package raftpb

type EntryType int32

const (
	EntryType_EntryNormal       EntryType = 0
	EntryType_EntryConfChange   EntryType = 1 // corresponds to pb.ConfChange
	EntryType_EntryConfChangeV2 EntryType = 2 // corresponds to pb.ConfChangeV2
)

var (
	EntryType_name = map[int32]string{
		0: "EntryNormal",
		1: "EntryConfChange",
		2: "EntryConfChangeV2",
	}
	EntryType_value = map[string]int32{
		"EntryNormal":       0,
		"EntryConfChange":   1,
		"EntryConfChangeV2": 2,
	}
)

func (x EntryType) Enum() *EntryType {
	p := new(EntryType)
	*p = x
	return p
}

func (x EntryType) String() string {
	if s, ok := EntryType_name[int32(x)]; ok {
		return s
	}
	return plainpbEnumUnknown(int32(x))
}

func (x *EntryType) UnmarshalJSON(b []byte) error {
	panic("plainpb: EntryType.UnmarshalJSON is a fail-closed stub (protobuf runtime engineered out; docs/raft-w2-log.md)")
}

func (EntryType) EnumDescriptor() ([]byte, []int) {
	panic("plainpb: EntryType.EnumDescriptor is a fail-closed stub (protobuf runtime engineered out; docs/raft-w2-log.md)")
}

type MessageType int32

const (
	MessageType_MsgHup               MessageType = 0
	MessageType_MsgBeat              MessageType = 1
	MessageType_MsgProp              MessageType = 2
	MessageType_MsgApp               MessageType = 3
	MessageType_MsgAppResp           MessageType = 4
	MessageType_MsgVote              MessageType = 5
	MessageType_MsgVoteResp          MessageType = 6
	MessageType_MsgSnap              MessageType = 7
	MessageType_MsgHeartbeat         MessageType = 8
	MessageType_MsgHeartbeatResp     MessageType = 9
	MessageType_MsgUnreachable       MessageType = 10
	MessageType_MsgSnapStatus        MessageType = 11
	MessageType_MsgCheckQuorum       MessageType = 12
	MessageType_MsgTransferLeader    MessageType = 13
	MessageType_MsgTimeoutNow        MessageType = 14
	MessageType_MsgReadIndex         MessageType = 15
	MessageType_MsgReadIndexResp     MessageType = 16
	MessageType_MsgPreVote           MessageType = 17
	MessageType_MsgPreVoteResp       MessageType = 18
	MessageType_MsgStorageAppend     MessageType = 19
	MessageType_MsgStorageAppendResp MessageType = 20
	MessageType_MsgStorageApply      MessageType = 21
	MessageType_MsgStorageApplyResp  MessageType = 22
	MessageType_MsgForgetLeader      MessageType = 23
)

var (
	MessageType_name = map[int32]string{
		0:  "MsgHup",
		1:  "MsgBeat",
		2:  "MsgProp",
		3:  "MsgApp",
		4:  "MsgAppResp",
		5:  "MsgVote",
		6:  "MsgVoteResp",
		7:  "MsgSnap",
		8:  "MsgHeartbeat",
		9:  "MsgHeartbeatResp",
		10: "MsgUnreachable",
		11: "MsgSnapStatus",
		12: "MsgCheckQuorum",
		13: "MsgTransferLeader",
		14: "MsgTimeoutNow",
		15: "MsgReadIndex",
		16: "MsgReadIndexResp",
		17: "MsgPreVote",
		18: "MsgPreVoteResp",
		19: "MsgStorageAppend",
		20: "MsgStorageAppendResp",
		21: "MsgStorageApply",
		22: "MsgStorageApplyResp",
		23: "MsgForgetLeader",
	}
	MessageType_value = map[string]int32{
		"MsgHup":               0,
		"MsgBeat":              1,
		"MsgProp":              2,
		"MsgApp":               3,
		"MsgAppResp":           4,
		"MsgVote":              5,
		"MsgVoteResp":          6,
		"MsgSnap":              7,
		"MsgHeartbeat":         8,
		"MsgHeartbeatResp":     9,
		"MsgUnreachable":       10,
		"MsgSnapStatus":        11,
		"MsgCheckQuorum":       12,
		"MsgTransferLeader":    13,
		"MsgTimeoutNow":        14,
		"MsgReadIndex":         15,
		"MsgReadIndexResp":     16,
		"MsgPreVote":           17,
		"MsgPreVoteResp":       18,
		"MsgStorageAppend":     19,
		"MsgStorageAppendResp": 20,
		"MsgStorageApply":      21,
		"MsgStorageApplyResp":  22,
		"MsgForgetLeader":      23,
	}
)

func (x MessageType) Enum() *MessageType {
	p := new(MessageType)
	*p = x
	return p
}

func (x MessageType) String() string {
	if s, ok := MessageType_name[int32(x)]; ok {
		return s
	}
	return plainpbEnumUnknown(int32(x))
}

func (x *MessageType) UnmarshalJSON(b []byte) error {
	panic("plainpb: MessageType.UnmarshalJSON is a fail-closed stub (protobuf runtime engineered out; docs/raft-w2-log.md)")
}

func (MessageType) EnumDescriptor() ([]byte, []int) {
	panic("plainpb: MessageType.EnumDescriptor is a fail-closed stub (protobuf runtime engineered out; docs/raft-w2-log.md)")
}

type ConfChangeTransition int32

const (
	// Automatically use the simple protocol if possible, otherwise fall back
	// to ConfChangeJointImplicit. Most applications will want to use this.
	ConfChangeTransition_ConfChangeTransitionAuto ConfChangeTransition = 0
	// Use joint consensus unconditionally, and transition out of them
	// automatically (by proposing a zero configuration change).
	//
	// This option is suitable for applications that want to minimize the time
	// spent in the joint configuration and do not store the joint configuration
	// in the state machine (outside of InitialState).
	ConfChangeTransition_ConfChangeTransitionJointImplicit ConfChangeTransition = 1
	// Use joint consensus and remain in the joint configuration until the
	// application proposes a no-op configuration change. This is suitable for
	// applications that want to explicitly control the transitions, for example
	// to use a custom payload (via the Context field).
	ConfChangeTransition_ConfChangeTransitionJointExplicit ConfChangeTransition = 2
)

var (
	ConfChangeTransition_name = map[int32]string{
		0: "ConfChangeTransitionAuto",
		1: "ConfChangeTransitionJointImplicit",
		2: "ConfChangeTransitionJointExplicit",
	}
	ConfChangeTransition_value = map[string]int32{
		"ConfChangeTransitionAuto":          0,
		"ConfChangeTransitionJointImplicit": 1,
		"ConfChangeTransitionJointExplicit": 2,
	}
)

func (x ConfChangeTransition) Enum() *ConfChangeTransition {
	p := new(ConfChangeTransition)
	*p = x
	return p
}

func (x ConfChangeTransition) String() string {
	if s, ok := ConfChangeTransition_name[int32(x)]; ok {
		return s
	}
	return plainpbEnumUnknown(int32(x))
}

func (x *ConfChangeTransition) UnmarshalJSON(b []byte) error {
	panic("plainpb: ConfChangeTransition.UnmarshalJSON is a fail-closed stub (protobuf runtime engineered out; docs/raft-w2-log.md)")
}

func (ConfChangeTransition) EnumDescriptor() ([]byte, []int) {
	panic("plainpb: ConfChangeTransition.EnumDescriptor is a fail-closed stub (protobuf runtime engineered out; docs/raft-w2-log.md)")
}

type ConfChangeType int32

const (
	ConfChangeType_ConfChangeAddNode        ConfChangeType = 0
	ConfChangeType_ConfChangeRemoveNode     ConfChangeType = 1
	ConfChangeType_ConfChangeUpdateNode     ConfChangeType = 2
	ConfChangeType_ConfChangeAddLearnerNode ConfChangeType = 3
)

var (
	ConfChangeType_name = map[int32]string{
		0: "ConfChangeAddNode",
		1: "ConfChangeRemoveNode",
		2: "ConfChangeUpdateNode",
		3: "ConfChangeAddLearnerNode",
	}
	ConfChangeType_value = map[string]int32{
		"ConfChangeAddNode":        0,
		"ConfChangeRemoveNode":     1,
		"ConfChangeUpdateNode":     2,
		"ConfChangeAddLearnerNode": 3,
	}
)

func (x ConfChangeType) Enum() *ConfChangeType {
	p := new(ConfChangeType)
	*p = x
	return p
}

func (x ConfChangeType) String() string {
	if s, ok := ConfChangeType_name[int32(x)]; ok {
		return s
	}
	return plainpbEnumUnknown(int32(x))
}

func (x *ConfChangeType) UnmarshalJSON(b []byte) error {
	panic("plainpb: ConfChangeType.UnmarshalJSON is a fail-closed stub (protobuf runtime engineered out; docs/raft-w2-log.md)")
}

func (ConfChangeType) EnumDescriptor() ([]byte, []int) {
	panic("plainpb: ConfChangeType.EnumDescriptor is a fail-closed stub (protobuf runtime engineered out; docs/raft-w2-log.md)")
}

type Entry struct {
	Term  *uint64    `protobuf:"varint,2,opt,name=Term" json:"Term,omitempty"`
	Index *uint64    `protobuf:"varint,3,opt,name=Index" json:"Index,omitempty"`
	Type  *EntryType `protobuf:"varint,1,opt,name=Type,enum=raftpb.EntryType" json:"Type,omitempty"`
	Data  []byte     `protobuf:"bytes,4,opt,name=Data" json:"Data,omitempty"`
}

func (x *Entry) Reset() {
	*x = Entry{}
}

func (x *Entry) String() string {
	panic("plainpb: Entry.String is a fail-closed stub (protobuf runtime engineered out; docs/raft-w2-log.md)")
}

func (*Entry) ProtoMessage() {}

func (*Entry) Descriptor() ([]byte, []int) {
	panic("plainpb: Entry.Descriptor is a fail-closed stub (protobuf runtime engineered out; docs/raft-w2-log.md)")
}

func (x *Entry) GetTerm() uint64 {
	if x != nil && x.Term != nil {
		return *x.Term
	}
	return 0
}

func (x *Entry) GetIndex() uint64 {
	if x != nil && x.Index != nil {
		return *x.Index
	}
	return 0
}

func (x *Entry) GetType() EntryType {
	if x != nil && x.Type != nil {
		return *x.Type
	}
	return EntryType_EntryNormal
}

func (x *Entry) GetData() []byte {
	if x != nil {
		return x.Data
	}
	return nil
}

type SnapshotMetadata struct {
	ConfState *ConfState `protobuf:"bytes,1,opt,name=conf_state,json=confState" json:"conf_state,omitempty"`
	Index     *uint64    `protobuf:"varint,2,opt,name=index" json:"index,omitempty"`
	Term      *uint64    `protobuf:"varint,3,opt,name=term" json:"term,omitempty"`
}

func (x *SnapshotMetadata) Reset() {
	*x = SnapshotMetadata{}
}

func (x *SnapshotMetadata) String() string {
	panic("plainpb: SnapshotMetadata.String is a fail-closed stub (protobuf runtime engineered out; docs/raft-w2-log.md)")
}

func (*SnapshotMetadata) ProtoMessage() {}

func (*SnapshotMetadata) Descriptor() ([]byte, []int) {
	panic("plainpb: SnapshotMetadata.Descriptor is a fail-closed stub (protobuf runtime engineered out; docs/raft-w2-log.md)")
}

func (x *SnapshotMetadata) GetConfState() *ConfState {
	if x != nil {
		return x.ConfState
	}
	return nil
}

func (x *SnapshotMetadata) GetIndex() uint64 {
	if x != nil && x.Index != nil {
		return *x.Index
	}
	return 0
}

func (x *SnapshotMetadata) GetTerm() uint64 {
	if x != nil && x.Term != nil {
		return *x.Term
	}
	return 0
}

type Snapshot struct {
	Data     []byte            `protobuf:"bytes,1,opt,name=data" json:"data,omitempty"`
	Metadata *SnapshotMetadata `protobuf:"bytes,2,opt,name=metadata" json:"metadata,omitempty"`
}

func (x *Snapshot) Reset() {
	*x = Snapshot{}
}

func (x *Snapshot) String() string {
	panic("plainpb: Snapshot.String is a fail-closed stub (protobuf runtime engineered out; docs/raft-w2-log.md)")
}

func (*Snapshot) ProtoMessage() {}

func (*Snapshot) Descriptor() ([]byte, []int) {
	panic("plainpb: Snapshot.Descriptor is a fail-closed stub (protobuf runtime engineered out; docs/raft-w2-log.md)")
}

func (x *Snapshot) GetData() []byte {
	if x != nil {
		return x.Data
	}
	return nil
}

func (x *Snapshot) GetMetadata() *SnapshotMetadata {
	if x != nil {
		return x.Metadata
	}
	return nil
}

type Message struct {
	Type *MessageType `protobuf:"varint,1,opt,name=type,enum=raftpb.MessageType" json:"type,omitempty"`
	To   *uint64      `protobuf:"varint,2,opt,name=to" json:"to,omitempty"`
	From *uint64      `protobuf:"varint,3,opt,name=from" json:"from,omitempty"`
	Term *uint64      `protobuf:"varint,4,opt,name=term" json:"term,omitempty"`
	// logTerm is generally used for appending Raft logs to followers. For example,
	// (type=MsgApp,index=100,logTerm=5) means the leader appends entries starting
	// at index=101, and the term of the entry at index 100 is 5.
	// (type=MsgAppResp,reject=true,index=100,logTerm=5) means follower rejects some
	// entries from its leader as it already has an entry with term 5 at index 100.
	// (type=MsgStorageAppendResp,index=100,logTerm=5) means the local node wrote
	// entries up to index=100 in stable storage, and the term of the entry at index
	// 100 was 5. This doesn't always mean that the corresponding MsgStorageAppend
	// message was the one that carried these entries, just that those entries were
	// stable at the time of processing the corresponding MsgStorageAppend.
	LogTerm *uint64  `protobuf:"varint,5,opt,name=logTerm" json:"logTerm,omitempty"`
	Index   *uint64  `protobuf:"varint,6,opt,name=index" json:"index,omitempty"`
	Entries []*Entry `protobuf:"bytes,7,rep,name=entries" json:"entries,omitempty"`
	Commit  *uint64  `protobuf:"varint,8,opt,name=commit" json:"commit,omitempty"`
	// (type=MsgStorageAppend,vote=5,term=10) means the local node is voting for
	// peer 5 in term 10. For MsgStorageAppends, the term, vote, and commit fields
	// will either all be set (to facilitate the construction of a HardState) if
	// any of the fields have changed or will all be unset if none of the fields
	// have changed.
	Vote *uint64 `protobuf:"varint,13,opt,name=vote" json:"vote,omitempty"`
	// snapshot is non-nil and non-empty for MsgSnap messages and nil for all other
	// message types. However, peer nodes running older binary versions may send a
	// non-nil, empty value for the snapshot field of non-MsgSnap messages. Code
	// should be prepared to handle such messages.
	Snapshot   *Snapshot `protobuf:"bytes,9,opt,name=snapshot" json:"snapshot,omitempty"`
	Reject     *bool     `protobuf:"varint,10,opt,name=reject" json:"reject,omitempty"`
	RejectHint *uint64   `protobuf:"varint,11,opt,name=rejectHint" json:"rejectHint,omitempty"`
	Context    []byte    `protobuf:"bytes,12,opt,name=context" json:"context,omitempty"`
	// responses are populated by a raft node to instruct storage threads on how
	// to respond and who to respond to when the work associated with a message
	// is complete. Populated for MsgStorageAppend and MsgStorageApply messages.
	Responses []*Message `protobuf:"bytes,14,rep,name=responses" json:"responses,omitempty"`
}

func (x *Message) Reset() {
	*x = Message{}
}

func (x *Message) String() string {
	panic("plainpb: Message.String is a fail-closed stub (protobuf runtime engineered out; docs/raft-w2-log.md)")
}

func (*Message) ProtoMessage() {}

func (*Message) Descriptor() ([]byte, []int) {
	panic("plainpb: Message.Descriptor is a fail-closed stub (protobuf runtime engineered out; docs/raft-w2-log.md)")
}

func (x *Message) GetType() MessageType {
	if x != nil && x.Type != nil {
		return *x.Type
	}
	return MessageType_MsgHup
}

func (x *Message) GetTo() uint64 {
	if x != nil && x.To != nil {
		return *x.To
	}
	return 0
}

func (x *Message) GetFrom() uint64 {
	if x != nil && x.From != nil {
		return *x.From
	}
	return 0
}

func (x *Message) GetTerm() uint64 {
	if x != nil && x.Term != nil {
		return *x.Term
	}
	return 0
}

func (x *Message) GetLogTerm() uint64 {
	if x != nil && x.LogTerm != nil {
		return *x.LogTerm
	}
	return 0
}

func (x *Message) GetIndex() uint64 {
	if x != nil && x.Index != nil {
		return *x.Index
	}
	return 0
}

func (x *Message) GetEntries() []*Entry {
	if x != nil {
		return x.Entries
	}
	return nil
}

func (x *Message) GetCommit() uint64 {
	if x != nil && x.Commit != nil {
		return *x.Commit
	}
	return 0
}

func (x *Message) GetVote() uint64 {
	if x != nil && x.Vote != nil {
		return *x.Vote
	}
	return 0
}

func (x *Message) GetSnapshot() *Snapshot {
	if x != nil {
		return x.Snapshot
	}
	return nil
}

func (x *Message) GetReject() bool {
	if x != nil && x.Reject != nil {
		return *x.Reject
	}
	return false
}

func (x *Message) GetRejectHint() uint64 {
	if x != nil && x.RejectHint != nil {
		return *x.RejectHint
	}
	return 0
}

func (x *Message) GetContext() []byte {
	if x != nil {
		return x.Context
	}
	return nil
}

func (x *Message) GetResponses() []*Message {
	if x != nil {
		return x.Responses
	}
	return nil
}

type HardState struct {
	Term   *uint64 `protobuf:"varint,1,opt,name=term" json:"term,omitempty"`
	Vote   *uint64 `protobuf:"varint,2,opt,name=vote" json:"vote,omitempty"`
	Commit *uint64 `protobuf:"varint,3,opt,name=commit" json:"commit,omitempty"`
}

func (x *HardState) Reset() {
	*x = HardState{}
}

func (x *HardState) String() string {
	panic("plainpb: HardState.String is a fail-closed stub (protobuf runtime engineered out; docs/raft-w2-log.md)")
}

func (*HardState) ProtoMessage() {}

func (*HardState) Descriptor() ([]byte, []int) {
	panic("plainpb: HardState.Descriptor is a fail-closed stub (protobuf runtime engineered out; docs/raft-w2-log.md)")
}

func (x *HardState) GetTerm() uint64 {
	if x != nil && x.Term != nil {
		return *x.Term
	}
	return 0
}

func (x *HardState) GetVote() uint64 {
	if x != nil && x.Vote != nil {
		return *x.Vote
	}
	return 0
}

func (x *HardState) GetCommit() uint64 {
	if x != nil && x.Commit != nil {
		return *x.Commit
	}
	return 0
}

type ConfState struct {
	// The voters in the incoming config. (If the configuration is not joint,
	// then the outgoing config is empty).
	Voters []uint64 `protobuf:"varint,1,rep,name=voters" json:"voters,omitempty"`
	// The learners in the incoming config.
	Learners []uint64 `protobuf:"varint,2,rep,name=learners" json:"learners,omitempty"`
	// The voters in the outgoing config.
	VotersOutgoing []uint64 `protobuf:"varint,3,rep,name=voters_outgoing,json=votersOutgoing" json:"voters_outgoing,omitempty"`
	// The nodes that will become learners when the outgoing config is removed.
	// These nodes are necessarily currently in nodes_joint (or they would have
	// been added to the incoming config right away).
	LearnersNext []uint64 `protobuf:"varint,4,rep,name=learners_next,json=learnersNext" json:"learners_next,omitempty"`
	// If set, the config is joint and Raft will automatically transition into
	// the final config (i.e. remove the outgoing config) when this is safe.
	AutoLeave *bool `protobuf:"varint,5,opt,name=auto_leave,json=autoLeave" json:"auto_leave,omitempty"`
}

func (x *ConfState) Reset() {
	*x = ConfState{}
}

func (x *ConfState) String() string {
	panic("plainpb: ConfState.String is a fail-closed stub (protobuf runtime engineered out; docs/raft-w2-log.md)")
}

func (*ConfState) ProtoMessage() {}

func (*ConfState) Descriptor() ([]byte, []int) {
	panic("plainpb: ConfState.Descriptor is a fail-closed stub (protobuf runtime engineered out; docs/raft-w2-log.md)")
}

func (x *ConfState) GetVoters() []uint64 {
	if x != nil {
		return x.Voters
	}
	return nil
}

func (x *ConfState) GetLearners() []uint64 {
	if x != nil {
		return x.Learners
	}
	return nil
}

func (x *ConfState) GetVotersOutgoing() []uint64 {
	if x != nil {
		return x.VotersOutgoing
	}
	return nil
}

func (x *ConfState) GetLearnersNext() []uint64 {
	if x != nil {
		return x.LearnersNext
	}
	return nil
}

func (x *ConfState) GetAutoLeave() bool {
	if x != nil && x.AutoLeave != nil {
		return *x.AutoLeave
	}
	return false
}

type ConfChange struct {
	Type    *ConfChangeType `protobuf:"varint,2,opt,name=type,enum=raftpb.ConfChangeType" json:"type,omitempty"`
	NodeId  *uint64         `protobuf:"varint,3,opt,name=node_id,json=nodeId" json:"node_id,omitempty"`
	Context []byte          `protobuf:"bytes,4,opt,name=context" json:"context,omitempty"`
	// NB: this is used only by etcd to thread through a unique identifier.
	// Ideally it should really use the Context instead. No counterpart to
	// this field exists in ConfChangeV2.
	Id *uint64 `protobuf:"varint,1,opt,name=id" json:"id,omitempty"`
}

func (x *ConfChange) Reset() {
	*x = ConfChange{}
}

func (x *ConfChange) String() string {
	panic("plainpb: ConfChange.String is a fail-closed stub (protobuf runtime engineered out; docs/raft-w2-log.md)")
}

func (*ConfChange) ProtoMessage() {}

func (*ConfChange) Descriptor() ([]byte, []int) {
	panic("plainpb: ConfChange.Descriptor is a fail-closed stub (protobuf runtime engineered out; docs/raft-w2-log.md)")
}

func (x *ConfChange) GetType() ConfChangeType {
	if x != nil && x.Type != nil {
		return *x.Type
	}
	return ConfChangeType_ConfChangeAddNode
}

func (x *ConfChange) GetNodeId() uint64 {
	if x != nil && x.NodeId != nil {
		return *x.NodeId
	}
	return 0
}

func (x *ConfChange) GetContext() []byte {
	if x != nil {
		return x.Context
	}
	return nil
}

func (x *ConfChange) GetId() uint64 {
	if x != nil && x.Id != nil {
		return *x.Id
	}
	return 0
}

type ConfChangeSingle struct {
	Type   *ConfChangeType `protobuf:"varint,1,opt,name=type,enum=raftpb.ConfChangeType" json:"type,omitempty"`
	NodeId *uint64         `protobuf:"varint,2,opt,name=node_id,json=nodeId" json:"node_id,omitempty"`
}

func (x *ConfChangeSingle) Reset() {
	*x = ConfChangeSingle{}
}

func (x *ConfChangeSingle) String() string {
	panic("plainpb: ConfChangeSingle.String is a fail-closed stub (protobuf runtime engineered out; docs/raft-w2-log.md)")
}

func (*ConfChangeSingle) ProtoMessage() {}

func (*ConfChangeSingle) Descriptor() ([]byte, []int) {
	panic("plainpb: ConfChangeSingle.Descriptor is a fail-closed stub (protobuf runtime engineered out; docs/raft-w2-log.md)")
}

func (x *ConfChangeSingle) GetType() ConfChangeType {
	if x != nil && x.Type != nil {
		return *x.Type
	}
	return ConfChangeType_ConfChangeAddNode
}

func (x *ConfChangeSingle) GetNodeId() uint64 {
	if x != nil && x.NodeId != nil {
		return *x.NodeId
	}
	return 0
}

type ConfChangeV2 struct {
	Transition *ConfChangeTransition `protobuf:"varint,1,opt,name=transition,enum=raftpb.ConfChangeTransition" json:"transition,omitempty"`
	Changes    []*ConfChangeSingle   `protobuf:"bytes,2,rep,name=changes" json:"changes,omitempty"`
	Context    []byte                `protobuf:"bytes,3,opt,name=context" json:"context,omitempty"`
}

func (x *ConfChangeV2) Reset() {
	*x = ConfChangeV2{}
}

func (x *ConfChangeV2) String() string {
	panic("plainpb: ConfChangeV2.String is a fail-closed stub (protobuf runtime engineered out; docs/raft-w2-log.md)")
}

func (*ConfChangeV2) ProtoMessage() {}

func (*ConfChangeV2) Descriptor() ([]byte, []int) {
	panic("plainpb: ConfChangeV2.Descriptor is a fail-closed stub (protobuf runtime engineered out; docs/raft-w2-log.md)")
}

func (x *ConfChangeV2) GetTransition() ConfChangeTransition {
	if x != nil && x.Transition != nil {
		return *x.Transition
	}
	return ConfChangeTransition_ConfChangeTransitionAuto
}

func (x *ConfChangeV2) GetChanges() []*ConfChangeSingle {
	if x != nil {
		return x.Changes
	}
	return nil
}

func (x *ConfChangeV2) GetContext() []byte {
	if x != nil {
		return x.Context
	}
	return nil
}

// plainpbEnumUnknown renders an out-of-range enum value the way the
// protobuf runtime's EnumStringOf fallback does: the decimal number.
// Unreachable for every value the name maps carry.
func plainpbEnumUnknown(v int32) string {
	if v == 0 {
		return "0"
	}
	neg := v < 0
	u := uint32(v)
	if neg {
		u = uint32(-int64(v))
	}
	s := ""
	for u > 0 {
		s = string(rune('0'+int(u%10))) + s
		u /= 10
	}
	if neg {
		s = "-" + s
	}
	return s
}
