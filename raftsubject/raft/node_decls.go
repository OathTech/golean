package raft

import (
	"errors"

	pb "raftpb"
)

type SnapshotStatus int

const (
	SnapshotFinish  SnapshotStatus = 1
	SnapshotFailure SnapshotStatus = 2
)

var (
	emptyState = &pb.HardState{}

	// ErrStopped is returned by methods on Nodes that have been stopped.
	ErrStopped = errors.New("raft: stopped")
)

type SoftState struct {
	Lead      uint64 // must use atomic operations to access; keep 64-bit aligned.
	RaftState StateType
}

func (a *SoftState) equal(b *SoftState) bool {
	return a.Lead == b.Lead && a.RaftState == b.RaftState
}

type Ready struct {
	// The current volatile state of a Node.
	// SoftState will be nil if there is no update.
	// It is not required to consume or store SoftState.
	*SoftState

	// The current state of a Node to be saved to stable storage BEFORE
	// Messages are sent.
	//
	// HardState will be nil if there is no update.
	//
	// If async storage writes are enabled, this field does not need to be acted
	// on immediately. It will be reflected in a MsgStorageAppend message in the
	// Messages slice.
	*pb.HardState

	// ReadStates can be used for node to serve linearizable read requests locally
	// when its applied index is greater than the index in ReadState.
	// Note that the readState will be returned when raft receives msgReadIndex.
	// The returned is only valid for the request that requested to read.
	ReadStates []ReadState

	// Entries specifies entries to be saved to stable storage BEFORE
	// Messages are sent.
	//
	// If async storage writes are enabled, this field does not need to be acted
	// on immediately. It will be reflected in a MsgStorageAppend message in the
	// Messages slice.
	Entries []*pb.Entry

	// Snapshot specifies the snapshot to be saved to stable storage.
	//
	// If async storage writes are enabled, this field does not need to be acted
	// on immediately. It will be reflected in a MsgStorageAppend message in the
	// Messages slice.
	Snapshot *pb.Snapshot

	// CommittedEntries specifies entries to be committed to a
	// store/state-machine. These have previously been appended to stable
	// storage.
	//
	// If async storage writes are enabled, this field does not need to be acted
	// on immediately. It will be reflected in a MsgStorageApply message in the
	// Messages slice.
	CommittedEntries []*pb.Entry

	// Messages specifies outbound messages.
	//
	// If async storage writes are not enabled, these messages must be sent
	// AFTER Entries are appended to stable storage.
	//
	// If async storage writes are enabled, these messages can be sent
	// immediately as the messages that have the completion of the async writes
	// as a precondition are attached to the individual MsgStorage{Append,Apply}
	// messages instead.
	//
	// If it contains a MsgSnap message, the application MUST report back to raft
	// when the snapshot has been received or has failed by calling ReportSnapshot.
	Messages []*pb.Message

	// MustSync indicates whether the HardState and Entries must be durably
	// written to disk or if a non-durable write is permissible.
	MustSync bool
}

func isHardStateEqual(a, b *pb.HardState) bool {
	return a.GetTerm() == b.GetTerm() && a.GetVote() == b.GetVote() && a.GetCommit() == b.GetCommit()
}

func IsEmptyHardState(st *pb.HardState) bool {
	return st == nil || isHardStateEqual(st, emptyState)
}

func IsEmptySnap(sp *pb.Snapshot) bool {
	return sp.GetMetadata().GetIndex() == 0
}

type Peer struct {
	ID      uint64
	Context []byte
}

func confChangeToMsg(c pb.ConfChangeI) (*pb.Message, error) {
	typ, data, err := pb.MarshalConfChange(c)
	if err != nil {
		return nil, err
	}
	return &pb.Message{Type: pb.MsgProp.Enum(), Entries: []*pb.Entry{{Type: typ.Enum(), Data: data}}}, nil
}
