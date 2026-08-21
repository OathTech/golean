// Package mpb: the mini-raft wire types (W4.3 item 4, the owed
// twin-family corpus rows — docs/raft-w43-log.md). A raft-SHAPED
// multipkg pin: named message-type enum with a name table, pointer
// message structs in a shared bag — the plainpb language shape in
// miniature, self-contained (the corpus never vendors the subject).
package mpb

type MsgType int32

const (
	MsgVote     MsgType = 0
	MsgVoteResp MsgType = 1
	MsgApp      MsgType = 2
	MsgAppResp  MsgType = 3
)

var msgTypeName = map[int32]string{
	0: "MsgVote",
	1: "MsgVoteResp",
	2: "MsgApp",
	3: "MsgAppResp",
}

func (t MsgType) String() string {
	if s, ok := msgTypeName[int32(t)]; ok {
		return s
	}
	return "?"
}

type Entry struct {
	Term uint64
	Data string
}

type Message struct {
	Type    MsgType
	From    uint64
	To      uint64
	Term    uint64
	Index   uint64 // Vote: candidate lastIndex; App: prevIndex; AppResp: acked index
	Entries []Entry
	Commit  uint64
	Granted bool
}
