package limits

// MaxRetries is an untyped integer constant.
const MaxRetries = 7

// Budget is a defined type; DefaultBudget a typed constant of it.
type Budget int64

const DefaultBudget Budget = 100

// The iota chain mirrors raft's StateType constants.
const (
	StateFollower = iota
	StateCandidate
	StateLeader
)
