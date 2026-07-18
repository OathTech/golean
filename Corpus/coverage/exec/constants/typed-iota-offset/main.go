package main

// quorum's VoteResult constants: a typed iota block starting at 1 + iota on a
// defined uint8 type (VotePending=1, VoteLost=2, VoteWon=3).

type voteResult uint8

const (
	votePending voteResult = 1 + iota
	voteLost
	voteWon
)

func typedIotaOffset() int {
	return int(votePending)*100 + int(voteLost)*10 + int(voteWon)
}
