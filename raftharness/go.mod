module golean.local/raftharness

go 1.26

require go.etcd.io/raft/v3 v3.0.0-00010101000000-000000000000

require google.golang.org/protobuf v1.36.11

replace go.etcd.io/raft/v3 => ../deps/raft
