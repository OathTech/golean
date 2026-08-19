// Copyright 2015 The etcd Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// OVERLAY (tools/raftsubject/overlay/raft/logger.go) — the W2.2 NO-OP LOGGER
// INJECTION (master plan §W2.2, scoping §7 layer B "Logging"). Upstream
// raft/logger.go's SHA-256 is pinned in tools/raftsubject/derive.py, so a pin
// move that changes the Logger interface fails the derivation loud.
//
// WHY AN OVERLAY AND NOT A VENDOR. Upstream's file is the Logger INTERFACE
// (pure declaration, portable) plus DefaultLogger, an implementation over
// `log`, `os`, `io` and `fmt` — four packages that are never interpreted
// (impure/runtime-touching, standing library policy). raft calls the logger
// from its normal paths, so it cannot simply be quarantined: it has to be
// REPLACED behind a seam the library already provides, which is exactly what
// the Logger interface is. Injecting a no-op is the seam's intended use, not
// a workaround.
//
// SUBJECT DELTA, itemised (docs/raft-w2-log.md, subject-delta ledger):
//
//  1. The `Logger` interface is upstream VERBATIM — twelve methods, same
//     names, same signatures. Any raft call site type-checks unchanged.
//  2. `DefaultLogger` (the `*log.Logger`-backed implementation, its
//     EnableDebug/EnableTimestamps knobs, and the `header` helper) is
//     REPLACED by `noopLogger`: twelve empty bodies. Imports `fmt`, `io`,
//     `log`, `os` disappear entirely.
//  3. `defaultLogger` and `discardLogger` both become the no-op, so
//     `ResetDefaultLogger()` restores the no-op rather than a stderr logger.
//  4. `os.Exit(1)` in Fatal/Fatalf is DROPPED, and `Panic`/`Panicf` no
//     longer panic. This is the one delta with observable weight: upstream
//     Fatal terminates the process and Panic panics. Rationale and the
//     honest cost are argued in the log; the short form is that both are
//     RENDERING-COUPLED aborts (they exist to print a message and die) and
//     raft reaches them only on states it treats as impossible. Keeping the
//     abort without the message would be a bare `panic("")`, which the
//     differential could not distinguish from a genuine one. The abort
//     behaviour is a recorded handoff item, not a settled question.
//  5. `raftLoggerMu sync.Mutex` is KEPT: `sync.Mutex` is modeled
//     (docs/2026-08-09_sync-package-design.md), SetLogger/getLogger race
//     under the concurrent twin, and dropping it would be a
//     concurrency-semantics delta smuggled in as a convenience.

package raft

import "sync"

type Logger interface {
	Debug(v ...any)
	Debugf(format string, v ...any)

	Error(v ...any)
	Errorf(format string, v ...any)

	Info(v ...any)
	Infof(format string, v ...any)

	Warning(v ...any)
	Warningf(format string, v ...any)

	Fatal(v ...any)
	Fatalf(format string, v ...any)

	Panic(v ...any)
	Panicf(format string, v ...any)
}

func SetLogger(l Logger) {
	raftLoggerMu.Lock()
	raftLogger = l
	raftLoggerMu.Unlock()
}

func ResetDefaultLogger() {
	SetLogger(defaultLogger)
}

func getLogger() Logger {
	raftLoggerMu.Lock()
	defer raftLoggerMu.Unlock()
	return raftLogger
}

var (
	defaultLogger = &noopLogger{}
	discardLogger = &noopLogger{}
	raftLoggerMu  sync.Mutex
	raftLogger    = Logger(defaultLogger)
)

// noopLogger is the injected no-op implementation of Logger (delta 2): every
// method is empty, so no rendering path is reachable through the logger seam
// and no format string is ever evaluated.
type noopLogger struct{}

func (l *noopLogger) Debug(v ...any)                   {}
func (l *noopLogger) Debugf(format string, v ...any)   {}
func (l *noopLogger) Info(v ...any)                    {}
func (l *noopLogger) Infof(format string, v ...any)    {}
func (l *noopLogger) Error(v ...any)                   {}
func (l *noopLogger) Errorf(format string, v ...any)   {}
func (l *noopLogger) Warning(v ...any)                 {}
func (l *noopLogger) Warningf(format string, v ...any) {}
func (l *noopLogger) Fatal(v ...any)                   {}
func (l *noopLogger) Fatalf(format string, v ...any)   {}
func (l *noopLogger) Panic(v ...any)                   {}
func (l *noopLogger) Panicf(format string, v ...any)   {}
