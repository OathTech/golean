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

package raft

import (
	"fmt"
	"log"
	"os"
	"sync"
)

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

// GOLEAN SUBJECT DELTA D-12 (the Q2 logger ruling — docs/raft-w42-log.md
// item 1): the two initializers lose their `log.New(...)` calls, which do
// not lower. The harness installs its own Logger through BOTH seams before
// any node exists; a pre-install Logger call under `go run` nil-derefs
// loudly instead of printing.
//
// NOT retired by H-11 (which shipped in W4.0). H-11's per-declaration
// quarantine is gated on `initializerEffectIsolated`, which refuses this
// initializer on three independent axes: the `&`-composite shape, `log.New`
// being outside `pureUnmodeledCallees` (kept minimal by audit F1 — an
// unmodeled call is NOT effect-free), and `os.Stderr`/`io.Discard` failing
// `isolatedType`. Retiring D-12 needs a writer-typed-global effect story:
// handoff H-20. See tools/raftsubject/derive.py for the full argument.
var (
	defaultLogger = &DefaultLogger{}
	discardLogger = &DefaultLogger{}
	raftLoggerMu  sync.Mutex
	raftLogger    = Logger(defaultLogger)
)

const (
	calldepth = 2
)

// DefaultLogger is a default implementation of the Logger interface.
type DefaultLogger struct {
	*log.Logger
	debug bool
}

func (l *DefaultLogger) EnableTimestamps() {
	l.SetFlags(l.Flags() | log.Ldate | log.Ltime)
}

func (l *DefaultLogger) EnableDebug() {
	l.debug = true
}

func (l *DefaultLogger) Debug(v ...any) {
	if l.debug {
		l.Output(calldepth, header("DEBUG", fmt.Sprint(v...)))
	}
}

func (l *DefaultLogger) Debugf(format string, v ...any) {
	if l.debug {
		l.Output(calldepth, header("DEBUG", fmt.Sprintf(format, v...)))
	}
}

func (l *DefaultLogger) Info(v ...any) {
	l.Output(calldepth, header("INFO", fmt.Sprint(v...)))
}

func (l *DefaultLogger) Infof(format string, v ...any) {
	l.Output(calldepth, header("INFO", fmt.Sprintf(format, v...)))
}

func (l *DefaultLogger) Error(v ...any) {
	l.Output(calldepth, header("ERROR", fmt.Sprint(v...)))
}

func (l *DefaultLogger) Errorf(format string, v ...any) {
	l.Output(calldepth, header("ERROR", fmt.Sprintf(format, v...)))
}

func (l *DefaultLogger) Warning(v ...any) {
	l.Output(calldepth, header("WARN", fmt.Sprint(v...)))
}

func (l *DefaultLogger) Warningf(format string, v ...any) {
	l.Output(calldepth, header("WARN", fmt.Sprintf(format, v...)))
}

func (l *DefaultLogger) Fatal(v ...any) {
	l.Output(calldepth, header("FATAL", fmt.Sprint(v...)))
	os.Exit(1)
}

func (l *DefaultLogger) Fatalf(format string, v ...any) {
	l.Output(calldepth, header("FATAL", fmt.Sprintf(format, v...)))
	os.Exit(1)
}

func (l *DefaultLogger) Panic(v ...any) {
	l.Logger.Panic(v...)
}

func (l *DefaultLogger) Panicf(format string, v ...any) {
	l.Logger.Panicf(format, v...)
}

func header(lvl, msg string) string {
	return fmt.Sprintf("%s: %s", lvl, msg)
}
