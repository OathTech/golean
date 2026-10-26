#!/bin/sh
# a -toolexec wrapper that dies on SIGKILL before running the tool (the compiler/linker child killed mid-run)
kill -9 $$
