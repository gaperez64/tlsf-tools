#!/bin/sh
# AbsSynthe stand-in that never terminates, so the caller's $ABSSYNTHE_TIMEOUT
# wall-clock cap fires and the cluster falls back.  `exec` so the kill lands on
# this process directly (no orphaned sleep).
exec sleep 30
