#!/usr/bin/env python3
"""DISABLED. This Bash hygiene gate was removed by user request.

It used to force a permission prompt (or silent deny) for any Bash command not on a
hardcoded allowlist. That behavior is gone. Bash is now governed ONLY by settings.json's
allow/deny lists (the deny list is the safety boundary). This file is kept as an inert
no-op so any lingering settings reference to it can't error/block; it may be deleted after
a session restart once no settings.json references it.

Contract: read stdin, do nothing, exit 0 (never gate)."""
import sys

def main():
    try:
        sys.stdin.read()
    except Exception:
        pass
    sys.exit(0)

if __name__ == "__main__":
    main()
