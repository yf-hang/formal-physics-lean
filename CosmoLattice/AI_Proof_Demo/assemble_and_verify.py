"""Backward-compatible entry point for verifying an existing completion."""

from ai_prove import main


if __name__ == "__main__":
    raise SystemExit(main(["--verify-only"]))
