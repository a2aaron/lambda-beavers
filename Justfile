#
benchmark:
    cargo nextest run --release --profile strong-only --features strong-only

test:
    cargo nextest run --release --no-fail-fast