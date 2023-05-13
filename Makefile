.PHONY: dev
dev:
	cargo clippy
	cargo fmt
	cargo doc --no-deps --document-private-items
	cargo build

.PHONY: test
test:
	cargo test
	cargo miri test --tests
