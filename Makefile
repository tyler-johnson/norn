# Daily driver: `make` = fast dogfood build; ~/.cargo/bin/norn symlinks to
# target/dogfood/norn, so the driver is live the moment it links.
# `make release` is the honest fat-LTO build.

.PHONY: build release test bless install clean

build:
	cargo build --profile dogfood

release:
	cargo build --release

test:
	cargo test

# Rewrite the parser snapshot corpus. Read the diff before committing it --
# a blessed snapshot is an assertion that the new output is what you meant.
bless:
	NORN_BLESS=1 cargo test

# Point ~/.cargo/bin/norn at the dogfood binary. Idempotent; rerun after a move.
install: build
	@mkdir -p $(HOME)/.cargo/bin
	ln -sfn $(CURDIR)/target/dogfood/norn $(HOME)/.cargo/bin/norn
	@echo "linked $(HOME)/.cargo/bin/norn -> $(CURDIR)/target/dogfood/norn"

clean:
	cargo clean
