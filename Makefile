# Daily driver: `make` = fast dogfood build; ~/.cargo/bin/norn symlinks to
# target/dogfood/norn, so the driver is live the moment it links.
# `make release` is the honest fat-LTO build.

.PHONY: build release test bless fmt fmt-check install editor-install editor-package clean

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

# Default rustfmt, no rustfmt.toml -- the style is whatever the toolchain says,
# so it never becomes something to argue about in review.
fmt:
	cargo fmt

fmt-check:
	cargo fmt --check

# Point ~/.cargo/bin/norn at the dogfood binary. Idempotent; rerun after a move.
install: build
	@mkdir -p $(HOME)/.cargo/bin
	ln -sfn $(CURDIR)/target/dogfood/norn $(HOME)/.cargo/bin/norn
	@echo "linked $(HOME)/.cargo/bin/norn -> $(CURDIR)/target/dogfood/norn"

# Link the VS Code extension into place. A symlink rather than a copy, so editing the grammar and
# reloading the window is the whole edit loop. See editors/vscode/README.md for other editor
# layouts (~/.vscode-server over SSH, ~/.vscode-oss on VSCodium).
editor-install:
	@mkdir -p $(HOME)/.vscode/extensions
	ln -sfn $(CURDIR)/editors/vscode $(HOME)/.vscode/extensions/norn-lang.norn
	@echo "linked; run \"Developer: Reload Window\" to pick it up"

# Build a .vsix. Needs npm, which nothing else here does.
editor-package:
	cd editors/vscode && npx --yes @vscode/vsce package --out norn.vsix

clean:
	cargo clean
