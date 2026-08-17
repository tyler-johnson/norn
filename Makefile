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

# Link the VS Code extension into every extensions directory that exists. A symlink rather than a
# copy, so editing the grammar and reloading the window is the whole edit loop. Both roots get it
# because which one is live depends on how the window was opened: a local window reads ~/.vscode,
# and a Remote-SSH window reads ~/.vscode-server on the machine it connected to.
EDITOR_ROOTS = $(HOME)/.vscode $(HOME)/.vscode-server $(HOME)/.vscode-oss $(HOME)/.cursor-server

editor-install:
	@found=0; \
	for root in $(EDITOR_ROOTS); do \
		[ -d "$$root" ] || continue; \
		mkdir -p "$$root/extensions"; \
		ln -sfn $(CURDIR)/editors/vscode "$$root/extensions/norn-lang.norn"; \
		echo "linked $$root/extensions/norn-lang.norn"; \
		found=1; \
	done; \
	if [ $$found -eq 0 ]; then \
		echo "no editor directory found; link editors/vscode into yours by hand" >&2; \
		exit 1; \
	fi
	@echo "run \"Developer: Reload Window\" to pick it up"

# Build a .vsix. Needs npm, which nothing else here does.
editor-package:
	cd editors/vscode && npx --yes @vscode/vsce package --out norn.vsix

clean:
	cargo clean
