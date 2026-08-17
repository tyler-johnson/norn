# Norn for VS Code

Syntax highlighting, a language configuration, and snippets for `.norn` files, plus a problem
matcher that turns `norn check` output into squiggles. No language server yet — see
[Toward a language server](#toward-a-language-server).

## Install

```
make editor-install
```

from the repository root, then reload the window (`Developer: Reload Window`). Any `.norn` file will
be coloured. Rerun it after moving the checkout.

It symlinks this directory into every extensions root it finds — `~/.vscode`, `~/.vscode-server`,
`~/.vscode-oss`, `~/.cursor-server` — because which one is live depends on how the window was
opened, not on which editor you installed. A local window reads `~/.vscode/extensions`; a Remote-SSH
window reads `~/.vscode-server/extensions` on the machine it connected to, which is why installing
into the obvious one and finding nothing coloured is the usual first surprise. If your editor keeps
them somewhere else again, the whole install is one line:

```
ln -sfn "$PWD/editors/vscode" <that directory>/norn-lang.norn
```

Linking is not the whole of an install, which is why `register.py` runs alongside it. VS Code keeps
`extensions.json` beside the extension folders as the record of what is installed there, and writes
it when something is installed or uninstalled rather than when the folder is scanned. A folder it
does not list does not exist; a version it lists that disagrees with `package.json` leaves the
extension asking to be restarted, and no restart resolves it, because nothing that runs at startup
rewrites that file. Both failures look like grammar bugs rather than install ones.

The manifest sets `"extensionKind": ["workspace"]` for a related reason. This extension is
declarative — a grammar, snippets, and a language configuration, with no `main` — and VS Code's
default for such an extension is `["ui", "workspace"]`, which over Remote-SSH means the copy on your
*client* wins and the symlink on the server is never read. The symptom is a grammar frozen at
whenever you last installed locally: keywords the language had then still colour, and everything
added since renders as a plain identifier. Pinning the kind makes the remote install the only
eligible one, and in a local window "workspace" is the local machine, so nothing is lost.

To build a `.vsix` instead, `make editor-package` (needs `npm`).

## What it knows

**Capitalization carries no meaning in Norn.** `Profile` and `profile` are the same kind of name;
only the `#` mark separates building data from calling a function, and only *position* separates a
type from a value. So the grammar finds types positionally rather than by case: inside a parameter
list — a `fn`'s or a `reactor`'s — after `->`, inside a `record` or `enum` body, and after the
colon of an `input`, `state`, or `signal` declaration. A named argument — `#User(id: 7)` — is
lexically identical to a field declaration, so outside those contexts nothing is guessed at, and
`id` stays an ordinary name rather than being mis-coloured as a type.

Beyond that:

- `task`, `await`, `scope`, and `spawn` share a scope, so suspension and structured concurrency read
  as one family.
- Capability names inside `uses { … }` are highlighted as constants. The grammar colours whatever is
  written rather than checking it against the v0 vocabulary — the checker owns that list and names
  the three when you get it wrong.
- `reactor`, `input`, `state`, `signal`, `on`, `after`, and `export` colour as the declarations
  they are, and a reactor's members read as members rather than as calls: `reactor Gate(…)` names a
  type, `on opened(…)` names the input it answers, and `after work() -> settled` colours `settled`
  as the input the result comes back on rather than as a return type.
- The queue clause `[capacity: 64, overflow: reject]` is anchored on its bracket, so `capacity` and
  `overflow` colour as the attributes they are there and stay ordinary names everywhere else —
  they are contextual words, not reserved ones. The four overflow policies colour as constants,
  because that vocabulary is closed.
- Reserved words (`loop`, `event`, `for`, `while`, and the rest of `lex.rs`'s list) are marked
  `invalid.illegal`, in binding positions too. `let event = 1` is an error, and the editor says so
  before the compiler has to.
- `2.seconds` is a projection off an integer; `2.5` is a float. The grammar splits them the same way
  the lexer does — a dot begins a fraction only when a digit follows it.
- Block comments nest.

`crates/norn-hir/tests/editor.rs` asserts that every keyword, reserved word, and builtin the front
end knows appears in this grammar, so a word added to the language cannot be silently forgotten
here. It checks membership rather than placement, which is the half a test can cheaply own; the
other half is checked by hand, by running the example corpus through `vscode-textmate` itself and
diffing the tokens against the previous grammar. Nothing from that check is committed — it needs
npm, and the workspace has no dependencies.

## Diagnostics

The extension contributes a `$norn` problem matcher for the driver's `file:line:col` diagnostic
format. The repository's `.vscode/tasks.json` wires it up:

- **norn: check this file** — the default build task (`Ctrl+Shift+B`); errors land in the Problems
  panel with squiggles in the editor.
- **norn: check the examples**, **norn: run this file** (under the virtual clock, with the event
  trace), **norn: graph this file** (the reactor's nodes, slots, propagation order, and per-input
  plans), **norn: format this file**.

These shell out to `cargo run --profile dogfood`, so they work in a fresh checkout without
installing the driver first. `make install` puts `norn` on your `PATH` if you would rather the tasks
call it directly.

## Toward a language server

The front end already produces everything a diagnostics server needs: `norn_hir::check` returns
spanned `Diagnostic`s, and `SourceFile::line_col` converts a byte offset to a position. A
`crates/norn-lsp` would be LSP framing over stdio, a document store, and that mapping — no new
analysis.

What comes after, roughly in order of how much of it already exists:

- **Semantic tokens** would replace the positional type-finding above with the real answer, since
  the checker knows which names are types. Until then this grammar is the approximation, and the two
  are meant to agree.
- **Hover** and **go to definition** from the typed HIR, which already resolves every name to an
  index and gives every expression a type.
- **Formatting** from `norn fmt`, which is `print::module` and already canonical.
- **Inlay hints** for inferred `let` types, and for the capability set a `task fn` actually needs.

Until then, keep the grammar and the lexer in step; the test above is what enforces it.
