//! The module loader: from an entry file to the parsed module graph.
//!
//! Filesystem-free behind a read callback, because the loader's consumers are not all the CLI —
//! the norn-nir and norn-codegen test crates drive it too, and a test crate cannot depend on a
//! binary. The CLI hands it `std::fs::read_to_string`; a test can hand it anything.
//!
//! Discovery is a worklist: the entry first, then each file's imports in written order, first
//! sighting wins — so module order, and with it every `FnId`, is a function of file contents
//! alone. Keys are lexically normalized (`./a/../fmt` ≡ `./fmt`, shared with the checker through
//! `resolve_specifier`); symlink aliasing is a documented v0 gap. A `std/…` specifier resolves
//! against the table embedded in `stdlib` rather than the filesystem: a hit parses the embedded
//! text, a miss is diagnosed here without touching `read`. Path *policy* — non-std bare
//! specifiers, a written `.norn`, self-imports — is the checker's, so those are skipped here
//! without comment. A file that fails to parse is reported but its import list is not walked: a
//! recovered AST's imports are not trustworthy. Loading continues elsewhere.

use std::collections::HashMap;

use norn_syntax::ast;
use norn_syntax::{Diagnostic, SourceFile, parse};

use crate::check::{Resolved, resolve_specifier};
use crate::stdlib;

pub struct Loaded {
    /// The entry module first, then the rest in discovery order.
    pub modules: Vec<LoadedModule>,
    /// Parse errors and missing files, each attributed to a module index — a missing file is the
    /// *importing* file's diagnostic, since the missing one has no text to point into.
    pub errors: Vec<(usize, Diagnostic)>,
}

impl Loaded {
    pub fn ok(&self) -> bool {
        self.errors.is_empty()
    }
}

pub struct LoadedModule {
    /// What diagnostics print. The loader uses the key for both.
    pub name: String,
    /// The lexically-normalized resolution identity import specifiers resolve to.
    pub key: String,
    pub file: SourceFile,
    pub module: ast::Module,
}

/// Load the module graph rooted at `entry`. `Err` means the entry itself could not be read —
/// there is nothing to attribute a diagnostic to; every later failure lands in `Loaded::errors`.
pub fn load(
    entry: &str,
    read: &mut dyn FnMut(&str) -> std::io::Result<String>,
) -> Result<Loaded, String> {
    let entry_key = normalize(entry);
    // A std key cannot be an entry, so the standard library cannot be shadowed from the command
    // line by a literal extensionless file either.
    if stdlib::source(&entry_key).is_some() {
        return Err(format!(
            "`{entry_key}` names a standard-library module, not a file; import it with `import {{ … }} from \"{entry_key}\"`"
        ));
    }
    let text = read(&entry_key).map_err(|err| format!("{entry}: {err}"))?;

    let mut modules: Vec<LoadedModule> = Vec::new();
    let mut clean: Vec<bool> = Vec::new();
    let mut errors: Vec<(usize, Diagnostic)> = Vec::new();
    let mut index_of: HashMap<String, usize> = HashMap::new();

    let admit = |key: String,
                 text: String,
                 modules: &mut Vec<LoadedModule>,
                 clean: &mut Vec<bool>,
                 errors: &mut Vec<(usize, Diagnostic)>,
                 index_of: &mut HashMap<String, usize>| {
        let index = modules.len();
        index_of.insert(key.clone(), index);
        let parsed = parse(&text);
        clean.push(parsed.ok());
        for diagnostic in parsed.errors {
            errors.push((index, diagnostic));
        }
        modules.push(LoadedModule {
            name: key.clone(),
            key: key.clone(),
            file: SourceFile::new(key, text),
            module: parsed.module,
        });
    };

    admit(
        entry_key,
        text,
        &mut modules,
        &mut clean,
        &mut errors,
        &mut index_of,
    );

    let mut next = 0;
    while next < modules.len() {
        if !clean[next] {
            next += 1;
            continue;
        }
        for decl in 0..modules[next].module.imports.len() {
            let import = &modules[next].module.imports[decl];
            // Bare and extension-carrying specifiers are the checker's diagnostics; a self-import
            // resolves to a file already loaded, so it needs nothing here either.
            let Ok(resolved) = resolve_specifier(&modules[next].key, &import.specifier) else {
                continue;
            };
            let (Resolved::File(key) | Resolved::Std(key)) = &resolved;
            if index_of.contains_key(key) {
                continue;
            }
            match resolved {
                Resolved::File(key) => match read(&key) {
                    Ok(text) => admit(
                        key,
                        text,
                        &mut modules,
                        &mut clean,
                        &mut errors,
                        &mut index_of,
                    ),
                    Err(_) => {
                        let import = &modules[next].module.imports[decl];
                        errors.push((
                            next,
                            Diagnostic::new(
                                import.specifier_span,
                                format!("cannot find module `{}`", import.specifier),
                            )
                            .note(format!("expected a file at {key}")),
                        ));
                    }
                },
                Resolved::Std(key) => match stdlib::source(&key) {
                    Some(text) => admit(
                        key,
                        text.to_string(),
                        &mut modules,
                        &mut clean,
                        &mut errors,
                        &mut index_of,
                    ),
                    // Same words as the checker's miss arm; no `read` — a std key never
                    // reaches the filesystem.
                    None => {
                        let import = &modules[next].module.imports[decl];
                        errors.push((
                            next,
                            Diagnostic::new(
                                import.specifier_span,
                                format!("no module `{}` in the standard library", import.specifier),
                            )
                            .note(format!(
                                "the standard library provides {}",
                                stdlib::catalogue()
                            )),
                        ));
                    }
                },
            }
        }
        next += 1;
    }

    // Grouped per file and in source order within one, however discovery interleaved them.
    errors.sort_by_key(|(index, diagnostic)| (*index, diagnostic.span.start));
    Ok(Loaded { modules, errors })
}

/// Fold `.` and `..` segments out of a path, the same arithmetic `resolve_specifier` applies —
/// lexical on purpose, so a key is a spelling rather than an inode.
fn normalize(path: &str) -> String {
    let mut parts: Vec<&str> = Vec::new();
    for segment in path.split('/') {
        match segment {
            "" | "." => {}
            ".." => {
                parts.pop();
            }
            segment => parts.push(segment),
        }
    }
    let prefix = if path.starts_with('/') { "/" } else { "" };
    format!("{prefix}{}", parts.join("/"))
}
