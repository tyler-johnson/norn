#!/usr/bin/env python3
"""Record the Norn extension in one VS Code extensions directory.

A symlink into `<root>/extensions` is not an install. VS Code keeps `extensions.json` beside the
extension folders and treats it as the record of what is installed there, writing it when something
is installed or uninstalled and not when the folder is scanned — so a folder that is not listed does
not exist, and a listed version that disagrees with the manifest leaves the extension stuck asking
to be restarted with nothing that a restart would fix.

Both failures look like grammar bugs rather than install ones, which is why this runs from
`make editor-install` rather than living in a comment.

Usage: register.py <extensions-directory>
"""

import json
import os
import pathlib
import sys

EXTENSION = "norn-lang.norn"


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print(__doc__, file=sys.stderr)
        return 2
    extensions = pathlib.Path(argv[1])
    manifest = pathlib.Path(__file__).resolve().parent / "package.json"
    version = json.loads(manifest.read_text())["version"]

    record = extensions / "extensions.json"
    try:
        entries = json.loads(record.read_text())
    except FileNotFoundError:
        entries = []
    except json.JSONDecodeError:
        # VS Code may be part-way through writing it. Leaving it alone is right: the alternative is
        # replacing a file another process believes it owns.
        print(f"{record} is not readable as JSON; not touching it", file=sys.stderr)
        return 1

    entries = [
        entry
        for entry in entries
        if entry.get("identifier", {}).get("id") != EXTENSION
    ]
    entries.append(
        {
            "identifier": {"id": EXTENSION},
            "version": version,
            # The path VS Code opens, which is the link rather than what it points at.
            "location": {
                "$mid": 1,
                "path": str(extensions / EXTENSION),
                "scheme": "file",
            },
            "relativeLocation": EXTENSION,
        }
    )

    # Written through a temporary file so a reader never sees half of it.
    staged = record.with_suffix(".json.norn-tmp")
    staged.write_text(json.dumps(entries))
    os.replace(staged, record)
    print(f"registered {EXTENSION} {version} in {record}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
