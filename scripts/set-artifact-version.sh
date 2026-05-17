#!/usr/bin/env bash
set -euo pipefail

if [ "$#" -ne 1 ]; then
  echo "usage: scripts/set-artifact-version.sh VERSION" >&2
  exit 2
fi

version="$1"

if [ -z "$version" ]; then
  echo "artifact version must not be empty" >&2
  exit 2
fi

python3 - "$version" <<'PY'
from pathlib import Path
import re
import sys

version = sys.argv[1]
path = Path("LeanUfo/UFO/DSL/Version.lean")
text = path.read_text()
pattern = r'(def artifactVersion : String :=\n\s*)"[^"]*"'
replacement = rf'\1"{version}"'
updated, count = re.subn(pattern, replacement, text, count=1)
if count != 1:
    raise SystemExit("could not find artifactVersion definition")
path.write_text(updated)
PY

echo "set Lean UFO artifact version to ${version}"
