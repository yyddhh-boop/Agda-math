#!/usr/bin/env python3
"""Audit project sources and type-check the entire entry point locally."""

import argparse
import datetime as dt
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--agda", help="Explicit Agda executable")
args = parser.parse_args()
compiler = args.agda or shutil.which("agda")
if compiler is None:
    fallback = Path.home() / ".local/bin/agda"
    if fallback.is_file():
        compiler = str(fallback)
if compiler is None:
    sys.exit("Agda not found; supply --agda /absolute/path/to/agda")

sources = sorted((ROOT / "DHH").rglob("*.agda")) + [ROOT / "Everything.agda"]
entry_source = (ROOT / "Everything.agda").read_text()
entry_imports = set(re.findall(r"^import\s+(DHH\.[\w.]+)\s*$", entry_source, re.M))
required_imports = {
    ".".join(path.relative_to(ROOT).with_suffix("").parts)
    for path in sources if path.name != "Everything.agda"
}
if entry_imports != required_imports:
    missing = sorted(required_imports - entry_imports)
    stale = sorted(entry_imports - required_imports)
    sys.exit(f"Everything.agda import coverage mismatch; missing={missing}, stale={stale}")
for path in sources:
    source = path.read_text()
    if not re.search(r"\{-# OPTIONS[^\n]*--cubical[^\n]*--safe", source):
        sys.exit(f"Required safe/cubical header missing: {path.name}")
    # Our files use non-nested block comments. Remove comments for the
    # syntactic audit; Agda remains the authority for proof completeness.
    code = re.sub(r"\{-.*?-\}", "", source, flags=re.S)
    code = re.sub(r"--[^\n]*", "", code)
    forbidden = r"\b(postulate|TERMINATING|NON_TERMINATING|NO_POSITIVITY_CHECK|NON_COVERING)\b|\{!|(?<!\w)\?(?!\w)"
    if re.search(forbidden, code):
        sys.exit(f"Unchecked proof construct found: {path.name}")
    forbidden_options = (
        "allow-unsolved-metas", "no-termination-check", "no-positivity-check",
        "allow-incomplete-matches", "type-in-type", "no-universe-check",
    )
    if any(option in source for option in forbidden_options):
        sys.exit(f"Unsafe option found: {path.name}")

version = subprocess.check_output([compiler, "--version"], text=True).strip()
if "2.8.0" not in version:
    sys.exit(f"This dependency snapshot targets Agda 2.8.0; found {version}")

checks = ROOT / "checks"
checks.mkdir(exist_ok=True)
command = [compiler, "--no-libraries", "-i", ".", "-i", "vendor/cubical",
           "--cubical", "--safe", "--guardedness",
           "-WnoUnsupportedIndexedMatch", "Everything.agda"]
started = time.monotonic()
log_path = checks / "latest.log"
with log_path.open("w") as log:
    completed = subprocess.run(command, cwd=ROOT, stdout=log,
                               stderr=subprocess.STDOUT, timeout=600)
manifest = {
    "checked_at_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
    "compiler": version,
    "cubical_version": "0.9",
    "cubical_commit": "b150186d2544e7efeddd31e5d14a8b9ecbb100f7",
    "command": command,
    "exit_code": completed.returncode,
    "elapsed_seconds": round(time.monotonic() - started, 3),
    "own_source_audit": "no postulates, holes, or unsafe proof bypasses",
    "source_sha256": {
        str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in sources
    },
    "scope": "All own modules, actual real geometries, stable nerve construction, and closed DHH statement type; classical/original localization and nerve comparisons remain; not a DHH proof",
}
(checks / "verification.json").write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + "\n")
print(f"{version}; {len(sources)} project modules audited.")
print(f"Type checking {'PASSED' if completed.returncode == 0 else 'FAILED'}; log: {log_path}")
if completed.returncode:
    print(log_path.read_text()[-10000:])
sys.exit(completed.returncode)
