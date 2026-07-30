#!/usr/bin/env python3
"""Check that every aggregate module imports exactly the files in its directory.

This repo keeps hand-maintained aggregate modules: a file `Foo.lean` that imports
every `Foo/Bar.lean`. Nothing enforces that they stay in sync, and a missing entry
does not error where the file lives - it errors much later, at a use site, as
"unknown identifier <theorem that demonstrably exists>".

That cost several debugging rounds on 2026-07-30 (the chunk aggregate missing 147
entries, the Branches aggregate missing 441). This makes it a one-second check.

Usage:  python3 scripts/check_aggregates.py           # report
        python3 scripts/check_aggregates.py --fix     # insert missing imports
Exit code 1 if anything is out of sync (so it can gate CI).
"""
import glob, re, sys
from pathlib import Path

def discover():
    """Any directory D with a sibling D.lean is an aggregate."""
    for d in sorted(p for p in Path('.').iterdir() if p.is_dir()):
        agg = Path(f'{d}.lean')
        if agg.exists() and glob.glob(f'{d}/*.lean'):
            yield agg, d
        for sub in sorted(p for p in d.iterdir() if p.is_dir()):
            agg2 = Path(f'{sub}.lean')
            if agg2.exists() and glob.glob(f'{sub}/*.lean'):
                yield agg2, sub

def module_of(path: Path) -> str:
    return str(path.with_suffix('')).replace('/', '.')

def main():
    fix = '--fix' in sys.argv
    bad = 0
    for agg, d in discover():
        prefix = module_of(d)
        text = agg.read_text()
        imported = set(re.findall(rf'^import {re.escape(prefix)}\.(\S+)\s*$', text, re.M))
        on_disk = {Path(f).stem for f in glob.glob(f'{d}/*.lean')}
        missing = sorted(on_disk - imported)
        stale   = sorted(imported - on_disk)
        if not missing and not stale:
            print(f"OK       {agg}  ({len(on_disk)} modules)")
            continue
        bad += 1
        print(f"OUT OF SYNC  {agg}")
        if missing:
            print(f"  {len(missing)} file(s) not imported: {missing[:5]}{' …' if len(missing)>5 else ''}")
        if stale:
            print(f"  {len(stale)} import(s) with no file: {stale[:5]}{' …' if len(stale)>5 else ''}")
        if fix and missing:
            lines = text.split('\n')
            idx = [i for i, l in enumerate(lines) if l.startswith(f'import {prefix}.')]
            at = (max(idx) + 1) if idx else 0
            for m in reversed(missing):
                lines.insert(at, f'import {prefix}.{m}')
            agg.write_text('\n'.join(lines))
            print(f"  FIXED: inserted {len(missing)} import(s)")
    if bad and not fix:
        print(f"\n{bad} aggregate(s) out of sync. Re-run with --fix to repair.")
    return 1 if (bad and not fix) else 0

if __name__ == '__main__':
    sys.exit(main())
