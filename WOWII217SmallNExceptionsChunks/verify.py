from __future__ import annotations

import re
from pathlib import Path

ROOT = Path("/Users/cameronbeeley/formal-conjectures-gc217-proof")
SRC_DIR = ROOT / "WOWII217SmallNExceptionsChunks" / "Branches"
OUT_DIR = Path("/tmp/spark_branches/out")


def parse_n(fname: str) -> int:
    m = re.search(r"_card(\d+)_", fname)
    if not m:
        raise ValueError(f"cannot parse n from {fname}")
    return int(m.group(1))


def parse_seq(lines: list[str]) -> str:
    line = next((line for line in lines if "hSeqG : G.degreeSequence" in line), None)
    if not line:
        raise ValueError("hSeqG line missing")
    m = re.search(r"G\.degreeSequence\s*=\s*(\[[^\]]*\])", line)
    if not m:
        raise ValueError("hSeqG list parse failed")
    return m.group(1).strip()


def normalize_seq(seq_text: str) -> list[int]:
    inner = seq_text.strip()[1:-1].strip()
    if not inner:
        return []
    return [int(x.strip()) for x in inner.split(",") if x.strip()]


def theorem_name_from(lines: list[str]) -> str:
    for line in lines:
        m = re.match(r"^\s*theorem\s+(\S+)", line)
        if m:
            return m.group(1)
    raise ValueError("theorem name missing")


def check_file(src: Path, out: Path) -> dict[str, bool | str | int]:
    s_lines = src.read_text().splitlines()
    g_lines = out.read_text().splitlines()
    n = parse_n(src.name)

    s_name = theorem_name_from(s_lines)
    g_name = theorem_name_from(g_lines)

    s_seq_text = parse_seq(s_lines)
    g_seq_text = parse_seq(g_lines)
    s_seq = normalize_seq(s_seq_text)
    g_seq = normalize_seq(g_seq_text)

    check_seq_identical = s_seq == g_seq
    check_len = len(g_seq) == n
    check_even = (sum(g_seq) % 2 == 0) and (g_seq)
    check_max = (max(g_seq) if g_seq else -1) <= n - 1
    check_n_range = 4 <= n <= 12
    w_expected = n * (n - 1) // 2
    check_width = check_n_range and w_expected >= 0

    return {
        "file": src.name,
        "n": n,
        "theorem_name_match": s_name == g_name,
        "seq_identical": check_seq_identical,
        "len": check_len,
        "sum_even": bool(check_even),
        "max_ok": bool(check_max),
        "n_range_ok": bool(check_n_range),
        "width_ok": bool(check_width),
        "s_sum": sum(s_seq),
        "s_max": max(s_seq) if s_seq else -1,
        "w": w_expected,
        "has_sorry": "sorry" in out.read_text(),
    }


def main() -> None:
    entries = []
    failures = 0
    for src in sorted(SRC_DIR.glob("*.lean")):
        out = OUT_DIR / src.name
        if not out.exists():
            raise FileNotFoundError(f"missing generated file {out}")
        res = check_file(src, out)
        entries.append(res)
        if not all(
            (
                res["theorem_name_match"],
                res["seq_identical"],
                res["len"],
                res["sum_even"],
                res["max_ok"],
                res["width_ok"],
            )
        ):
            failures += 1

    total = len(entries)
    checks = {
        "theorem_name_match": sum(1 for x in entries if x["theorem_name_match"]),
        "seq_identical": sum(1 for x in entries if x["seq_identical"]),
        "len": sum(1 for x in entries if x["len"]),
        "sum_even": sum(1 for x in entries if x["sum_even"]),
        "max_ok": sum(1 for x in entries if x["max_ok"]),
        "n_range_ok": sum(1 for x in entries if x["n_range_ok"]),
        "width_ok": sum(1 for x in entries if x["width_ok"]),
        "no_sorry": sum(1 for x in entries if not x["has_sorry"]),
    }

    print("VERIFICATION SUMMARY")
    for k, v in checks.items():
        print(f"{k}: {v}/{total}")
    print(f"TOTAL FAILURES: {failures}")
    if failures:
        print("FAILURES:")
        for e in entries:
            if not all(
                (
                    e["theorem_name_match"],
                    e["seq_identical"],
                    e["len"],
                    e["sum_even"],
                    e["max_ok"],
                    e["n_range_ok"],
                    e["width_ok"],
                    not e["has_sorry"],
                )
            ):
                print(
                    f"{e['file']}: name={e['theorem_name_match']} seq={e['seq_identical']} "
                    f"len={e['len']} sum_even={e['sum_even']} max_ok={e['max_ok']} "
                    f"n_range_ok={e['n_range_ok']} width_ok={e['width_ok']} no_sorry={not e['has_sorry']}"
                )
    else:
        print("ALL PASS")


if __name__ == "__main__":
    main()
