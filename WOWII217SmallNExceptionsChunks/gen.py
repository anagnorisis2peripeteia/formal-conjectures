from __future__ import annotations

import re
from pathlib import Path

ROOT = Path("/Users/cameronbeeley/formal-conjectures-gc217-proof")
SRC_DIR = ROOT / "WOWII217SmallNExceptionsChunks" / "Branches"
OUT_DIR = Path("/tmp/spark_branches/out")

EXTRA_IMPORTS = [
    "import WOWII217Bridge.SmallNPattern",
    "import WOWII217Bridge.Certified",
]


def parse_n(fname: str) -> int:
    m = re.search(r"_card(\d+)_", fname)
    if not m:
        raise ValueError(f"cannot parse card number from {fname}")
    return int(m.group(1))


def parse_theorem_name(lines: list[str]) -> str:
    for line in lines:
        m = re.match(r"^\s*theorem\s+(\S+)", line)
        if m:
            return m.group(1)
    raise ValueError("theorem name not found")


def parse_sequence(line: str) -> tuple[str, list[int]]:
    m = re.search(r"\[([^\]]+)\]", line)
    if not m:
        raise ValueError("sequence literal missing")
    seq_text = f"[{m.group(1)}]"
    nums = [x.strip() for x in m.group(1).split(",") if x.strip()]
    seq = [int(x) for x in nums]
    return seq_text, seq


def find_lines_with(haystack: list[str], needle: str) -> list[int]:
    return [i for i, line in enumerate(haystack) if needle in line]


def build_theorem(lines: list[str], theorem_name: str, n: int, seq_text: str) -> list[str]:
    theorem_idx = next(i for i, line in enumerate(lines) if re.match(r"^\s*theorem\s+\S+", line))
    by_idx = next(
        i
        for i in range(theorem_idx, len(lines))
        if re.search(r"^\s*:=\s*by\s*$", lines[i])
    )
    end_result_idx = by_idx
    header = lines[theorem_idx:end_result_idx]

    hcard_candidates = [i for i in range(theorem_idx, end_result_idx) if "Fintype.card V = " in lines[i] and "hCard" in lines[i]]
    if not hcard_candidates:
        raise ValueError("hCard binder not found")
    hcard_idx = hcard_candidates[0]
    hseq_candidates = [i for i in range(theorem_idx, end_result_idx) if "hSeqG : G.degreeSequence" in lines[i]]
    if not hseq_candidates:
        raise ValueError("hSeqG binder not found")
    hseq_idx = hseq_candidates[0]
    if hseq_idx <= hcard_idx:
        raise ValueError("unexpected hSeqG position")

    theorem_head = lines[theorem_idx : hcard_idx + 1]
    theorem_head[-1] = re.sub(r"\s*:\s*$", "", theorem_head[-1])

    # Keep indentation from hCard line
    indent_match = re.match(r"^(\s*)", theorem_head[-1])
    indent = indent_match.group(1) if indent_match else ""
    fixed_hfin = (
        f"{indent}(hFinTrans : ∃ e : Fin {n} ≃ V, "
        f"List.ofFn (fun v : Fin {n} => G.degree (e v)) = {seq_text})"
    )

    hseq_line = lines[hseq_idx]
    hseq_line = hseq_line.rstrip()
    if not hseq_line.rstrip().endswith(":"):
        hseq_line = hseq_line + " :"
    result_type_lines = lines[hseq_idx + 1 : by_idx]

    theorem = []
    theorem.extend(theorem_head)
    theorem.append(fixed_hfin)
    theorem.append(hseq_line)
    theorem.extend(result_type_lines)
    theorem.append("  := by")
    theorem.append("")
    digits = "".join(seq_text.strip()[1:-1].replace(" ", "").split(","))
    theorem.append("  exact WOWII217Bridge.traceable_of_card_eq G " + seq_text)
    theorem.append("    (fun H _ hconn hds =>")
    theorem.append(
        f"      WOWII217Bridge.certified_{n} _ H connected_degreeSequence_{digits}_closes hconn hds)"
    )
    theorem.append("    connected")
    theorem.append("    hFinTrans")

    return theorem


def add_imports(lines: list[str]) -> list[str]:
    existing = {line.strip() for line in lines}
    first_non_import = next(
        (i for i, line in enumerate(lines) if not line.startswith("import ")),
        len(lines),
    )
    missing = [imp for imp in EXTRA_IMPORTS if imp not in existing]
    if not missing:
        return lines
    return lines[:first_non_import] + missing + lines[first_non_import:]


def emit_out_file(src: Path, out: Path) -> None:
    text = src.read_text()
    lines = text.splitlines()
    theorem_name = parse_theorem_name(lines)

    # extract sequence literal from hSeqG binder
    hseq_line_idx = next(
        i for i, line in enumerate(lines) if "hSeqG : G.degreeSequence" in line
    )
    seq_text, _seq = parse_sequence(lines[hseq_line_idx])

    n = parse_n(src.name)
    # insert required imports once and keep namespace/end scaffold from source
    lines = add_imports(lines)

    theorem_idx = next(i for i, line in enumerate(lines) if re.match(r"^\s*theorem\s+\S+", line))
    by_idx = next(
        i
        for i in range(theorem_idx, len(lines))
        if re.search(r"^\s*:=\s*by\s*$", lines[i])
    )
    end_idx = next(i for i in range(by_idx, len(lines)) if re.match(r"^\s*end\s+\S+", lines[i]))

    preamble = lines[:theorem_idx]
    namespace_tail = lines[end_idx:]

    new_thm = build_theorem(lines[theorem_idx:end_idx], theorem_name, n, seq_text)

    out_lines = preamble + ["open Classical in"] + new_thm + namespace_tail
    out.write_text("\n".join(out_lines) + "\n")


def main():
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    for src in sorted(SRC_DIR.glob("*.lean")):
        emit_out_file(src, OUT_DIR / src.name)


if __name__ == "__main__":
    main()
