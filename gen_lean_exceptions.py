import argparse
import re
from pathlib import Path

REPO_ROOT = Path('/Users/cameronbeeley/formal-conjectures-gc217-proof')
CHUNK_DIR = REPO_ROOT / 'WOWII217FiniteSmallExceptionsChunks'

SIMPL_LIST = """    [completeUpper, pathClosureParallelRound,
      pathClosureParallelMask, degreeUpperNat, degreeUpperBv5, BitVec.zero,
      upperPairs, upperIndex,
      edgeCount, fixedDegreeSequenceUpper, matchesDegreesFromUpper,
      degreeBitsUpper, BoolFour.increment, BoolFour.same, BoolFour.ofNat,
      connectedUpper, reachableFromZeroUpper,
      adjUpper, setBit, bitMask, maskHas,
      List.range, List.range.loop, List.foldl, List.all, List.any,
      List.flatMap, List.flatten, List.map, List.append,
      List.length_cons, List.length_nil, beq_iff_eq, Bool.or_eq_true,
      decide_eq_true_eq, ite_self]"""

HEADER = """import WOWII217FiniteBase
import WOWII217Closure

namespace WOWII217FiniteSmallExceptions

open WOWII217FiniteBase WOWII217Closure

"""

FOOTER = "\nend WOWII217FiniteSmallExceptions\n"


def extract_chunk_payload(path: Path) -> dict:
    text = path.read_text()
    lines = text.splitlines()

    # Collect theorem signature from the first theorem ending with `_closes` up to `:= by`.
    signature_lines = []
    in_sig = False
    for line in lines:
        if not in_sig and line.startswith("theorem ") and line.strip().endswith("_closes :"):
            in_sig = True
            signature_lines.append(line)
            continue
        if in_sig:
            if ":= by" in line:
                before, _ = line.split(":= by", 1)
                signature_lines.append(before)
                break
            signature_lines.append(line)
    if not signature_lines:
        raise ValueError(f"No _closes theorem found in {path}")

    closes_sig = "\n".join(signature_lines) + "\n"

    first_line = signature_lines[0].strip()
    name = first_line.split()[1]
    if not name.endswith("_closes"):
        raise ValueError(f"Unexpected closes theorem name {name} in {path}")

    # Parse n and BitVec width from closes signature.
    n_match = re.search(r"n := (\d+)", closes_sig)
    if not n_match:
        raise ValueError(f"Could not parse n from {path}")
    n_val = int(n_match.group(1))

    w_match = re.search(r"BitVec\s+(\d+)", closes_sig)
    if not w_match:
        raise ValueError(f"Could not parse BitVec width from {path}")
    w_val = int(w_match.group(1))

    # Extract fixed degree sequence text exactly as it appears.
    fd_idx = closes_sig.find("fixedDegreeSequenceUpper")
    if fd_idx < 0:
        raise ValueError(f"Could not locate fixedDegreeSequenceUpper in {path}")
    lbrack = closes_sig.find("[", fd_idx)
    rbrack = closes_sig.find("]", lbrack)
    if lbrack < 0 or rbrack < 0:
        raise ValueError(f"Could not locate degree sequence bracket text in {path}")
    seq_text = closes_sig[lbrack : rbrack + 1]

    # Parse seq for verification checks.
    seq_inner = seq_text[1:-1].strip()
    seq = []
    if seq_inner:
        seq = [int(token.strip()) for token in seq_inner.split(",") if token.strip()]

    return {
        "path": path,
        "base_name": name,
        "closes_sig": closes_sig,
        "n": n_val,
        "w": w_val,
        "seq_text": seq_text,
        "seq": seq,
    }


def generate_chunk(payload: dict) -> str:
    name = payload["base_name"]
    n_val = payload["n"]
    w_val = payload["w"]
    seq_text = payload["seq_text"]
    closes_sig = payload["closes_sig"].rstrip("\n")

    chain_name = f"{name}_closure_chain"

    chain_sig = (
        f"theorem {chain_name} :\n"
        f"    ∀ g g1 g2 g3 g4 : BitVec {w_val},\n"
        f"      connectedUpper (n := {n_val}) g = true →\n"
        f"      fixedDegreeSequenceUpper (n := {n_val}) g\n"
        f"        {seq_text} = true →\n"
        f"      (g1 == pathClosureParallelRound (n := {n_val}) g) = true →\n"
        f"      (g2 == pathClosureParallelRound (n := {n_val}) g1) = true →\n"
        f"      (g3 == pathClosureParallelRound (n := {n_val}) g2) = true →\n"
        f"      (g4 == pathClosureParallelRound (n := {n_val}) g3) = true →\n"
        f"      completeUpper (n := {n_val}) g4 = true := by\n"
    )

    closes_body = (
        f"  intro g connected degrees\n"
        f"  let g1 := pathClosureParallelRound (n := {n_val}) g\n"
        f"  let g2 := pathClosureParallelRound (n := {n_val}) g1\n"
        f"  let g3 := pathClosureParallelRound (n := {n_val}) g2\n"
        f"  let g4 := pathClosureParallelRound (n := {n_val}) g3\n"
        f"  have closed := {chain_name} g g1 g2 g3 g4 connected degrees\n"
        f"    (by simp [g1]) (by simp [g2]) (by simp [g3]) (by simp [g4])\n"
        f"  simpa [pathClosureParallelRounds, g1, g2, g3, g4] using closed\n"
    )

    return (
        f"set_option maxRecDepth 100000 in\n"
        f"set_option maxHeartbeats 1000000000 in\n"
        f"{chain_sig}"
        f"  simp (config := {{ maxSteps := 1000000000 }}) only\n"
        f"{SIMPL_LIST}\n"
        f"  bv_decide (maxSteps := 1000000000) (timeout := 600)\n\n"
        f"set_option maxRecDepth 100000 in\n"
        f"set_option maxHeartbeats 1000000000 in\n"
        f"{closes_sig}"
        f":= by\n{closes_body}"
    )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--src', default=str(CHUNK_DIR), help='Source chunk directory')
    parser.add_argument('--out', default='/tmp/spark_gen/out', help='Output directory')
    args = parser.parse_args()

    src = Path(args.src)
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)

    chunk_paths = sorted(src.glob('Chunk*.lean'))
    if not chunk_paths:
        raise RuntimeError(f'No chunk files under {src}')

    for chunk in chunk_paths:
        payload = extract_chunk_payload(chunk)
        content = HEADER + generate_chunk(payload) + FOOTER
        (out / chunk.name).write_text(content)


if __name__ == '__main__':
    main()
