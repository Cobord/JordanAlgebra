"""Run every computation listed in README.md, in parallel where the data dependencies allow.

    uv run python main.py            # everything; reuses autO.pkl, gauss2.pkl, eis2.pkl if present
    uv run python main.py --fresh    # also regenerate those caches (aut_cache.py, run2.py)
    uv run python main.py --quick    # quick checks only
    uv run python main.py --brute    # also the ~20 minute brute_gauss.py recount

Each step's output is printed in full when it finishes.
"""

import argparse
import os
import shutil
import subprocess
import sys
import time
from concurrent.futures import FIRST_COMPLETED, Future, ThreadPoolExecutor, wait
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Set, Tuple

HERE = Path(__file__).resolve().parent


@dataclass
class Step:
    name: str
    cmd: List[str]
    deps: List[str] = field(default_factory=list)
    outputs: List[str] = field(default_factory=list)  # cached results: skipped if all present and not --fresh


def py(*args: str) -> List[str]:
    return [sys.executable, *args]


QUICK: List[Step] = [
    Step("spin", py("spin.py")),
    Step("moufang", py("moufang.py")),
    Step("binary_tetrahedral", py("binary_tetrahedral.py")),
]

PIPELINE: List[Step] = [
    Step("aut_cache", py("aut_cache.py"), outputs=["autO.pkl"]),
    Step("run2 gauss", py("run2.py", "gauss"), ["aut_cache"], ["gauss2.pkl"]),
    Step("run2 eis", py("run2.py", "eis"), ["aut_cache"], ["eis2.pkl"]),
    Step("analyze gauss", py("analyze.py", "gauss", "4"), ["run2 gauss"]),
    Step("analyze eis", py("analyze.py", "eis", "6"), ["run2 eis"]),
    Step("color_rep", py("color_rep.py"), ["run2 gauss", "run2 eis"]),
    Step("eis_struct", py("eis_struct.py"), ["run2 eis"]),
    Step("kd", py("kd.py"), ["aut_cache"]),
    Step("export_gap", py("export_gap.py"), ["aut_cache", "run2 gauss", "run2 eis"]),
]

GAP = Step("ident.g", ["gap", "-q", "ident.g"], ["export_gap"])
BRUTE = Step("brute_gauss", py("brute_gauss.py"))


def run(step: Step) -> Tuple[bool, float, str]:
    # steps already run in parallel; multithreaded BLAS in each would oversubscribe the cores
    env = {**os.environ, "OMP_NUM_THREADS": "1", "OPENBLAS_NUM_THREADS": "1", "MKL_NUM_THREADS": "1"}
    start = time.monotonic()
    proc = subprocess.run(step.cmd, cwd=HERE, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    return proc.returncode == 0, time.monotonic() - start, proc.stdout


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--quick", action="store_true", help="only the quick checks")
    parser.add_argument("--fresh", action="store_true", help="regenerate cached .pkl files")
    parser.add_argument("--brute", action="store_true", help="also run brute_gauss.py (about twenty minutes)")
    args = parser.parse_args()

    steps: List[Step] = list(QUICK)
    if not args.quick:
        steps += PIPELINE
        if shutil.which("gap"):
            steps.append(GAP)
        else:
            print("gap not found on PATH; skipping ident.g", file=sys.stderr)
        if args.brute:
            steps.append(BRUTE)

    done: Set[str] = set()
    results: List[Tuple[str, str, float]] = []
    for s in steps:
        if s.outputs and not args.fresh and all((HERE / o).exists() for o in s.outputs):
            done.add(s.name)
            results.append((s.name, "cached", 0.0))
    pending: List[Step] = [s for s in steps if s.name not in done]

    failed = False
    start = time.monotonic()
    with ThreadPoolExecutor() as pool:
        running: Dict[Future, Step] = {}
        while pending or running:
            if not failed:
                for s in [s for s in pending if all(d in done for d in s.deps)]:
                    pending.remove(s)
                    running[pool.submit(run, s)] = s
            if not running:
                break
            finished, _ = wait(running, return_when=FIRST_COMPLETED)
            for fut in finished:
                s = running.pop(fut)
                ok, secs, out = fut.result()
                print(f"\n=== {s.name} ({secs:.1f}s) ===\n{out}", end="", flush=True)
                results.append((s.name, "ok" if ok else "FAIL", secs))
                if ok:
                    done.add(s.name)
                else:
                    failed = True  # let running steps finish, start nothing new

    print(f"\n=== summary ({time.monotonic() - start:.0f}s wall) ===")
    for name, status, secs in results:
        print(f"{status:6} {secs:6.1f}s  {name}")
    for s in pending:
        print(f"{'skip':6} {'':7}  {s.name}")
    if failed or pending:
        sys.exit(1)


if __name__ == "__main__":
    main()
