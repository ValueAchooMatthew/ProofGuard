#!/usr/bin/env python3
"""Run a checker over the ProoVer 2026 competition proofs and compare its
verdicts with the correct answers.

The correct answers in tests/proover2026_truth.txt come from the official
results page (https://tptp.org/CASC/J13/WWWFiles/Results.html#PRVProblems):
a proof on which systems scored +2 or -10 is invalid, one on which they
scored +1 or -1 is valid. Nine of the 100 published proofs were not scored
and have no answer.

Usage:
    python3 tests/proover2026.py                     # this checkout
    python3 tests/proover2026.py --save FILE         # also record the verdicts
    python3 tests/proover2026.py --baseline FILE     # and compare with a recorded run
    python3 tests/proover2026.py --checker CMD       # another checker, e.g. the 1.0 bundle
    python3 tests/proover2026.py --fetch             # download the proofs first

Exits 1 if an invalid proof is accepted, or if a proof the baseline got right
is no longer right.
"""
import os, re, shlex, subprocess, sys, time, urllib.request, zipfile, io
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
CORPUS = os.path.join(HERE, "proover2026", "ProoVer2026")
TRUTH = os.path.join(HERE, "proover2026_truth.txt")
URL = "https://proover-competition.github.io/assets/ProoVer2026.zip"

OUTCOMES = ["bad proof rejected", "good proof accepted", "bad proof ACCEPTED",
            "good proof REJECTED", "gave up on a bad proof", "gave up on a good proof"]

def outcome(truth, verdict):
    if truth not in ("good", "bad"):
        return "unscored"
    if verdict == "VerifiedGood":
        return "good proof accepted" if truth == "good" else "bad proof ACCEPTED"
    if verdict == "VerifiedBad":
        return "bad proof rejected" if truth == "bad" else "good proof REJECTED"
    return f"gave up on a {truth} proof"

def correct(o):
    return o in ("bad proof rejected", "good proof accepted")

def score(counts):
    return (2 * counts.get("bad proof rejected", 0) + counts.get("good proof accepted", 0)
            - counts.get("good proof REJECTED", 0) - 10 * counts.get("bad proof ACCEPTED", 0))

def run_one(cmd, proof, limit):
    start = time.monotonic()
    try:
        out = subprocess.run(cmd + ["--quiet", "--time-limit", str(limit), proof],
                             cwd=CORPUS, capture_output=True, text=True,
                             timeout=limit + 15).stdout
    except subprocess.TimeoutExpired:
        out = ""
    m = re.search(r"SZS status (\w+)(?: : (.*))?", out)
    return (m.group(1) if m else "NoStatus", time.monotonic() - start,
            (m.group(2) or "") if m else "")

def load(path):
    rows = {}
    for line in open(path):
        if line.strip() and not line.startswith("#"):
            f = line.rstrip("\n").split("\t")
            rows[f[0]] = (f[1], float(f[2]), f[3] if len(f) > 3 else "")
    return rows

def main(argv):
    def opt(name, default=None):
        return argv[argv.index(name) + 1] if name in argv else default
    if "--fetch" in argv and not os.path.isdir(CORPUS):
        data = urllib.request.urlopen(URL, timeout=120).read()
        zipfile.ZipFile(io.BytesIO(data)).extractall(os.path.dirname(CORPUS))
    if not os.path.isdir(CORPUS):
        print(f"{CORPUS} not found; run with --fetch to download it")
        return 2
    cmd = shlex.split(opt("--checker", f"{shlex.quote(sys.executable)} "
                                         f"{shlex.quote(os.path.join(ROOT, 'proover-check'))}"))
    cmd += shlex.split(opt("--args", ""))
    limit = float(opt("--time-limit", "30"))
    jobs = int(opt("-j", "4"))
    truth = dict(line.split() for line in open(TRUTH))
    proofs = sorted(f for f in os.listdir(CORPUS) if f.endswith(".s"))

    with ThreadPoolExecutor(jobs) as pool:
        results = list(pool.map(lambda p: run_one(cmd, p, limit), proofs))
    rows = {p[:-2]: r for p, r in zip(proofs, results)}

    if "--save" in argv:
        with open(opt("--save"), "w") as f:
            f.write("# proof\tverdict\tseconds\treason\n")
            for p, (v, secs, why) in rows.items():
                f.write(f"{p}\t{v}\t{secs:.2f}\t{why}\n")

    counts = {}
    for p, (v, _, _) in rows.items():
        o = outcome(truth.get(p), v)
        counts[o] = counts.get(o, 0) + 1
    scored = [r for p, r in rows.items() if p in truth]
    print(f"{len(rows)} proofs, {len(scored)} scored. Score {score(counts)} of 138, "
          f"mean time {sum(r[1] for r in scored) / len(scored):.2f} s")
    for o in OUTCOMES:
        print(f"  {counts.get(o, 0):3d}  {o}")
    print(f"  {counts.get('unscored', 0):3d}  unscored (no official answer)")

    failed = counts.get("bad proof ACCEPTED", 0) > 0
    base_path = opt("--baseline")
    if base_path:
        base = load(base_path)
        base_counts = {}
        for p, (v, _, _) in base.items():
            o = outcome(truth.get(p), v)
            base_counts[o] = base_counts.get(o, 0) + 1
        print(f"\nagainst {os.path.basename(base_path)} (score {score(base_counts)}):")
        changes = [(p, base[p][0], rows[p][0]) for p in rows
                   if p in base and base[p][0] != rows[p][0]]
        for p, old, new in changes:
            o_old, o_new = outcome(truth.get(p), old), outcome(truth.get(p), new)
            if o_old == "unscored":
                mark = "unscored  "
            elif correct(o_new) and not correct(o_old):
                mark = "fixed     "
            elif correct(o_old) and not correct(o_new):
                mark = "REGRESSION"; failed = True
            else:
                mark = "changed   "
            print(f"  {mark} {p}  {truth.get(p, '-'):4s}  {old} -> {new}"
                  + (f"  ({rows[p][2][:90]})" if rows[p][2] else ""))
        if not changes:
            print("  no verdict changed")
    return 1 if failed else 0

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
