#!/usr/bin/env python3
"""Run a checker over the TSTP FOF proof benchmark of Taprogge, Steen and
Sariyanto (doi:10.5281/zenodo.19792604), built to evaluate the Nörgler proof
checker.

The benchmark has 1976 correct FOF refutations from the TSTP library (1806
by Otter, 170 by PyRes) and 1952 falsified versions of them made by
automated mutation. The PyRes problems are included. The Otter problems
come from the TPTP library, and the axiom files they include must be under
--tptp. The benchmark was built from TPTP v8.1.0. KRS180+1 was corrected in
v9.3.2, so with a later TPTP its two proofs are reported separately and not
scored.

These proofs come from real provers and do not follow the ProoVer 2026
certificate format (Otter's imported formulas, for instance, are all named
"unknown"). The tolerant profile is the one meant for them.

tests/noergler_subset.txt lists the 122 PyRes proofs that ProofGuard 1.0
accepts. They were chosen by that verdict, so accepting them again shows
nothing, and the subset is meant for testing their falsified versions. Each
falsified proof is a proof known to be correct with one formula changed, and
the harness reports whether it was rejected at the changed step, at a step
that uses it, or elsewhere. The PyRes proofs include their problems, so this subset needs no
TPTP library.

Usage:
    python3 tests/noergler_bench.py --fetch --subset tests/noergler_subset.txt
    python3 tests/noergler_bench.py [--bench DIR] [--tptp DIR] [--subset FILE]
        [--checker CMD] [--args ARGS] [-j N] [--time-limit S]
        [--save FILE] [--baseline FILE]

--fetch downloads the benchmark into tests/noergler/, which is the default
--bench. --tptp is needed only for the Otter proofs. Exits 1 if a falsified
proof is accepted, or if a proof the baseline got right is no longer right.
"""
import hashlib, io, os, re, shlex, subprocess, sys, time, urllib.request, zipfile
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
sys.setrecursionlimit(100_000)
import proover as P

CHANGED_SINCE_V810 = {"KRS180+1"}
DEFAULT_BENCH = os.path.join(HERE, "noergler", "benchmarks")
URL = "https://zenodo.org/api/records/19792604/files/TstpVerificationBenchmarks.zip/content"
MD5 = "356d08af882cdd9c0f43f3a47ccc1100"


def fetch(bench):
    data = urllib.request.urlopen(URL, timeout=300).read()
    if hashlib.md5(data).hexdigest() != MD5:
        raise SystemExit("downloaded benchmark does not match its published checksum")
    zipfile.ZipFile(io.BytesIO(data)).extractall(os.path.dirname(bench))

def located(proof):
    """Where a falsified proof's mutation is: (mutated step names, and for
    every step the names of its premises), with quotes removed."""
    text = open(proof).read()
    unq = lambda n: n.strip().strip("'")
    muts = {unq(m) for m in re.findall(r"^%+\s*Mutated formula '(.*)':\s*$", text, re.M)}
    try:
        steps = P.parse_tstp(text)
    except Exception:
        return muts, {}
    return muts, {unq(s.name): {unq(q) for q in s.premises} for s in steps}

def caught_where(proof, reason):
    """'at the mutated step', 'at a step that uses it', or 'elsewhere'."""
    m = re.match(r"step (.+?): ", reason)
    if not m:
        return "elsewhere"
    muts, premises = located(proof)
    step = m.group(1).strip().strip("'")
    if step in muts:
        return "at the mutated step"
    if premises.get(step, set()) & muts:
        return "at a step that uses it"
    return "elsewhere"


def jobs(bench, tptp, subset=None):
    out = []
    for prover in ("Otter", "PyRes"):
        for kind in ("original", "falsified"):
            d = os.path.join(bench, prover, kind)
            for f in sorted(os.listdir(d)):
                if not f.endswith(".proof"):
                    continue
                if subset is not None and f.replace("_falsified", "")[:-6] not in subset:
                    continue
                if prover == "Otter" and not tptp:
                    raise SystemExit("the Otter proofs need --tptp DIR (a TPTP library)")
                name = f.split("_")[0]
                problem = (os.path.join(bench, "PyRes", "problems", name + ".p")
                           if prover == "PyRes" else
                           os.path.join(tptp, "Problems", name[:3], name + ".p"))
                out.append((f"{prover}/{kind}/{f}", name, kind, problem,
                            os.path.join(d, f)))
    return out

def run_one(cmd, job, limit, tptp):
    _, _, _, problem, proof = job
    env = dict(os.environ, TPTP=tptp or "")
    start = time.monotonic()
    try:
        out = subprocess.run(cmd + ["--quiet", "--time-limit", str(limit), problem, proof],
                             capture_output=True, text=True, env=env,
                             timeout=limit + 15).stdout
    except subprocess.TimeoutExpired:
        out = ""
    m = re.search(r"SZS status (\w+)(?: : (.*))?", out)
    return (m.group(1) if m else "NoStatus", time.monotonic() - start,
            (m.group(2) or "") if m else "")

def outcome(kind, verdict):
    if verdict == "VerifiedGood":
        return "accepted"
    if verdict == "VerifiedBad":
        return "rejected"
    return "gave up"

def correct(kind, verdict):
    return outcome(kind, verdict) == ("accepted" if kind == "original" else "rejected")

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
    bench = os.path.abspath(opt("--bench", DEFAULT_BENCH))
    tptp = os.path.abspath(opt("--tptp")) if opt("--tptp") else None
    if "--fetch" in argv and not os.path.isdir(bench):
        fetch(bench)
    if not os.path.isdir(bench):
        print(f"{bench} not found; run with --fetch to download it")
        return 2
    subset = None
    if opt("--subset"):
        subset = {l.split()[0] for l in open(opt("--subset"))
                  if l.strip() and not l.startswith("#")}
    cmd = shlex.split(opt("--checker", f"{shlex.quote(sys.executable)} "
                                         f"{shlex.quote(os.path.join(ROOT, 'proover-check'))}"))
    cmd += shlex.split(opt("--args", ""))
    limit = float(opt("--time-limit", "30"))
    todo = jobs(bench, tptp, subset)
    with ThreadPoolExecutor(int(opt("-j", "4"))) as pool:
        results = list(pool.map(lambda j: run_one(cmd, j, limit, tptp), todo))
    rows = {j[0]: r for j, r in zip(todo, results)}
    info = {j[0]: j for j in todo}

    if "--save" in argv:
        with open(opt("--save"), "w") as f:
            f.write("# proof\tverdict\tseconds\treason\n")
            for key, (v, secs, why) in rows.items():
                f.write(f"{key}\t{v}\t{secs:.2f}\t{why}\n")

    scored = {k: r for k, r in rows.items() if info[k][1] not in CHANGED_SINCE_V810}
    print(f"{len(rows)} proofs, {len(scored)} scored "
          f"(not scored: {', '.join(sorted(CHANGED_SINCE_V810))}, changed after TPTP v8.1.0)")
    print(f"{'':10s} {'':10s} {'proofs':>7s} {'accepted':>9s} {'rejected':>9s} "
          f"{'gave up':>8s} {'mean s':>7s}")
    for prover in ("Otter", "PyRes", "all"):
        for kind in ("original", "falsified"):
            sel = [r for k, r in scored.items()
                   if info[k][2] == kind and (prover == "all" or k.startswith(prover + "/"))]
            if not sel:
                continue
            n = {o: sum(outcome(kind, r[0]) == o for r in sel)
                 for o in ("accepted", "rejected", "gave up")}
            print(f"{prover:10s} {kind:10s} {len(sel):7d} {n['accepted']:9d} {n['rejected']:9d} "
                  f"{n['gave up']:8d} {sum(r[1] for r in sel) / len(sel):7.2f}")
    where = {}
    for k, r in scored.items():
        if info[k][2] == "falsified" and r[0] == "VerifiedBad":
            w = caught_where(info[k][4], r[2])
            where[w] = where.get(w, 0) + 1
    if where:
        print("\nfalsified proofs rejected: " + ", ".join(
            f"{where.get(w, 0)} {w}" for w in
            ("at the mutated step", "at a step that uses it", "elsewhere")))
    bad = sorted(k for k, r in scored.items()
                 if info[k][2] == "falsified" and r[0] == "VerifiedGood")
    print(f"\nfalsified proofs accepted: {len(bad)}")
    for k in bad[:20]:
        print(f"  {k}")
    failed = bool(bad)

    base_path = opt("--baseline")
    if base_path:
        base = load(base_path)
        print(f"\nagainst {os.path.basename(base_path)}:")
        counts = {}
        for k, (v, _, why) in scored.items():
            if k not in base or base[k][0] == v:
                continue
            kind = info[k][2]
            was, now = correct(kind, base[k][0]), correct(kind, v)
            mark = "fixed" if now and not was else "REGRESSION" if was and not now else "changed"
            failed |= mark == "REGRESSION"
            key = (mark, kind, base[k][0], v)
            counts.setdefault(key, []).append(k)
        for (mark, kind, old, new), ks in sorted(counts.items()):
            print(f"  {mark:10s} {kind:9s} {old} -> {new}: {len(ks)}  e.g. {ks[0]}")
        if not counts:
            print("  no verdict changed")
    return 1 if failed else 0

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
