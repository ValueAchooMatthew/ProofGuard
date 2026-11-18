#!/usr/bin/env python3
"""Conformance tests: proofs that are logically sound, or look it, but break
the ProoVer 2026 certificate specification must never be accepted.

Two parts. The hand-written cases cover each way ProofGuard 1.0 was found to
accept such a proof. The mutations take every valid competition proof the
checker accepts and break the specification in one place at a time (drop a
required annotation, add a false status, point a file directive at the wrong
formula, and so on).

Usage:
    python3 tests/conformance.py                  # this checkout
    python3 tests/conformance.py --checker CMD    # another checker, e.g. the 1.0 bundle

Exits 1 if any broken proof is reported VerifiedGood, or a valid one is not.
"""
import os, re, shlex, subprocess, sys, tempfile
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
import proover as P

CORPUS = os.path.join(HERE, "proover2026", "ProoVer2026")
TRUTH = os.path.join(HERE, "proover2026_truth.txt")

P1 = """
fof(a1, axiom, p(a)).
fof(a2, axiom, ![X]: (p(X) => ?[Y]: r(X,Y))).
fof(a3, axiom, p(a) & s(a)).
fof(c, conjecture, ?[Y]: r(a,Y)).
"""
P2 = """
fof(a1, axiom, p(a)).
fof(c, conjecture, q(a)).
"""
P3 = """
fof(a1, axiom, ![X]: ?[Y]: r(X,Y)).
fof(c, conjecture, ?[Y]: ![X]: r(X,Y)).
"""
P4 = """
fof(a1, axiom, ![X]: ?[Y]: r(X,Y)).
fof(c, conjecture, r(a,b)).
"""
P5 = """
fof(a1, axiom, ![X]: ?[Y]: ?[Z]: r(X,Y,Z)).
fof(c, conjecture, ?[X]: ?[Y]: ?[Z]: r(X,Y,Z)).
"""
NESTED = """% Proof : Problems/P5.p
fof(a1, axiom, ![X]: ?[Y]: ?[Z]: r(X,Y,Z), file('Problems/P5.p', a1)).
fof(c, conjecture, ?[X]: ?[Y]: ?[Z]: r(X,Y,Z), file('Problems/P5.p', c)).
fof(nc, negated_conjecture, ~ ?[X]: ?[Y]: ?[Z]: r(X,Y,Z), inference(negated_conjecture, [status(cth)], [c])).
fof(sk, plain, ![X]: ?[Y]: r(X,Y,sK0(X)), inference(skolemize, [status(esa), new_symbols(skolem,[sK0]), skolemize(Z,sK0(X))], [a1])).
fof(bot, plain, $false, inference(consequence, [status(thm)], [sk, nc])).
"""
P6 = """
fof(a1, axiom, ![X]: ![Z]: ?[Y]: r(X,Z,Y)).
fof(c, conjecture, ?[X]: ?[Z]: ?[Y]: r(X,Z,Y)).
"""
SK2 = """% Proof : Problems/P6.p
fof(a1, axiom, ![X]: ![Z]: ?[Y]: r(X,Z,Y), file('Problems/P6.p', a1)).
fof(c, conjecture, ?[X]: ?[Z]: ?[Y]: r(X,Z,Y), file('Problems/P6.p', c)).
fof(nc, negated_conjecture, ~ ?[X]: ?[Z]: ?[Y]: r(X,Z,Y), inference(negated_conjecture, [status(cth)], [c])).
fof(sk, plain, ![X]: ![Z]: r(X,Z,sK0(X,Z)), inference(skolemize, [status(esa), new_symbols(skolem,[sK0]), skolemize(Y,sK0(X,Z))], [a1])).
fof(bot, plain, $false, inference(consequence, [status(thm)], [sk, nc])).
"""
SK2_STEP = "fof(sk, plain, ![X]: ![Z]: r(X,Z,sK0(X,Z)), inference(skolemize, [status(esa), new_symbols(skolem,[sK0]), skolemize(Y,sK0(X,Z))], [a1]))."
P7 = """
fof(a1, axiom, ~ ![X]: p(X)).
fof(c, conjecture, ?[X]: ~p(X)).
"""
NEG = """% Proof : Problems/P7.p
fof(a1, axiom, ~ ![X]: p(X), file('Problems/P7.p', a1)).
fof(c, conjecture, ?[X]: ~p(X), file('Problems/P7.p', c)).
fof(nc, negated_conjecture, ~ ?[X]: ~p(X), inference(negated_conjecture, [status(cth)], [c])).
fof(sk, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem,[sK0]), skolemize(X,sK0)], [a1])).
fof(bot, plain, $false, inference(consequence, [status(thm)], [sk, nc])).
"""
OK = """% Proof : Problems/P1.p
fof(a1, axiom, p(a), file('Problems/P1.p', a1)).
fof(a2, axiom, ![X]: (p(X) => ?[Y]: r(X,Y)), file('Problems/P1.p', a2)).
fof(c, conjecture, ?[Y]: r(a,Y), file('Problems/P1.p', c)).
fof(nc, negated_conjecture, ~ ?[Y]: r(a,Y), inference(negated_conjecture, [status(cth)], [c])).
fof(s1, plain, ?[Y]: r(a,Y), inference(mp, [status(thm)], [a1, a2])).
fof(bot, plain, $false, inference(consequence, [status(thm)], [nc, s1])).
"""
SK = """% Proof : Problems/P1.p
fof(a1, axiom, p(a), file('Problems/P1.p', a1)).
fof(a2, axiom, ![X]: (p(X) => ?[Y]: r(X,Y)), file('Problems/P1.p', a2)).
fof(c, conjecture, ?[Y]: r(a,Y), file('Problems/P1.p', c)).
fof(nc, negated_conjecture, ~ ?[Y]: r(a,Y), inference(negated_conjecture, [status(cth)], [c])).
fof(s1, plain, ?[Y]: r(a,Y), inference(mp, [status(thm)], [a1, a2])).
fof(s2, plain, r(a,sK0), inference(skolemize, [status(esa), new_symbols(skolem,[sK0]), skolemize(Y,sK0)], [s1])).
fof(s3, plain, ?[Y]: r(a,Y), inference(egen, [status(thm)], [s2])).
fof(bot, plain, $false, inference(consequence, [status(thm)], [nc, s3])).
"""
A1 = "fof(a1, axiom, p(a), file('Problems/P1.p', a1))."
NC = "inference(negated_conjecture, [status(cth)]"
MP = "inference(mp, [status(thm)]"
SKI = "inference(skolemize, [status(esa), new_symbols(skolem,[sK0]), skolemize(Y,sK0)]"

def sub(text, old, new):
    assert text.count(old) == 1, old
    return text.replace(old, new)

VALID, BROKEN, UNSOUND = "valid", "breaks the specification", "proves a non-theorem"

# (label, proof text, kind). The UNSOUND proofs "prove" a conjecture that
# does not follow from the axioms, so no profile may accept them.
CASES = [
    ("valid proof", OK, VALID),
    ("valid proof with a Skolemization", SK, VALID),
    ("valid proof with quoted names", sub(sub(OK, "fof(a1, axiom", "fof('a1', axiom"),
                                          "P1.p', a1)", "P1.p', 'a1')"), VALID),
    ("Skolemization under another existential", NESTED, VALID),
    ("Skolemization under another existential, wrong result",
     sub(NESTED, "![X]: ?[Y]: r(X,Y,sK0(X)), inference", "![X]: ?[Y]: r(X,sK0(X),Y), inference"), BROKEN),
    # orders, Skolem terms and freshness that the rules allow
    ("steps listed in reverse order",
     OK.split("\n", 1)[0] + "\n" + "\n".join(reversed(OK.strip().split("\n")[1:])) + "\n", VALID),
    ("Skolem term lists the universals in another order",
     sub(SK2, "r(X,Z,sK0(X,Z)), inference(skolemize, [status(esa), new_symbols(skolem,[sK0]), skolemize(Y,sK0(X,Z))]",
         "r(X,Z,sK0(Z,X)), inference(skolemize, [status(esa), new_symbols(skolem,[sK0]), skolemize(Y,sK0(Z,X))]"), VALID),
    ("Skolemization of ~![X]: an existential under a negation", NEG, VALID),
    ("Skolem symbol occurs in a consequence of another Skolemization", """% Proof : Problems/P8.p
fof(c, conjecture, (?[X]: ![Y]: r(X,Y)) => (![Y]: ?[X]: r(X,Y)), file('Problems/P8.p', c)).
fof(neg, negated_conjecture, (?[X]: ![Y]: r(X,Y)) & (?[Y]: ![X]: ~r(X,Y)), inference(negated_conjecture, [status(cth)], [c])).
fof(s1, plain, ?[X]: ![Y]: r(X,Y), inference(alpha, [status(thm)], [neg])).
fof(s2, plain, ?[Y]: ![X]: ~r(X,Y), inference(alpha, [status(thm)], [neg])).
fof(sk2, plain, ![X]: ~r(X,sK1), inference(skolemize, [status(esa), new_symbols(skolem,[sK1]), skolemize(Y,sK1)], [s2])).
fof(s4, plain, ~r(sK0,sK1), inference(instantiate, [status(thm)], [sk2])).
fof(sk1, plain, ![Y]: r(sK0,Y), inference(skolemize, [status(esa), new_symbols(skolem,[sK0]), skolemize(X,sK0)], [s1])).
fof(s3, plain, r(sK0,sK1), inference(instantiate, [status(thm)], [sk1])).
fof(bot, plain, $false, inference(resolution, [status(thm)], [s3, s4])).
""", VALID),
    ("Skolem symbol occurs in an unrelated tautology",
     sub(SK2, SK2_STEP, "fof(taut, plain, (q(sK0(a,a)) | ~q(sK0(a,a))), inference(tautology, [status(thm)], [])).\n" + SK2_STEP), VALID),
    # and the ones they do not
    ("a step depends on itself", sub(OK, "[status(thm)], [a1, a2])", "[status(thm)], [a1, a2, s1])"), BROKEN),
    ("Skolem term leaves out a universal it depends on",
     sub(SK2, "r(X,Z,sK0(X,Z)), inference(skolemize, [status(esa), new_symbols(skolem,[sK0]), skolemize(Y,sK0(X,Z))]",
         "r(X,Z,sK0(X)), inference(skolemize, [status(esa), new_symbols(skolem,[sK0]), skolemize(Y,sK0(X))]"), BROKEN),
    ("Skolem term built from another symbol",
     sub(SK2, "r(X,Z,sK0(X,Z)), inference(skolemize, [status(esa), new_symbols(skolem,[sK0])",
         "r(X,Z,sK0(X,Z)), inference(skolemize, [status(esa), new_symbols(skolem,[sK1])"), BROKEN),
    ("Skolemization of ~?[X]: a universal under a negation",
     sub(NEG, "fof(bot, plain, $false, inference(consequence, [status(thm)], [sk, nc])).",
         "fof(sk2, plain, ~ ~p(sK1), inference(skolemize, [status(esa), new_symbols(skolem,[sK1]), skolemize(X,sK1)], [nc])).\n"
         "fof(bot, plain, $false, inference(consequence, [status(thm)], [sk, nc]))."), BROKEN),
    ("Skolem symbol occurs in the parent",
     sub(SK2, SK2_STEP,
         "fof(s0, plain, ![X]: ![Z]: ?[Y]: (r(X,Z,Y) & (q(sK0(X,Z)) | ~q(sK0(X,Z)))), inference(weaken, [status(thm)], [a1])).\n"
         "fof(sk, plain, ![X]: ![Z]: (r(X,Z,sK0(X,Z)) & (q(sK0(X,Z)) | ~q(sK0(X,Z)))), inference(skolemize, [status(esa), new_symbols(skolem,[sK0]), skolemize(Y,sK0(X,Z))], [s0]))."), BROKEN),
    ("Skolem symbol introduced twice, the second listed first",
     sub(SK2, SK2_STEP,
         "fof(sk2, plain, ![X]: ![Z]: r(X,Z,sK0(X,Z)), inference(skolemize, [status(esa), new_symbols(skolem,[sK0]), skolemize(Y,sK0(X,Z))], [a1])).\n"
         "fof(dummy, plain, ![X]: ![Z]: r(X,Z,sK0(X,Z)), inference(copy, [status(thm)], [sk2])).\n" + SK2_STEP), BROKEN),
    ("derived step with role conjecture is negated", """% Proof : Problems/P2.p
fof(a1, axiom, p(a), file('Problems/P2.p', a1)).
fof(c, conjecture, q(a), file('Problems/P2.p', c)).
fof(fake, conjecture, p(a), inference(copy, [status(thm)], [a1])).
fof(nc, negated_conjecture, ~ p(a), inference(negated_conjecture, [status(cth)], [fake])).
fof(bot, plain, $false, inference(consequence, [status(thm)], [a1, nc])).
""", UNSOUND),
    ("axiom imported with role conjecture, then negated", """% Proof : Problems/P2.p
fof(a1, axiom, p(a), file('Problems/P2.p', a1)).
fof(fake, conjecture, p(a), file('Problems/P2.p', a1)).
fof(nc, negated_conjecture, ~ p(a), inference(negated_conjecture, [status(cth)], [fake])).
fof(bot, plain, $false, inference(consequence, [status(thm)], [a1, nc])).
""", UNSOUND),
    ("Skolemization of a formula with a free variable", """% Proof : Problems/P3.p
fof(a1, axiom, ![X]: ?[Y]: r(X,Y), file('Problems/P3.p', a1)).
fof(c, conjecture, ?[Y]: ![X]: r(X,Y), file('Problems/P3.p', c)).
fof(nc, negated_conjecture, ~ ?[Y]: ![X]: r(X,Y), inference(negated_conjecture, [status(cth)], [c])).
fof(s1, plain, ?[Y]: r(X,Y), inference(instantiate, [status(thm)], [a1])).
fof(s2, plain, r(X,sK0), inference(skolemize, [status(esa), new_symbols(skolem,[sK0]), skolemize(Y,sK0)], [s1])).
fof(bot, plain, $false, inference(consequence, [status(thm)], [s2, nc])).
""", UNSOUND),
    ("leaf with a free variable named like a renamed bound one", """% Proof : Problems/P4.p
fof(a1, axiom, ![X]: ?[Y]: r(X,V1), file('Problems/P4.p', a1)).
fof(c, conjecture, r(a,b), file('Problems/P4.p', c)).
fof(nc, negated_conjecture, ~ r(a,b), inference(negated_conjecture, [status(cth)], [c])).
fof(bot, plain, $false, inference(consequence, [status(thm)], [a1, nc])).
""", UNSOUND),
    ("axiom step with no source", sub(OK, A1, "fof(a1, axiom, p(a))."), BROKEN),
    ("file directive names a missing formula", sub(OK, "P1.p', a1)", "P1.p', nosuch)"), BROKEN),
    ("file directive names another formula", sub(OK, "P1.p', a1)", "P1.p', a3)"), BROKEN),
    ("leaf states an instance of the named formula",
     sub(OK, "fof(a2, axiom, ![X]: (p(X) => ?[Y]: r(X,Y)),", "fof(a2, axiom, (p(a) => ?[Y]: r(a,Y)),"), BROKEN),
    ("file directive without a formula name", sub(OK, "P1.p', a1)", "P1.p')"), BROKEN),
    ("file directive names another file", sub(OK, "file('Problems/P1.p', a1)", "file('Problems/P2.p', a1)"), BROKEN),
    ("imported step with role plain", sub(OK, "fof(a1, axiom, p(a), file", "fof(a1, plain, p(a), file"), BROKEN),
    ("premise is a problem formula that was never imported", sub(OK, A1 + "\n", ""), BROKEN),
    ("negated_conjecture without a status", sub(OK, NC, "inference(negated_conjecture, []"), BROKEN),
    ("negated_conjecture with status esa", sub(OK, NC, "inference(negated_conjecture, [status(esa)]"), BROKEN),
    ("negated_conjecture also claiming thm", sub(OK, NC, "inference(negated_conjecture, [status(cth), status(thm)]"), BROKEN),
    ("conjecture negated under another rule name", sub(OK, NC, "inference(negate, [status(cth)]"), BROKEN),
    ("inference without a status", sub(OK, MP, "inference(mp, []"), BROKEN),
    ("inference claiming thm and esa", sub(OK, MP, "inference(mp, [status(thm), status(esa)]"), BROKEN),
    ("Skolemization under another rule name", sub(SK, SKI, "inference(sk_intro, [status(esa)]"), BROKEN),
    ("Skolemization spelled skolemise", sub(SK, "inference(skolemize,", "inference(skolemise,"), BROKEN),
    ("Skolemization without skolemize(Var,Term)", sub(SK, ", skolemize(Y,sK0)]", "]"), BROKEN),
    ("Skolemization without new_symbols", sub(SK, " new_symbols(skolem,[sK0]),", ""), BROKEN),
    ("Skolemization with two skolemize annotations", sub(SK, "skolemize(Y,sK0)]", "skolemize(Y,sK0), skolemize(Z,sK9)]"), BROKEN),
    ("Skolemization declaring a second symbol", sub(SK, "new_symbols(skolem,[sK0])", "new_symbols(skolem,[sK0]), new_symbols(skolem,[sK7])"), BROKEN),
    ("Skolemization also claiming thm", sub(SK, "[status(esa), new", "[status(esa), status(thm), new"), BROKEN),
    ("Skolemization also claiming cth", sub(SK, "[status(esa), new", "[status(esa), status(cth), new"), BROKEN),
    ("proof with a unit that is not fof or cnf", OK + "tff(extra, axiom, $true).\n", BROKEN),
]


def units_of(text):
    out = []
    for lang, u in P.annotated_units(P.strip_comments(text)):
        f = [x.strip() for x in P.split_top(u)]
        out.append({"lang": lang, "name": f[0], "role": f[1], "formula": f[2],
                    "source": f[3] if len(f) > 3 else ""})
    return out

def emit(header, units):
    return header + "".join(
        f"{u['lang']}({u['name']}, {u['role']}, {u['formula']}"
        + (f", {u['source']}" if u["source"] else "") + ").\n" for u in units)

def record(u, rule=None, info=None, parents=None):
    s = P.parse_source(u["source"])
    return {**u, "source": "inference(%s,[%s],[%s])" % (
        rule or s.rule, ",".join(s.info if info is None else info),
        ",".join(s.parents if parents is None else parents))}

def is_status(item): return item.startswith("status(")
def leaf(u, s): return s.kind == "file"
def rule(name): return lambda u, s: s.kind == "inference" and s.rule == name
def other(u, s): return (s.kind == "inference" and s.rule not in ("negated_conjecture", "skolemize")
                         and [i for i in s.info if is_status(i)] == ["status(thm)"])

def redirect(u, s, cx):
    mine = cx["problem"].get(P.canon_name(s.name))
    for name, p in cx["problem"].items():
        if mine is not None and (p.role == "conjecture") == (mine.role == "conjecture") \
                and not P.equal_mod_alpha(p.formula, mine.formula):
            return {**u, "source": f"file({s.path},{name})"}

def second_parent(u, s, cx):
    extra = [n for n in cx["earlier"] if n not in s.parents]
    return record(u, parents=list(s.parents) + extra[:1]) if extra else None

# (label, which steps it applies to, the change)
MUTATIONS = [
    ("leaf: names another formula of the problem", leaf, redirect),
    ("leaf: names a formula that does not exist", leaf, lambda u, s, cx: {**u, "source": f"file({s.path},no_such_formula)"}),
    ("leaf: file directive without a name", leaf, lambda u, s, cx: {**u, "source": f"file({s.path})"}),
    ("leaf: no source", leaf, lambda u, s, cx: {**u, "source": ""}),
    ("leaf: role plain", leaf, lambda u, s, cx: {**u, "role": "plain"}),
    ("leaf: states (F | F) for the named F", leaf, lambda u, s, cx: {**u, "formula": f"(({u['formula']}) | ({u['formula']}))"}),
    ("negated_conjecture: no status", rule("negated_conjecture"), lambda u, s, cx: record(u, info=[i for i in s.info if not is_status(i)])),
    ("negated_conjecture: status esa", rule("negated_conjecture"), lambda u, s, cx: record(u, info=["status(esa)"])),
    ("negated_conjecture: also claims thm", rule("negated_conjecture"), lambda u, s, cx: record(u, info=list(s.info) + ["status(thm)"])),
    ("negated_conjecture: rule renamed", rule("negated_conjecture"), lambda u, s, cx: record(u, rule="negate")),
    ("skolemize: no skolemize(Var,Term)", rule("skolemize"), lambda u, s, cx: record(u, info=[i for i in s.info if not i.startswith("skolemize(")])),
    ("skolemize: no new_symbols", rule("skolemize"), lambda u, s, cx: record(u, info=[i for i in s.info if not i.startswith("new_symbols(")])),
    ("skolemize: also claims thm", rule("skolemize"), lambda u, s, cx: record(u, info=list(s.info) + ["status(thm)"])),
    ("skolemize: no status", rule("skolemize"), lambda u, s, cx: record(u, info=[i for i in s.info if not is_status(i)])),
    ("skolemize: rule renamed", rule("skolemize"), lambda u, s, cx: record(u, rule="skolemise")),
    ("skolemize: a second parent", rule("skolemize"), second_parent),
    ("inference: no status", other, lambda u, s, cx: record(u, info=[i for i in s.info if not is_status(i)])),
    ("inference: status esa", other, lambda u, s, cx: record(u, info=["status(esa)" if is_status(i) else i for i in s.info])),
    ("inference: also claims esa", other, lambda u, s, cx: record(u, info=list(s.info) + ["status(esa)"])),
    ("inference: role conjecture", other, lambda u, s, cx: {**u, "role": "conjecture"}),
    ("inference: role axiom", other, lambda u, s, cx: {**u, "role": "axiom"}),
    ("inference: cites itself", other, lambda u, s, cx: record(u, parents=list(s.parents) + [u["name"]])),
    ("proof: a unit that is not fof or cnf", None, None),
]

def mutants(proof):
    """One mutant per mutation, applied to the first step it fits."""
    text = open(os.path.join(CORPUS, proof + ".s")).read()
    header = "".join(l + "\n" for l in text.split("\n") if l.startswith("%"))
    units = units_of(text)
    problem = {P.canon_name(s.name): s for s in
               P.parse_tstp(open(os.path.join(CORPUS, "Problems", proof + ".p")).read())}
    for label, applies, change in MUTATIONS:
        if applies is None:
            yield label, emit(header, units) + "tff(extra, axiom, $true).\n"
            continue
        for i, u in enumerate(units):
            s = P.parse_source(u["source"])
            if applies(u, s):
                new = change(u, s, {"problem": problem, "earlier": [x["name"] for x in units[:i]]})
                if new is not None and new != u:
                    yield label, emit(header, units[:i] + [new] + units[i + 1:])
                    break


def reordered(proof):
    """The proof with its steps listed in reverse order, which the rules allow."""
    text = open(os.path.join(CORPUS, proof + ".s")).read()
    header = "".join(l + "\n" for l in text.split("\n") if l.startswith("%"))
    return emit(header, list(reversed(units_of(text))))

def verdict(cmd, text, problems):
    """Run the checker on `text` the way the competition did: proof only."""
    with tempfile.TemporaryDirectory() as d:
        os.symlink(problems, os.path.join(d, "Problems"))
        with open(os.path.join(d, "proof.s"), "w") as f:
            f.write(text)
        try:
            out = subprocess.run(cmd + ["--quiet", "--time-limit", "30", "proof.s"],
                                 cwd=d, capture_output=True, text=True, timeout=45).stdout
        except subprocess.TimeoutExpired:
            return "Timeout"
    m = re.search(r"SZS status (\w+)", out)
    return m.group(1) if m else "NoStatus"

def main(argv):
    cmd = shlex.split(argv[argv.index("--checker") + 1]) if "--checker" in argv else \
        [sys.executable, os.path.join(ROOT, "proover-check")]
    failures = 0

    with tempfile.TemporaryDirectory() as d:
        for name, text in (("P1.p", P1), ("P2.p", P2), ("P3.p", P3), ("P4.p", P4), ("P5.p", P5),
                           ("P6.p", P6), ("P7.p", P7),
                           ("P8.p", "fof(c, conjecture, (?[X]: ![Y]: r(X,Y)) => (![Y]: ?[X]: r(X,Y))).\n")):
            with open(os.path.join(d, name), "w") as f:
                f.write(text)
        print("hand-written cases:")
        with ThreadPoolExecutor(4) as pool:
            got = list(pool.map(lambda c: verdict(cmd, c[1], d), CASES))
        for (label, _, kind), v in zip(CASES, got):
            ok = (v == "VerifiedGood") == (kind == VALID)
            failures += not ok
            print(f"  [{'PASS' if ok else 'FAIL'}] {label:56s} -> {v}")
        if "--checker" not in argv:
            # the tolerant profile accepts proofs that break the specification
            # (and, being the 1.0 rules, rejects some valid ones), but it must
            # never accept a proof of a non-theorem
            print("\ntolerant profile, unsound proofs only:")
            sound = [c for c in CASES if c[2] == UNSOUND]
            with ThreadPoolExecutor(4) as pool:
                got = list(pool.map(lambda c: verdict(
                    cmd + ["--profile", "tolerant"], c[1], d), sound))
            for (label, _, kind), v in zip(sound, got):
                ok = v != "VerifiedGood"
                failures += not ok
                print(f"  [{'PASS' if ok else 'FAIL'}] {label:56s} -> {v}")

    if not os.path.isdir(CORPUS):
        print(f"\n{CORPUS} not found; skipping the mutations "
              "(python3 tests/proover2026.py --fetch downloads it)")
        return 1 if failures else 0

    truth = dict(line.split() for line in open(TRUTH))
    problems = os.path.join(CORPUS, "Problems")
    good = [p for p in sorted(truth) if truth[p] == "good"
            and os.path.getsize(os.path.join(CORPUS, p + ".s")) < 100_000]
    with ThreadPoolExecutor(4) as pool:
        base = list(pool.map(lambda p: verdict(
            cmd, open(os.path.join(CORPUS, p + ".s")).read(), problems), good))
    bases = [p for p, v in zip(good, base) if v == "VerifiedGood"]
    jobs = [(p, label, text) for p in bases for label, text in mutants(p)]
    with ThreadPoolExecutor(4) as pool:
        got = list(pool.map(lambda j: verdict(cmd, j[2], problems), jobs))

    print(f"\nmutations of the {len(bases)} valid competition proofs the checker accepts:")
    for label, _, _ in MUTATIONS:
        rows = [(p, v) for (p, l, _), v in zip(jobs, got) if l == label]
        accepted = [p for p, v in rows if v == "VerifiedGood"]
        failures += len(accepted)
        print(f"  [{'PASS' if not accepted else 'FAIL'}] {label:46s} {len(rows):3d} mutants, "
              f"{len(accepted):3d} accepted" + (f"  e.g. {accepted[0]}" if accepted else ""))
    with ThreadPoolExecutor(4) as pool:
        again = list(pool.map(lambda p: verdict(cmd, reordered(p), problems), bases))
    lost = [p for p, v in zip(bases, again) if v != "VerifiedGood"]
    failures += len(lost)
    print(f"\nthe same {len(bases)} proofs with their steps in reverse order (still valid):")
    print(f"  [{'PASS' if not lost else 'FAIL'}] {len(bases) - len(lost)} still accepted"
          + (f", lost: {' '.join(lost)}" if lost else ""))
    total = sum(v == "VerifiedGood" for v in got)
    print(f"\n{len(jobs)} mutants, {total} accepted; "
          f"{sum(c[2] != VALID for c in CASES)} hand-written invalid cases")
    return 1 if failures else 0

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
