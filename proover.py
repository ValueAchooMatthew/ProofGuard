"""Verifier for TSTP refutation proofs of FOF problems (ProoVer 2026).

Verdicts: VerifiedGood, VerifiedBad, Unknown. Running out of the wall-clock
budget raises OutOfTime, which the CLI reports as Timeout. The external ATP
is only ever invoked on a single step together with its own premises.

There are two profiles. The strict profile (the default) checks a proof
against the ProoVer 2026 certificate specification: a step is accepted only
when every obligation the specification puts on that kind of step has been
discharged. The tolerant profile is the ProofGuard 1.0 checker, which also
accepts the dialects of real ATP systems and only establishes that a proof
is logically sound.
"""
from __future__ import annotations
import os, re, subprocess, tempfile, itertools, shutil, time
from dataclasses import dataclass, field

VERSION = "1.1"


class OutOfTime(Exception):
    pass


class Deadline:
    def __init__(self, seconds=None):
        self.start = time.monotonic()
        self.limit = seconds

    def remaining(self):
        if self.limit is None:
            return float("inf")
        return self.limit - (time.monotonic() - self.start)

    def check(self, margin=0.5):
        if self.remaining() < margin:
            raise OutOfTime()


@dataclass(frozen=True)
class Var:   name: str
@dataclass(frozen=True)
class Func:
    name: str
    args: tuple = ()

@dataclass(frozen=True)
class Atom:  pred: str; args: tuple = ()
@dataclass(frozen=True)
class Eq:    lhs: object; rhs: object
@dataclass(frozen=True)
class Not:   sub: object
@dataclass(frozen=True)
class And:   l: object; r: object
@dataclass(frozen=True)
class Or:    l: object; r: object
@dataclass(frozen=True)
class Implies: l: object; r: object
@dataclass(frozen=True)
class Iff:   l: object; r: object
@dataclass(frozen=True)
class Forall: var: str; body: object
@dataclass(frozen=True)
class Exists: var: str; body: object

TOKEN = re.compile(r"""
    \s+                                   |
    (?P<op><=>|=>|<=|<~>|~\||~&|!=|[&|~()\[\],:=?!]) |
    (?P<id>[A-Za-z_$][A-Za-z0-9_$]*)      |
    (?P<num>\d+(?:\.\d+)?)                |
    (?P<q>'(?:[^'\\]|\\.)*'|"(?:[^"\\]|\\.)*")
""", re.VERBOSE)

def tokenize(s):
    residue = TOKEN.sub('', s)
    if residue:
        raise SyntaxError(f"unexpected character {residue[:10]!r}")
    return [a or b or c or d for a, b, c, d in TOKEN.findall(s) if a or b or c or d]

def _is_var_name(name):
    return name[0].isupper() or name[0] == '_'

class Parser:
    def __init__(self, toks): self.t = toks; self.i = 0
    def peek(self): return self.t[self.i] if self.i < len(self.t) else None
    def next(self):
        if self.i >= len(self.t):
            raise SyntaxError("unexpected end of formula")
        x = self.t[self.i]; self.i += 1; return x
    def expect(self, x):
        got = self.next()
        if got != x: raise SyntaxError(f"expected {x!r}, got {got!r}")

    def formula(self): return self.iff()
    def iff(self):
        l = self.implies()
        while self.peek() in ('<=>', '<~>', '~&', '~|'):
            op = self.next(); r = self.implies()
            l = {'<=>': Iff, '<~>': lambda x, y: Not(Iff(x, y)),
                 '~&': lambda x, y: Not(And(x, y)),           # nand
                 '~|': lambda x, y: Not(Or(x, y))}[op](l, r)   # nor
        return l
    def implies(self):
        l = self.disj()
        if self.peek() == '=>': self.next(); return Implies(l, self.implies())
        if self.peek() == '<=': self.next(); return Implies(self.implies(), l)
        return l
    def disj(self):
        l = self.conj()
        while self.peek() == '|': self.next(); l = Or(l, self.conj())
        return l
    def conj(self):
        l = self.unary()
        while self.peek() == '&': self.next(); l = And(l, self.unary())
        return l
    def unary(self):
        if self.peek() == '~': self.next(); return Not(self.unary())
        if self.peek() in ('!', '?'):
            q = self.next(); self.expect('[')
            vs = [self.next()]
            while self.peek() == ',': self.next(); vs.append(self.next())
            self.expect(']'); self.expect(':')
            body = self.unary()
            for v in reversed(vs):
                body = Forall(v, body) if q == '!' else Exists(v, body)
            return body
        if self.peek() == '(':
            self.next(); f = self.formula(); self.expect(')'); return f
        return self.atom()
    def atom(self):
        name = self.next()
        if name == '$false': return Atom('$false')
        if name == '$true':  return Atom('$true')
        args = ()
        if self.peek() == '(':
            self.next(); args = [self.term()]
            while self.peek() == ',': self.next(); args.append(self.term())
            self.expect(')'); args = tuple(args)
        if self.peek() in ('=', '!='):
            op = self.next()
            lhs = Func(name, args) if args or not _is_var_name(name) else Var(name)
            rhs = self.term()
            eq = Eq(lhs, rhs)
            return Not(eq) if op == '!=' else eq
        return Atom(name, args)
    def term(self):
        name = self.next()
        if self.peek() == '(':
            self.next(); args = [self.term()]
            while self.peek() == ',': self.next(); args.append(self.term())
            self.expect(')'); return Func(name, tuple(args))
        return Var(name) if _is_var_name(name) else Func(name, ())

def parse_formula(s):
    p = Parser(tokenize(s))
    f = p.formula()
    if p.peek() is not None:
        raise SyntaxError(f"trailing tokens after formula: {p.peek()!r}")
    return f

def parse_term(s):
    p = Parser(tokenize(s))
    t = p.term()
    if p.peek() is not None:
        raise SyntaxError(f"trailing tokens after term: {p.peek()!r}")
    return t


def subst_term(t, m):
    if isinstance(t, Var):  return m.get(t.name, t)
    if isinstance(t, Func): return Func(t.name, tuple(subst_term(a, m) for a in t.args))
    return t

_fresh = (f"_z{i}" for i in itertools.count())
def subst(f, m):
    if isinstance(f, Atom): return Atom(f.pred, tuple(subst_term(a, m) for a in f.args))
    if isinstance(f, Eq):   return Eq(subst_term(f.lhs, m), subst_term(f.rhs, m))
    if isinstance(f, Not):  return Not(subst(f.sub, m))
    if isinstance(f, (And, Or, Implies, Iff)):
        return type(f)(subst(f.l, m), subst(f.r, m))
    if isinstance(f, (Forall, Exists)):
        cls = type(f)
        if f.var in m:
            m = {k: v for k, v in m.items() if k != f.var}
        if any(f.var in term_vars(v) for v in m.values()):
            nv = next(_fresh)
            body = subst(f.body, {f.var: Var(nv)})
            return cls(nv, subst(body, m))
        return cls(f.var, subst(f.body, m))
    return f

def term_vars(t):
    if isinstance(t, Var):  return {t.name}
    if isinstance(t, Func): return set().union(*[term_vars(a) for a in t.args]) if t.args else set()
    return set()

def free_vars(f):
    if isinstance(f, Atom): return set().union(*[term_vars(a) for a in f.args]) if f.args else set()
    if isinstance(f, Eq):   return term_vars(f.lhs) | term_vars(f.rhs)
    if isinstance(f, Not):  return free_vars(f.sub)
    if isinstance(f, (And, Or, Implies, Iff)): return free_vars(f.l) | free_vars(f.r)
    if isinstance(f, (Forall, Exists)): return free_vars(f.body) - {f.var}
    return set()

def universal_closure(f):
    for v in sorted(free_vars(f), reverse=True):
        f = Forall(v, f)
    return f

def pp_term(t):
    if isinstance(t, Var):  return t.name
    if isinstance(t, Func): return t.name + (f"({','.join(pp_term(a) for a in t.args)})" if t.args else "")
    raise TypeError(f"not a term: {t!r}")

def pp(f):
    if isinstance(f, Atom): return f.pred + (f"({','.join(pp_term(a) for a in f.args)})" if f.args else "")
    if isinstance(f, Eq):   return f"{pp_term(f.lhs)}={pp_term(f.rhs)}"
    if isinstance(f, Not):
        if isinstance(f.sub, Eq):
            return f"{pp_term(f.sub.lhs)}!={pp_term(f.sub.rhs)}"
        return f"~({pp(f.sub)})"
    if isinstance(f, And):  return f"({pp(f.l)} & {pp(f.r)})"
    if isinstance(f, Or):   return f"({pp(f.l)} | {pp(f.r)})"
    if isinstance(f, Implies): return f"({pp(f.l)} => {pp(f.r)})"
    if isinstance(f, Iff):  return f"({pp(f.l)} <=> {pp(f.r)})"
    if isinstance(f, Forall): return f"(![{f.var}]:{pp(f.body)})"
    if isinstance(f, Exists): return f"(?[{f.var}]:{pp(f.body)})"
    raise TypeError(f"not a formula: {f!r}")

def alpha_norm(f):
    counter = itertools.count()
    def t(x, env):
        if isinstance(x, Var):  return Var(env.get(x.name, x.name))
        if isinstance(x, Func): return Func(x.name, tuple(t(a, env) for a in x.args))
    def go(g, env):
        if isinstance(g, Atom): return Atom(g.pred, tuple(t(a, env) for a in g.args))
        if isinstance(g, Eq):   return Eq(t(g.lhs, env), t(g.rhs, env))
        if isinstance(g, Not):  return Not(go(g.sub, env))
        if isinstance(g, (And, Or, Implies, Iff)):
            return type(g)(go(g.l, env), go(g.r, env))
        if isinstance(g, (Forall, Exists)):
            nv = f"#{next(counter)}"    # not a TPTP name: cannot clash with a free variable
            return type(g)(nv, go(g.body, {**env, g.var: nv}))
    return go(f, {})

def equal_mod_alpha(a, b):
    return a == b or alpha_norm(a) == alpha_norm(b)

def func_symbols(f):
    out = set()
    def t(x):
        if isinstance(x, Func):
            out.add(x.name)
            for a in x.args: t(a)
    def go(g):
        if isinstance(g, Atom):
            for a in g.args: t(a)
        elif isinstance(g, Eq): t(g.lhs); t(g.rhs)
        elif isinstance(g, Not): go(g.sub)
        elif isinstance(g, (And, Or, Implies, Iff)): go(g.l); go(g.r)
        elif isinstance(g, (Forall, Exists)): go(g.body)
    go(f); return out

def pred_symbols(f):
    out = set()
    def go(g):
        if isinstance(g, Atom):
            if g.pred not in ('$false', '$true'):
                out.add(g.pred)
        elif isinstance(g, Not): go(g.sub)
        elif isinstance(g, (And, Or, Implies, Iff)): go(g.l); go(g.r)
        elif isinstance(g, (Forall, Exists)): go(g.body)
    go(f); return out

def negate(f):
    return f.sub if isinstance(f, Not) else Not(f)


def strip_closure(f):
    while isinstance(f, Forall):
        f = f.body
    return f

def _clause_literals(f):
    lits = []
    def go(g):
        if isinstance(g, Or):
            return go(g.l) and go(g.r)
        neg = isinstance(g, Not)
        if neg:
            g = g.sub
        if isinstance(g, (Atom, Eq)):
            lits.append((neg, g))
            return True
        return False
    return lits if go(strip_closure(f)) else None

def _match_term(a, b, m, rm):
    if isinstance(a, Var) and isinstance(b, Var):
        if m.get(a.name, b.name) != b.name or rm.get(b.name, a.name) != a.name:
            return False
        m[a.name] = b.name; rm[b.name] = a.name
        return True
    if isinstance(a, Func) and isinstance(b, Func):
        return (a.name == b.name and len(a.args) == len(b.args)
                and all(_match_term(x, y, m, rm) for x, y in zip(a.args, b.args)))
    return False

def _match_atom(a, b, m, rm):
    if isinstance(a, Atom) and isinstance(b, Atom):
        return (a.pred == b.pred and len(a.args) == len(b.args)
                and all(_match_term(x, y, m, rm) for x, y in zip(a.args, b.args)))
    if isinstance(a, Eq) and isinstance(b, Eq):
        save = dict(m), dict(rm)
        if _match_term(a.lhs, b.lhs, m, rm) and _match_term(a.rhs, b.rhs, m, rm):
            return True
        m.clear(); m.update(save[0]); rm.clear(); rm.update(save[1])
        return (_match_term(a.lhs, b.rhs, m, rm)
                and _match_term(a.rhs, b.lhs, m, rm))
    return False

def clause_equal(a, b):
    """Clause equality up to variable renaming, literal order, and equation
    orientation."""
    la, lb = _clause_literals(a), _clause_literals(b)
    if la is None or lb is None or len(la) != len(lb):
        return False

    def backtrack(i, used, m, rm):
        if i == len(la):
            return True
        nega, atoma = la[i]
        for j, (negb, atomb) in enumerate(lb):
            if j in used or nega != negb:
                continue
            m2, rm2 = dict(m), dict(rm)
            if _match_atom(atoma, atomb, m2, rm2):
                if backtrack(i + 1, used | {j}, m2, rm2):
                    return True
        return False

    return backtrack(0, frozenset(), {}, {})

def same_formula(a, b):
    return equal_mod_alpha(a, b) or clause_equal(a, b)


@dataclass
class Step:
    name: str
    role: str
    formula: object
    source_kind: str = None            # None | 'file' | 'inference' | 'introduced' | 'copy'
    file_ref: str = None
    rule: str = None
    status: str = None
    premises: list = field(default_factory=list)
    annots: str = ""
    opaque_premises: bool = False
    statuses: frozenset = frozenset()  # every status() across a nested chain
    source: str = ""                   # the source field exactly as written


def strip_comments(text):
    out = []
    for line in text.split("\n"):
        if "%" in line or "#" in line:
            quoted = False
            for i, c in enumerate(line):
                if c == "'":
                    quoted = not quoted
                elif c in "%#" and not quoted:
                    line = line[:i]
                    break
        out.append(line)
    return "\n".join(out)

def annotated_units(text, deadline=None, spans=None):
    units = []
    n = len(text)
    i = 0
    while True:
        if deadline is not None:
            deadline.check()
        jf = text.find("fof", i)
        jc = text.find("cnf", i)
        js = [j for j in (jf, jc) if j != -1]
        if not js:
            break
        j = min(js)
        lang = text[j:j + 3]
        before = text[j - 1] if j > 0 else ""
        if before.isalnum() or before in ("_", "$"):
            i = j + 3
            continue
        k = j + 3
        while k < n and text[k].isspace():
            k += 1
        if k >= n or text[k] != "(":
            i = j + 3
            continue
        depth = 0
        quoted = False
        start = k + 1
        p = k
        while p < n:
            c = text[p]
            if quoted:
                if c == "'":
                    quoted = False
            elif c == "'":
                quoted = True
            elif c == "(":
                depth += 1
            elif c == ")":
                depth -= 1
                if depth == 0:
                    units.append((lang, text[start:p]))
                    if spans is not None:
                        spans.append((j, p + 1))
                    break
            p += 1
        else:
            raise SyntaxError("unbalanced parentheses in annotated formula")
        i = p + 1
    return units

def split_top(s, sep=','):
    depth = 0; quoted = False; cur = ''; out = []
    for c in s:
        if quoted:
            cur += c
            if c == "'":
                quoted = False
            continue
        if c == "'":
            quoted = True; cur += c; continue
        if c in '([': depth += 1
        elif c in ')]': depth -= 1
        if c == sep and depth == 0:
            out.append(cur); cur = ''
        else:
            cur += c
    if cur.strip():
        out.append(cur)
    return out

_NAME = re.compile(r"^(?:[A-Za-z0-9_$]+|'(?:[^'\\]|\\.)*')$")
_STATUS = re.compile(r"status\((\w+)\)")
_FILE = re.compile(r"file\(\s*('(?:[^'\\]|\\.)*'|[^',()]*)\s*"
                   r"(?:,\s*([\w$]+|'(?:[^'\\]|\\.)*'))?\s*\)\s*$")

def _inference_fields(src):
    s = src.strip()
    if not s.startswith("inference"):
        return None
    body = s[len("inference"):].strip()
    if not (body.startswith("(") and body.endswith(")")):
        return None
    fields = [f.strip() for f in split_top(body[1:-1])]
    if len(fields) != 3:
        return None
    annots, plist = fields[1], fields[2]
    if not (annots.startswith("[") and annots.endswith("]")
            and plist.startswith("[") and plist.endswith("]")):
        return None
    return fields[0], annots[1:-1], plist[1:-1]

def _flatten_inference(src):
    """Flatten a possibly-nested inference(...) term into
    (rule, status, all statuses, leaf premise names, annots, opaque)."""
    f = _inference_fields(src)
    if f is None:
        return None
    rule, annots, plist = f
    sm = _STATUS.search(annots)
    status = sm.group(1) if sm else None
    statuses = {status}
    leaves, opaque = [], False
    for p in (q.strip() for q in split_top(plist)):
        if not p:
            continue
        if _NAME.match(p):
            leaves.append(p)
        elif p.startswith("inference"):
            sub = _flatten_inference(p)
            if sub is None:
                opaque = True
            else:
                statuses |= sub[2]; leaves += sub[3]; opaque |= sub[5]
        elif p.startswith("theory(") or p.startswith("introduced("):
            pass
        else:
            opaque = True
    return rule, status, frozenset(statuses), leaves, annots, opaque

def parse_annotated(lang, unit):
    parts = split_top(unit)
    if len(parts) < 3:
        raise SyntaxError(f"annotated formula with only {len(parts)} fields")
    name = parts[0].strip()
    role = parts[1].strip()
    formula = parse_formula(parts[2].strip())
    if lang == 'cnf':
        formula = universal_closure(formula)
    step = Step(name, role, formula)
    if len(parts) > 3:
        source = parts[3].strip()
        step.source = source
        fm = _FILE.match(source)
        im = re.match(r"introduced\(\s*(\w+)", source)
        flat = None if (fm or im) else _flatten_inference(source)
        if fm:
            step.source_kind = 'file'
            step.file_ref = fm.group(2)
        elif im:
            step.source_kind = 'introduced'
            step.rule = im.group(1)
        elif flat:
            step.source_kind = 'inference'
            (step.rule, step.status, step.statuses,
             step.premises, step.annots, step.opaque_premises) = flat
        elif _NAME.match(source):
            step.source_kind = 'copy'
            step.file_ref = source
    return step

def parse_tstp(text, deadline=None):
    return [parse_annotated(lang, u)
            for lang, u in annotated_units(strip_comments(text), deadline)]


_INCLUDE = re.compile(r"include\(\s*'([^']+)'\s*(?:,\s*\[[^\]]*\])?\s*\)\s*\.")

def expand_includes(text, base_dir, depth=0):
    """Inline include('...') directives, resolving against base_dir then $TPTP."""
    if depth > 8:
        raise SyntaxError("include() nesting too deep")

    def repl(m):
        rel = m.group(1)
        for root in (base_dir, os.environ.get("TPTP")):
            if root:
                cand = os.path.join(root, rel)
                if os.path.exists(cand):
                    with open(cand) as f:
                        return expand_includes(f.read(), base_dir, depth + 1)
        raise SyntaxError(f"cannot resolve include({rel!r})")

    return _INCLUDE.sub(repl, strip_comments(text))


GOOD, BAD, UNSURE = "GOOD", "BAD", "UNSURE"

class ATP:
    BIN = os.environ.get("ATP_EPROVER_BIN", "eprover")
    PER_CALL = 10

    @staticmethod
    def _bin_path():
        candidate = ATP.BIN
        path = candidate if os.path.isabs(candidate) else shutil.which(candidate)
        if path and os.access(path, os.X_OK):
            return path
        import sys
        for base in (getattr(sys, '_MEIPASS', None),
                     os.path.dirname(os.path.abspath(sys.argv[0] or '.')),
                     os.path.dirname(os.path.abspath(__file__))):
            if base:
                cand = os.path.join(base, "eprover")
                if os.path.isfile(cand) and os.access(cand, os.X_OK):
                    return cand
        raise RuntimeError(
            f"external prover {ATP.BIN!r} is not available; "
            "install E or set ATP_EPROVER_BIN")

    @staticmethod
    def _run(problem, deadline):
        budget = min(ATP.PER_CALL, deadline.remaining() - 1.0)
        if budget < 1.0:
            raise OutOfTime()
        cpu = max(1, int(budget))
        with tempfile.NamedTemporaryFile('w', suffix='.p', delete=False) as fh:
            fh.write(problem); path = fh.name
        try:
            out = subprocess.run(
                [ATP._bin_path(), "--auto", "--silent", "-s", "--proof-object=0",
                 f"--cpu-limit={cpu}", path],
                capture_output=True, text=True, timeout=budget + 3).stdout
        except subprocess.TimeoutExpired:
            return "Timeout"
        finally:
            try: os.unlink(path)
            except OSError: pass
        m = re.search(r'SZS status (\w+)', out)
        return m.group(1) if m else "Unknown"

    @staticmethod
    def entails(premises, conclusion, deadline):
        """GOOD if premises |= conclusion, BAD if demonstrably not, else UNSURE."""
        ax = "\n".join(f"fof(p{i}, axiom, {pp(universal_closure(p.formula))})."
                       for i, p in enumerate(premises))
        goal = universal_closure(conclusion)
        pos = ATP._run(ax + f"\nfof(goal, conjecture, {pp(goal)}).", deadline)
        if pos in ("Theorem", "ContradictoryAxioms"):
            return GOOD, "ATP confirms premises entail the step"
        if pos == "CounterSatisfiable":
            return BAD, "ATP shows premises do NOT entail the step"
        neg = ATP._run(ax + f"\nfof(goal, conjecture, {pp(negate(goal))}).", deadline)
        if neg == "Theorem":
            return BAD, "ATP shows premises entail the NEGATION of the step"
        return UNSURE, "ATP could not confirm the step"

    @staticmethod
    def decide(formula, deadline):
        return ATP._run(f"fof(goal, conjecture, {pp(formula)}).", deadline)


def check_negated_conjecture(step, parents, deadline):
    statuses = step.statuses or {step.status}
    if any(x is not None for x in statuses) and not statuses & {'cth', 'esa'}:
        return BAD, f"negating the conjecture requires status cth, got {step.status}"
    if len(parents) != 1:
        return BAD, "negated_conjecture must have exactly one parent"
    parent = parents[0]
    if parent.role != 'conjecture':
        return BAD, f"negated_conjecture parent {parent.name} is not the conjecture"
    r = ATP.decide(Iff(universal_closure(step.formula),
                       negate(universal_closure(parent.formula))), deadline)
    if r == "Theorem":
        return GOOD, "formula is the correct negation of the conjecture"
    if r == "CounterSatisfiable":
        return BAD, "formula is NOT the negation of the conjecture"
    return UNSURE, "prover could not decide negation equivalence"

# two annotation dialects: skolemize(Var, Term) | skolemized(Var) ... bind(Var, Term)
_SK_NEW  = re.compile(r"new_symbols\(\s*skolem\s*,\s*\[([\w$,\s]+)\]\s*\)")
_SK_PAIR = re.compile(r"skolemi[sz]e\(\s*(\w+)\s*,\s*(.+?)\)\s*(?:,|$)")
_SK_VAR  = re.compile(r"skolemi[sz]ed\(\s*(\w+)\s*\)")
_SK_BIND = re.compile(r"bind\(\s*(\w+)\s*,\s*(.+?)\)\s*$")

def _skolem_annotation(annots):
    ns = _SK_NEW.search(annots)
    if not ns:
        return None
    new_syms = [s.strip() for s in ns.group(1).split(",") if s.strip()]
    rest = annots[:ns.start()] + annots[ns.end():]
    pm = _SK_PAIR.search(rest)
    if pm:
        return new_syms, pm.group(1), pm.group(2)
    vm = _SK_VAR.search(rest)
    bm = _SK_BIND.search(rest.strip())
    if vm and bm:
        if vm.group(1) != bm.group(1):
            return new_syms, None, None
        return new_syms, bm.group(1), bm.group(2)
    return None

def check_skolemize(step, parents, seen_symbols, deadline):
    if step.status != 'esa':
        return BAD, f"skolemize must have status esa, got {step.status}"
    if len(parents) != 1:
        return UNSURE, "expected exactly one parent"

    ann = _skolem_annotation(step.annots)
    if ann is None:
        return UNSURE, "skolemize annotations missing or not understood"
    new_syms, sk_var, term_text = ann
    if sk_var is None:
        return BAD, "skolemize annotations are inconsistent"
    if len(new_syms) != 1:
        return UNSURE, "multi-symbol skolemization not supported"
    return skolemization(parents[0].formula, step.formula, new_syms[0],
                         sk_var, term_text, seen_symbols)

def skolemization(parent, formula, new_sym, sk_var, term_text, seen_symbols,
                  strict=False):
    """Is `formula` the result of replacing the existential `sk_var` of
    `parent` by the term `term_text`, where that term is the fresh symbol
    `new_sym` applied to the universals in scope?

    With `strict`, the prefix may also contain negations (so ~![X]: p(X)
    Skolemizes X), and the Skolem term may list the universals in any order.
    A term that leaves out a universal the eliminated variable depends on is
    a flaw. Any other departure from the expected term is left undecided,
    since the competition's rules and proceedings disagree on it."""
    if new_sym in seen_symbols:
        return BAD, f"Skolem symbol {new_sym} is not fresh (already in use)"

    # Walk the quantifier prefix down to the existential being eliminated.
    # Other existentials may sit above it (as in ![X]: ?[Y]: ?[Z] when Z is
    # eliminated first); the Skolem term depends only on the universals.
    # Under a negation a quantifier changes kind: ~![X] is an existential.
    prefix, node, negated = [], parent, False   # prefix: (node, is_existential)
    while True:
        if strict and isinstance(node, Not):
            prefix.append((node, None)); negated = not negated; node = node.sub
        elif isinstance(node, (Forall, Exists)):
            existential = isinstance(node, Exists) != negated
            if existential and node.var == sk_var:
                break
            prefix.append((node, existential)); node = node.body
        else:
            return BAD, f"no existential {sk_var} at the expected position"
    scope = [q.var for q, ex in prefix if ex is False]
    nested = any(ex for _, ex in prefix)
    bound = [q.var for q, ex in prefix if ex is not None]
    if len(set(bound) | {sk_var}) != len(bound) + 1:
        return UNSURE, "quantified variable names repeat in the prefix; cannot check"

    try:
        bind_term = parse_term(term_text.strip())
    except SyntaxError:
        return UNSURE, "cannot parse skolem binding term"
    expected = Func(new_sym, tuple(Var(v) for v in scope))
    if bind_term != expected and strict:
        v, why = _skolem_term(bind_term, expected, scope, node.body)
        if v is not None:
            return v, why
    elif bind_term != expected:
        if nested:
            # only the exact term is checked under existentials; anything else
            # is left undecided rather than rejected
            return UNSURE, (f"Skolem term {pp_term(bind_term)} under other "
                            f"existentials is not {pp_term(expected)}; cannot check")
        return BAD, (f"Skolem term {pp_term(bind_term)} should be {pp_term(expected)} "
                     "(fresh symbol applied to exactly the universals in scope)")

    rebuilt = subst(node.body, {sk_var: bind_term})
    for q, ex in reversed(prefix):
        rebuilt = Not(rebuilt) if ex is None else type(q)(q.var, rebuilt)
    if equal_mod_alpha(rebuilt, formula):
        return GOOD, f"correct Skolemization introducing {pp_term(bind_term)}"
    return BAD, (f"Skolemization result is wrong; expected {pp(rebuilt)} "
                 f"but the step states {pp(formula)}")


def _skolem_term(term, expected, scope, body):
    """Judge a Skolem term that is not exactly `expected`. Returns (None, None)
    if it is the same symbol applied to the same universals in another order."""
    sym = expected.name
    if not (isinstance(term, Func) and term.name == sym):
        return BAD, (f"Skolem term {pp_term(term)} is not built from the declared "
                     f"Skolem symbol {sym}")
    names = [a.name for a in term.args if isinstance(a, Var)]
    if len(names) == len(term.args) and len(set(names)) == len(names) \
            and set(names) == set(scope):
        return None, None
    missing = [v for v in scope if v in free_vars(body) and v not in term_vars(term)]
    if missing:
        return BAD, (f"Skolem term {pp_term(term)} does not depend on "
                     f"{', '.join(missing)}, which the eliminated variable depends on")
    return UNSURE, (f"Skolem term {pp_term(term)} is not {pp_term(expected)} up to "
                    "argument order; the competition rules require exactly the "
                    "universals in scope, its proceedings at least those in the formula")

def _sk_occurrences(f, sk):
    occs = []
    def t(x):
        if isinstance(x, Func):
            if x.name == sk:
                occs.append(x.args)
            for a in x.args: t(a)
    def go(g):
        if isinstance(g, Atom):
            for a in g.args: t(a)
        elif isinstance(g, Eq): t(g.lhs); t(g.rhs)
        elif isinstance(g, Not): go(g.sub)
        elif isinstance(g, (And, Or, Implies, Iff)): go(g.l); go(g.r)
        elif isinstance(g, (Forall, Exists)): go(g.body)
    go(f); return occs

def _replace_skterm(f, sk, args, var):
    target = Func(sk, args)
    def t(x):
        if x == target:
            return Var(var)
        if isinstance(x, Func):
            return Func(x.name, tuple(t(a) for a in x.args))
        return x
    def go(g):
        if isinstance(g, Atom): return Atom(g.pred, tuple(t(a) for a in g.args))
        if isinstance(g, Eq):   return Eq(t(g.lhs), t(g.rhs))
        if isinstance(g, Not):  return Not(go(g.sub))
        if isinstance(g, (And, Or, Implies, Iff)):
            return type(g)(go(g.l), go(g.r))
        if isinstance(g, (Forall, Exists)):
            return type(g)(g.var, go(g.body))
        return g
    return go(f)

def _binder_info(f):
    counts, above, kinds = {}, {}, {}
    def go(g, anc):
        if isinstance(g, (Forall, Exists)):
            counts[g.var] = counts.get(g.var, 0) + 1
            above.setdefault(g.var, set()).update(anc)
            kinds[g.var] = type(g)
            go(g.body, anc | {g.var})
        elif isinstance(g, Not): go(g.sub, anc)
        elif isinstance(g, (And, Or, Implies, Iff)): go(g.l, anc); go(g.r, anc)
    go(f, frozenset())
    return counts, above, kinds

def _insert_exists_inside(f, binder_var, ex_var):
    if isinstance(f, Forall) and f.var == binder_var:
        return Forall(f.var, Exists(ex_var, f.body))
    if isinstance(f, (Forall, Exists)):
        return type(f)(f.var, _insert_exists_inside(f.body, binder_var, ex_var))
    if isinstance(f, Not):
        return Not(_insert_exists_inside(f.sub, binder_var, ex_var))
    if isinstance(f, (And, Or, Implies, Iff)):
        return type(f)(_insert_exists_inside(f.l, binder_var, ex_var),
                       _insert_exists_inside(f.r, binder_var, ex_var))
    return f

def check_generic_skolemize(step, parents, seen_symbols, deadline):
    """Check an annotation-free skolemization: replace each fresh symbol's
    term sk(X1..Xn) by a new variable bound existentially just inside its
    innermost argument binder. The step formula is a correct skolemization
    of that reconstruction by construction, so the step is sound iff the
    premise entails the reconstruction."""
    if len(parents) != 1:
        return UNSURE, "expected exactly one parent"
    F = step.formula
    new_syms = sorted(func_symbols(F) - seen_symbols)

    for i, sk in enumerate(new_syms):
        occs = _sk_occurrences(F, sk)
        if not occs:
            continue
        args = occs[0]
        if any(o != args for o in occs):
            return UNSURE, f"skolem {sk} used with varying arguments"
        if not all(isinstance(a, Var) for a in args):
            return UNSURE, f"skolem {sk} applied to non-variable arguments"
        names = [a.name for a in args]
        if len(set(names)) != len(names):
            return UNSURE, f"skolem {sk} repeats an argument"
        counts, above, kinds = _binder_info(F)
        for n in names:
            if counts.get(n, 0) != 1:
                return UNSURE, f"argument {n} of skolem {sk} is not uniquely bound"
            if kinds[n] is not Forall:
                return UNSURE, f"argument {n} of skolem {sk} is not universal"
        v = f"_sk{i}"
        F = _replace_skterm(F, sk, args, v)
        if names:
            innermost = next((n for n in names
                              if set(names) - {n} <= above[n]), None)
            if innermost is None:
                return UNSURE, f"argument binders of skolem {sk} are not nested"
            F = _insert_exists_inside(F, innermost, v)
        else:
            F = Exists(v, F)

    if free_vars(F) != free_vars(step.formula):
        return UNSURE, "skolem occurrence escapes its quantifier scope"

    v, why = ATP.entails(parents, F, deadline)
    return v, {GOOD: "premise entails the de-skolemized formula",
               BAD: "premise does NOT entail the de-skolemized formula",
               UNSURE: "ATP could not confirm the de-skolemized formula"}[v]


def check_definition(step, seen_preds):
    """introduced(definition) must be a conservative extension:
    forall vars (newpred(vars) <=> body), newpred fresh, body over those vars."""
    core = strip_closure(step.formula)
    if not isinstance(core, Iff):
        return UNSURE, "introduced definition is not an equivalence"
    for lhs, body in ((core.l, core.r), (core.r, core.l)):
        if not isinstance(lhs, Atom):
            continue
        args = lhs.args
        if not all(isinstance(a, Var) for a in args):
            continue
        if len({a.name for a in args}) != len(args):
            return BAD, "defined atom repeats a variable"
        if lhs.pred in seen_preds:
            return BAD, f"defined predicate {lhs.pred} is not fresh"
        if lhs.pred in pred_symbols(body):
            return BAD, f"definition of {lhs.pred} is circular"
        if not free_vars(body) <= {a.name for a in args}:
            return BAD, "definition body uses variables not in the defined atom"
        return GOOD, f"conservative definition of {lhs.pred}"
    return UNSURE, "introduced definition has unexpected shape"


def check_proof(problem_steps, proof_steps, deadline=None, log_to=None):
    """Return (verdict, reason, log) with verdict VerifiedGood/VerifiedBad/Unknown."""
    deadline = deadline or Deadline()
    problem_by_name = {s.name: s for s in problem_steps}
    by_name = {}
    seen_symbols = set()
    seen_preds = set()
    for s in problem_steps:
        seen_symbols |= func_symbols(s.formula)
        seen_preds |= pred_symbols(s.formula)

    log = []
    first_bad = first_unsure = None
    has_false = False
    clausified = {}

    def record(step, kind, verdict, why):
        nonlocal first_bad, first_unsure
        log.append((step.name, kind, verdict, why))
        if log_to is not None:
            tag = {GOOD: "ok  ", BAD: "BAD ", UNSURE: "????"}[verdict]
            print(f"   [{tag}] {step.name:18s} {kind or '-':18s} {why}", file=log_to)
        if verdict == BAD and first_bad is None:
            first_bad = (step.name, why)
        if verdict == UNSURE and first_unsure is None:
            first_unsure = (step.name, why)

    if not proof_steps:
        return "VerifiedBad", "proof contains no formulae", log

    for s in proof_steps:
        deadline.check()
        if s.name in by_name:
            record(s, "structure", BAD, "duplicate step name")
            by_name[s.name] = s
            continue

        if s.source_kind == 'inference':
            missing = [p for p in s.premises
                       if p not in by_name and p not in problem_by_name]
            if s.opaque_premises:
                record(s, s.rule, UNSURE, "premise list not understood")
            elif missing:
                record(s, s.rule, BAD,
                       f"premise(s) {missing} not defined before this step")
            else:
                parents = [by_name.get(p) or problem_by_name[p]
                           for p in s.premises]
                used_conj = [p.name for p in parents if p.role == 'conjecture']
                statuses = s.statuses or frozenset({s.status})
                if any(p.role == 'conjecture' and p.source_kind in
                       ('inference', 'introduced') for p in parents):
                    # only the conjecture imported from the problem may be negated
                    record(s, s.rule, UNSURE,
                           "a parent has role conjecture but is a derived step")
                elif s.rule == 'negated_conjecture' or (
                        used_conj and (statuses & {'cth', 'esa'}
                                       or statuses <= {None})):
                    # must be the negation of the conjecture, or a skolemized
                    # form of it for esa/unlabelled chains
                    v, why = check_negated_conjecture(s, parents, deadline)
                    if v != GOOD and len(parents) == 1 and (
                            'esa' in statuses or statuses <= {None}):
                        target = negate(universal_closure(parents[0].formula))
                        v2, why2 = check_generic_skolemize(
                            s, [Step(parents[0].name, 'plain', target)],
                            seen_symbols, deadline)
                        if v2 == GOOD:
                            v, why = GOOD, ("skolemized negation of the "
                                            f"conjecture: {why2}")
                        elif v == BAD:
                            v, why = UNSURE, (f"{why} (nor confirmed as a "
                                              "skolemized negation)")
                    record(s, s.rule, v, why)
                elif used_conj:
                    record(s, s.rule, BAD,
                           f"conjecture {used_conj[0]} used as a premise "
                           "(only a negation of the conjecture may consume it)")
                elif 'esa' in statuses or s.rule in ('skolemize', 'skolemise'):
                    v = why = None
                    if _skolem_annotation(s.annots) is not None:
                        v, why = check_skolemize(s, parents, seen_symbols,
                                                 deadline)
                    if v is None or v == UNSURE:
                        v2, why2 = check_generic_skolemize(
                            s, parents, seen_symbols, deadline)
                        if v is None or v2 != UNSURE:
                            v, why = v2, why2
                    record(s, s.rule, v, why)
                elif statuses <= {'thm'}:
                    v, why = ATP.entails(parents, s.formula, deadline)
                    record(s, s.rule, v, why)
                elif statuses <= {None}:
                    # no status given (e.g. Vampire): verify semantically, but
                    # a failed check is Unknown since the claimed semantics is
                    # unknown - the step may be a legal splitting/esa step
                    v, why = ATP.entails(parents, s.formula, deadline)
                    if v != GOOD and func_symbols(s.formula) - seen_symbols:
                        v2, why2 = check_generic_skolemize(
                            s, parents, seen_symbols, deadline)
                        if v2 == GOOD:
                            v, why = v2, why2
                    if v != GOOD:
                        v, why = UNSURE, ("unlabelled step could not be "
                                          "confirmed as consequence or "
                                          "skolemization")
                    record(s, s.rule, v, why)
                else:
                    record(s, s.rule, UNSURE,
                           f"rule {s.rule} with status(es) "
                           f"{sorted(x or '?' for x in statuses)} not checkable")
        elif s.source_kind == 'introduced':
            if s.rule == 'definition':
                v, why = check_definition(s, seen_preds)
                record(s, "definition", v, why)
            else:
                record(s, "introduced", UNSURE,
                       f"introduced({s.rule}) not checkable")
        else:
            def backs(p):
                return ((s.role == 'conjecture') == (p.role == 'conjecture')
                        and same_formula(p.formula, s.formula))
            ref = s.file_ref or s.name
            origin = None
            if s.source_kind == 'copy':
                prev = by_name.get(ref)
                if prev is not None and prev.role != 'conjecture' \
                        and same_formula(prev.formula, s.formula):
                    origin = prev
            if origin is None:
                origin = problem_by_name.get(ref)
                if origin is None or not backs(origin):
                    origin = next((p for p in problem_steps if backs(p)), None)
            if origin is not None:
                record(s, "input", GOOD, f"matches formula {origin.name!r}")
            else:
                # not a verbatim copy; some systems emit pre-clausified inputs
                # as file() leaves. Clauses of one source formula share skolem
                # symbols, so conjoin the open bodies of the skolem-connected
                # clauses under a single closure (universals merge: forall X p
                # & forall X q = forall X (p & q)) and check the result as a
                # skolemized consequence of the named formula.
                named = problem_by_name.get(ref) if s.file_ref else None
                fresh = func_symbols(s.formula) - seen_symbols
                if named is not None and s.role != 'conjecture' \
                        and (named.role == 'conjecture') \
                        == (s.role == 'negated_conjecture'):
                    target = negate(universal_closure(named.formula)) \
                        if named.role == 'conjecture' else named.formula
                    prior = clausified.get(ref, [])
                    all_prior_syms = set().union(set(), *[ps for _, ps in prior])
                    body = strip_closure(s.formula)
                    inc_syms = set(func_symbols(body))
                    included, changed = [], True
                    while changed:
                        changed = False
                        for pb, ps in prior:
                            if id(pb) not in included and ps & inc_syms:
                                body = And(body, pb)
                                inc_syms |= ps | func_symbols(pb)
                                included.append(id(pb))
                                changed = True
                    probe = Step(s.name, s.role, universal_closure(body))
                    v, why = check_generic_skolemize(
                        probe, [Step(named.name, 'plain', target)],
                        seen_symbols - all_prior_syms, deadline)
                    if v == BAD and included:
                        # multi-clause reconstruction is heuristic; a failed
                        # joint check does not prove the leaf is flawed
                        v, why = UNSURE, f"joint clausification unconfirmed: {why}"
                    record(s, "input", v,
                           f"as clausified form of {named.name!r}: {why}")
                    if v == GOOD:
                        own = func_symbols(s.formula) - (seen_symbols
                                                         - all_prior_syms)
                        clausified[ref] = prior + [(strip_closure(s.formula),
                                                    own)]
                elif fresh:
                    record(s, "input", UNSURE,
                           f"input {s.name} not found in the problem "
                           "(unrecognised clausified form?)")
                else:
                    record(s, "input", BAD,
                           f"input {s.name} ({s.role}) does not occur "
                           "in the problem")

        if s.formula == Atom('$false'):
            has_false = True
        seen_symbols |= func_symbols(s.formula)
        seen_preds |= pred_symbols(s.formula)
        by_name[s.name] = s
        if first_bad:
            break

    if first_bad:
        return "VerifiedBad", f"step {first_bad[0]}: {first_bad[1]}", log
    if not has_false:
        return "VerifiedBad", "refutation never derives $false", log
    if first_unsure:
        return "Unknown", f"step {first_unsure[0]}: {first_unsure[1]}", log
    return "VerifiedGood", "all steps verified", log


# ---------------------------------------------------------------------------
# Strict profile: the ProoVer 2026 certificate specification
#
# Every annotation of a step is treated as a claim to be checked, not as a
# hint that helps the checker. A step is accepted only when every obligation
# listed for its form in SPEC has passed, in that order. There are no
# fallbacks: a step that fails an obligation, or cannot discharge it, is
# never retried with a different check. Checks that go beyond what the
# specification prescribes (entailment, de-Skolemization) are used here only
# to refute a step, never to accept one.
# ---------------------------------------------------------------------------

SPEC = {
    'leaf': ('L1', 'L2', 'L3', 'L4', 'L5', 'L6'),
    'negated_conjecture': ('D1', 'D2', 'N1', 'N2', 'N3', 'N4'),
    'skolemize': ('D1', 'D2', 'S1', 'S2', 'S3', 'S4', 'S5', 'S6'),
    'inference': ('D1', 'D2', 'I1', 'I2'),
}

OBLIGATIONS = {
    'G1': "step names are unique",
    'G2': "the step is imported with a file directive or derived by an inference",
    'G3': "the formula has no free variables",
    'L1': "an imported step has role axiom or conjecture",
    'L2': "the file directive names a formula",
    'L3': "the file directive names the problem being checked",
    'L4': "the named formula exists in the problem",
    'L5': "the step and the named formula are both axioms or both the conjecture",
    'L6': "the step's formula is alpha-equivalent to the named formula",
    'D1': "a derived step does not have role axiom or conjecture",
    'D2': "every parent is a step of the proof, and no step depends on itself",
    'N1': "a negated_conjecture step claims status cth",
    'N2': "its only parent is the imported conjecture",
    'N3': "its formula is the negation of the conjecture",
    'N4': "it claims no other status",
    'S1': "a skolemize step claims status esa",
    'S2': "it has exactly one parent, which is not the conjecture",
    'S3': "it declares its Skolem symbol with new_symbols(skolem,[sK])",
    'S4': "it names the eliminated variable and its term with skolemize(Var,Term)",
    'S5': "its Skolem symbol is fresh, and its formula is the Skolemization of the parent that the annotations describe",
    'S6': "it claims no other status",
    'I1': "the conjecture is not among the parents",
    'I2': "it claims status thm and nothing else, and its parents entail it",
}


@dataclass(frozen=True)
class Source:
    kind: str               # 'none' | 'file' | 'inference' | 'other'
    path: str = None        # file: the file the directive names
    name: str = None        # file: the formula the directive names
    rule: str = None        # inference: the rule name
    info: tuple = ()        # inference: every item of the info list
    parents: tuple = ()     # inference: the parent names

def _call(text):
    """Read 'head(a, b, ...)' as (head, [a, b, ...]). None if the text is not
    exactly one such term."""
    text = text.strip()
    m = re.match(r"[A-Za-z_$][\w$]*\s*\(", text)
    if not m or not text.endswith(")"):
        return None
    depth, quoted = 0, False
    for i, c in enumerate(text):
        if quoted:
            quoted = c != "'"
        elif c == "'":
            quoted = True
        elif c in "([":
            depth += 1
        elif c in ")]":
            depth -= 1
            if depth == 0 and i != len(text) - 1:
                return None
    if depth != 0 or quoted:
        return None
    return text[:m.end() - 1].strip(), [a.strip() for a in split_top(text[m.end():-1])]

def _items(text):
    """Read '[a, b, ...]' as [a, b, ...]. None if the text is not a list."""
    text = text.strip()
    if not (text.startswith("[") and text.endswith("]")):
        return None
    return [a.strip() for a in split_top(text[1:-1])]

def parse_source(text):
    """Read the whole source field. Anything that is not a file directive or
    a flat inference record over named parents is reported as 'other'."""
    if not text.strip():
        return Source('none')
    c = _call(text)
    if c is not None:
        head, args = c
        if head == 'file' and len(args) in (1, 2) and all(args):
            return Source('file', path=args[0],
                          name=args[1] if len(args) == 2 else None)
        if head == 'inference' and len(args) == 3:
            info, parents = _items(args[1]), _items(args[2])
            if (_NAME.match(args[0]) and info is not None and parents is not None
                    and all(_NAME.match(p) for p in parents)):
                return Source('inference', rule=args[0], info=tuple(info),
                              parents=tuple(parents))
    return Source('other')

def canon_name(name):
    """In TPTP, 'a1' and a1 are the same name."""
    name = name.strip()
    m = re.fullmatch(r"'([a-z][A-Za-z0-9_]*)'", name)
    return m.group(1) if m else name

def claimed_statuses(info):
    """Every status an inference record claims, in order, without repeats.
    A status item that cannot be read is reported as '?'."""
    out = []
    for item in info:
        if not re.match(r"status\b", item):
            continue
        c = _call(item)
        ok = c is not None and len(c[1]) == 1 and re.fullmatch(r"\w+", c[1][0])
        st = c[1][0] if ok else '?'
        if st not in out:
            out.append(st)
    return out

def skolem_annotations(info):
    """The new_symbols(skolem,[...]) and skolemize(Var,Term) items of an info
    list, as (symbol lists, (var, term) pairs, all readable?)."""
    decls, binds, readable = [], [], True
    for item in info:
        if re.match(r"new_symbols\b", item):
            c = _call(item)
            syms = _items(c[1][1]) if c is not None and len(c[1]) == 2 else None
            if syms is None or not all(_NAME.match(x) for x in syms):
                readable = False
            elif c[1][0] == 'skolem':
                decls.append(syms)
        elif re.match(r"skolemize\b", item):
            c = _call(item)
            if (c is not None and len(c[1]) == 2
                    and re.fullmatch(r"[A-Z_]\w*", c[1][0])):
                binds.append((c[1][0], c[1][1]))
            else:
                readable = False
    return decls, binds, readable


class Evidence:
    """What has been established about one step. The step counts as verified
    only when `passed` is exactly the list SPEC gives for its form."""
    def __init__(self, form):
        self.form, self.passed = form, []
        self.verdict, self.failed, self.why = None, None, ""
    def ok(self, oid):
        self.passed.append(oid)
    def bad(self, oid, why):
        self.verdict, self.failed, self.why = BAD, oid, why
        return self
    def unsure(self, oid, why):
        self.verdict, self.failed, self.why = UNSURE, oid, why
        return self
    def good(self, why):
        self.verdict, self.why = GOOD, why
        return self
    def complete(self):
        return self.verdict == GOOD and tuple(self.passed) == SPEC.get(self.form)


class _Strict:
    """State shared by the strict checks of one proof."""
    def __init__(self, problem_steps, deadline, problem_file):
        self.deadline, self.problem_file = deadline, problem_file
        self.problem, self.ambiguous = {}, set()
        self.problem_symbols = set()
        for p in problem_steps:
            n = canon_name(p.name)
            if n in self.problem:
                self.ambiguous.add(n)
            self.problem[n] = p
            self.problem_symbols |= func_symbols(p.formula)
        self.steps = {}

    def graph(self, proof_steps, sources):
        """Index the derivation. Ancestors are kept as bit sets over step
        positions."""
        self.proof, self.index = proof_steps, {}
        for i, s in enumerate(proof_steps):
            self.index.setdefault(canon_name(s.name), i)
        self.parents = [[self.index.get(canon_name(q)) for q in src.parents]
                        if src.kind == 'inference' else [] for src in sources]
        self.declares = [set().union(*skolem_annotations(src.info)[0])
                         if src.kind == 'inference' and src.rule == 'skolemize' else set()
                         for src in sources]
        self.esa = [src.kind == 'inference' and (src.rule == 'skolemize' or
                    'esa' in claimed_statuses(src.info)) for src in sources]
        self.occurs = {}
        for i, s in enumerate(proof_steps):
            for f in func_symbols(s.formula):
                self.occurs.setdefault(f, []).append(i)

    def order(self):
        """Topological order, keeping file order where the derivation allows.
        Returns (order, None), or (None, cycle) if some step depends on itself."""
        import heapq
        n = len(self.proof)
        children, waiting = [[] for _ in range(n)], [0] * n
        for i, ps in enumerate(self.parents):
            for q in set(ps):
                children[q].append(i); waiting[i] += 1
        ready = [i for i in range(n) if waiting[i] == 0]
        heapq.heapify(ready)
        order = []
        while ready:
            i = heapq.heappop(ready); order.append(i)
            for c in children[i]:
                waiting[c] -= 1
                if waiting[c] == 0:
                    heapq.heappush(ready, c)
        if len(order) == n:
            self.ancestors = [0] * n
            for i in order:
                a = 0
                for q in set(self.parents[i]):
                    a |= self.ancestors[q] | (1 << q)
                self.ancestors[i] = a
            return order, None
        # every step left over has a parent that is also left over
        left = set(range(n)) - set(order)
        path, i = [], min(left)
        while i not in path:
            path.append(i)
            i = min(q for q in self.parents[i] if q in left)
        return None, path[path.index(i):]

    def depends(self, i, j):
        """Does step i depend, directly or not, on step j?"""
        return (self.ancestors[i] >> j) & 1 == 1

    def symbols_before(self, i):
        """The problem's symbols and those of every step that step i depends on."""
        out, a, j = set(self.problem_symbols), self.ancestors[i], 0
        while a:
            if a & 1:
                out |= func_symbols(self.proof[j].formula)
            a >>= 1; j += 1
        return out

    def fresh(self, i, sym):
        """May step i introduce `sym` as a Skolem symbol?

        Not if the problem, or any step that step i depends on, mentions it,
        and not if another step also introduces it. Steps that depend on step
        i may mention it freely. So may any other step that only claims to be
        a logical consequence of its parents (status thm or cth): such a step
        is true whatever `sym` stands for, provided its parents are. The one
        case left is another step that only preserves satisfiability (status
        esa) and mentions `sym`: its own witness could depend on what `sym`
        stands for, so freshness cannot be decided."""
        name = lambda j: self.proof[j].name
        if sym in self.problem_symbols:
            return BAD, f"Skolem symbol {sym} is not fresh: it occurs in the problem"
        pending = None
        for j in self.occurs.get(sym, []):
            if j == i or self.depends(j, i):
                continue
            if self.depends(i, j):
                return BAD, (f"Skolem symbol {sym} is not fresh: it occurs in "
                             f"{name(j)}, which this step depends on")
            if sym in self.declares[j]:
                return BAD, (f"Skolem symbol {sym} is not fresh: step {name(j)} "
                             "also introduces it")
            if self.esa[j] and pending is None:
                pending = (f"Skolem symbol {sym} also occurs in {name(j)}, another "
                           "step with status esa; cannot check freshness")
        return (UNSURE, pending) if pending else (GOOD, "")

def _got(claims):
    return ", ".join(claims) if claims else "no status"

def _strict_leaf(s, src, cx):
    ev = Evidence('leaf')
    if s.role not in ('axiom', 'conjecture'):
        return ev.bad('L1', f"imported with a file directive but has role {s.role}")
    ev.ok('L1')
    if src.name is None:
        return ev.bad('L2', "file directive does not name a formula of the problem")
    ev.ok('L2')
    if cx.problem_file is not None and \
            os.path.basename(src.path.strip("'")) != cx.problem_file:
        return ev.unsure('L3', f"file directive names {src.path}, "
                               "which is not the problem being checked")
    ev.ok('L3')
    ref = canon_name(src.name)
    if ref in cx.ambiguous:
        return ev.unsure('L4', f"the problem has several formulas named {ref}")
    origin = cx.problem.get(ref)
    if origin is None:
        return ev.bad('L4', f"file directive names {ref}, which is not in the problem")
    ev.ok('L4')
    if origin.role not in ('axiom', 'conjecture'):
        return ev.unsure('L5', f"{ref} has role {origin.role} in the problem; only "
                               "axioms and the conjecture can be imported")
    if origin.role != s.role:
        return ev.bad('L5', f"has role {s.role}, but {ref} has role "
                            f"{origin.role} in the problem")
    ev.ok('L5')
    if not equal_mod_alpha(s.formula, origin.formula):
        return ev.bad('L6', f"formula differs from {ref} in the problem")
    ev.ok('L6')
    return ev.good(f"imports {ref}")

def _strict_parents(ev, s, src, cx):
    """The obligations every derived step shares. Returns the parent steps,
    or None once `ev` holds a verdict."""
    if s.role in ('axiom', 'conjecture'):
        ev.bad('D1', f"has role {s.role} but is derived by {src.rule}; axioms "
                     "and the conjecture must be imported with a file directive")
        return None
    ev.ok('D1')
    missing = [p for p in src.parents if canon_name(p) not in cx.steps]
    if missing:
        ev.bad('D2', f"premise(s) {missing} not defined before this step")
        return None
    ev.ok('D2')
    return [cx.steps[canon_name(p)] for p in src.parents]

def _strict_claims(ev, oid, s, parents, claims, prescribed, cx, summary):
    """A step may claim only the status its form prescribes. Any other
    status keeps the step from being accepted, and is a flaw if it can be
    refuted."""
    extra = [st for st in claims if st != prescribed]
    if 'thm' in extra:
        v, why = ATP.entails(parents, s.formula, cx.deadline)
        if v == BAD:
            return ev.bad(oid, f"also claims status thm, but {why}")
    if extra:
        return ev.unsure(oid, f"also claims status {extra[0]}; a {ev.form} "
                              f"step may only claim {prescribed}")
    ev.ok(oid)
    return ev.good(summary)

def _strict_negated_conjecture(s, src, cx):
    ev = Evidence('negated_conjecture')
    parents = _strict_parents(ev, s, src, cx)
    if parents is None:
        return ev
    claims = claimed_statuses(src.info)
    if 'cth' not in claims:
        return ev.bad('N1', f"negated_conjecture must have status cth, got {_got(claims)}")
    ev.ok('N1')
    if len(parents) != 1:
        return ev.bad('N2', "negated_conjecture must have exactly one parent")
    parent = parents[0]
    if parent.role != 'conjecture':
        return ev.bad('N2', f"negated_conjecture parent {parent.name} is not the conjecture")
    ev.ok('N2')
    r = ATP.decide(Iff(universal_closure(s.formula),
                       negate(universal_closure(parent.formula))), cx.deadline)
    if r == "CounterSatisfiable":
        return ev.bad('N3', "formula is NOT the negation of the conjecture")
    if r != "Theorem":
        return ev.unsure('N3', "prover could not decide negation equivalence")
    ev.ok('N3')
    return _strict_claims(ev, 'N4', s, parents, claims, 'cth', cx,
                          "formula is the correct negation of the conjecture")

def _strict_skolemize(s, src, cx):
    ev = Evidence('skolemize')
    parents = _strict_parents(ev, s, src, cx)
    if parents is None:
        return ev
    claims = claimed_statuses(src.info)
    if 'esa' not in claims:
        return ev.bad('S1', f"skolemize must have status esa, got {_got(claims)}")
    ev.ok('S1')
    if len(parents) != 1:
        return ev.bad('S2', "skolemize must have exactly one parent")
    parent = parents[0]
    if parent.role == 'conjecture':
        return ev.bad('S2', f"conjecture {parent.name} used as a premise "
                            "(only a negated_conjecture step may consume it)")
    ev.ok('S2')
    decls, binds, readable = skolem_annotations(src.info)
    if not readable:
        return ev.unsure('S3', "skolemize annotations not understood")
    if not decls:
        return ev.bad('S3', "skolemize step has no new_symbols(skolem,[...]) annotation")
    if len(decls) != 1 or len(decls[0]) != 1:
        return ev.unsure('S3', "multi-symbol skolemization not supported")
    ev.ok('S3')
    if not binds:
        return ev.bad('S4', "skolemize step has no skolemize(Var,Term) annotation")
    if len(binds) != 1:
        return ev.unsure('S4', "more than one skolemize(Var,Term) annotation")
    ev.ok('S4')
    v, why = cx.fresh(cx.current, decls[0][0])
    if v == GOOD:
        v, why = skolemization(parent.formula, s.formula, decls[0][0],
                               binds[0][0], binds[0][1], (), strict=True)
    if v == BAD:
        return ev.bad('S5', why)
    if v == UNSURE:
        # this shape is not covered: the step cannot be accepted, but it may
        # still be refuted, semantically or through another status it claims
        v2, why2 = check_generic_skolemize(s, parents, cx.symbols_before(cx.current),
                                           cx.deadline)
        if v2 == BAD:
            return ev.bad('S5', why2)
        probe = _strict_claims(Evidence('skolemize'), 'S6', s, parents, claims,
                               'esa', cx, "")
        if probe.verdict == BAD:
            return ev.bad('S6', probe.why)
        return ev.unsure('S5', why)
    ev.ok('S5')
    return _strict_claims(ev, 'S6', s, parents, claims, 'esa', cx, why)

def _strict_inference(s, src, cx):
    ev = Evidence('inference')
    parents = _strict_parents(ev, s, src, cx)
    if parents is None:
        return ev
    conj = [p.name for p in parents if p.role == 'conjecture']
    if conj:
        return ev.bad('I1', f"conjecture {conj[0]} used as a premise "
                            "(only a negated_conjecture step may consume it)")
    ev.ok('I1')
    claims = claimed_statuses(src.info)
    if not claims:
        return ev.unsure('I2', f"rule {src.rule} has no status, so the "
                               "specification gives no way to check it")
    pending = None
    for st in claims:
        if st == 'thm':
            v, why = ATP.entails(parents, s.formula, cx.deadline)
        elif st == 'esa':
            # only skolemize steps may be esa: read as a Skolemization, this
            # step can be refuted, but it can never be accepted
            v, why = check_generic_skolemize(s, parents, cx.symbols_before(cx.current),
                                             cx.deadline)
            if v != BAD:
                v, why = UNSURE, (f"status esa can only be checked on skolemize "
                                  f"steps, not on rule {src.rule}")
        else:
            v, why = UNSURE, f"status {st} on rule {src.rule} cannot be checked"
        if v == BAD:
            return ev.bad('I2', why)
        if v == UNSURE and pending is None:
            pending = why
    if pending is not None:
        return ev.unsure('I2', pending)
    ev.ok('I2')
    return ev.good("ATP confirms premises entail the step")

_STRICT_RULES = {'negated_conjecture': _strict_negated_conjecture,
                 'skolemize': _strict_skolemize}

def check_proof_strict(problem_steps, proof_steps, deadline=None, log_to=None,
                       problem_file=None):
    """Return (verdict, reason, log) under the strict profile. `log` holds
    one (step name, Evidence) pair per step that was checked."""
    deadline = deadline or Deadline()
    cx = _Strict(problem_steps, deadline, problem_file)
    log = []
    first_bad = first_unsure = None
    has_false = False

    if not proof_steps:
        return "VerifiedBad", "proof contains no formulae", log
    if sum(p.role == 'conjecture' for p in problem_steps) > 1:
        return "Unknown", "the problem has more than one conjecture", log
    is_open = open_formula(problem_steps)
    if is_open:
        return "Unknown", f"problem formula {is_open} has free variables", log

    sources = [parse_source(s.source) for s in proof_steps]
    seen = set()
    for s in proof_steps:
        if canon_name(s.name) in seen:
            return "VerifiedBad", f"step {s.name}: duplicate step name", log
        seen.add(canon_name(s.name))
    cx.graph(proof_steps, sources)
    for s, ps, src in zip(proof_steps, cx.parents, sources):
        missing = [q for q, i in zip(src.parents, ps) if i is None]
        if missing:
            return "VerifiedBad", (f"step {s.name}: premise(s) {missing} are not "
                                   "steps of the proof"), log
    order, cycle = cx.order()
    if cycle:
        names = " -> ".join(proof_steps[i].name for i in cycle + cycle[:1])
        return "VerifiedBad", f"step {proof_steps[cycle[0]].name}: the derivation is cyclic ({names})", log

    # Steps are checked in an order where every parent comes first: the rules
    # put no restriction on the order in which a proof lists its steps.
    for i in order:
        deadline.check()
        s, src, cx.current = proof_steps[i], sources[i], i
        name = canon_name(s.name)
        if src.kind == 'none':
            ev = Evidence('structure').bad(
                'G2', "has no source: a step must be imported with a file "
                      "directive or derived by an inference")
        elif src.kind == 'file':
            ev = _strict_leaf(s, src, cx)
        elif src.kind == 'inference':
            ev = _STRICT_RULES.get(src.rule, _strict_inference)(s, src, cx)
        else:
            ev = Evidence('structure').unsure(
                'G2', "source is neither a file directive nor a flat inference record")
        if ev.verdict == GOOD and free_vars(s.formula):
            # free variables are read as universally quantified by the ATP but
            # are invisible to the Skolemization check, so they are not accepted
            ev = Evidence(ev.form).unsure(
                'G3', "formula has free variables, which a fof formula may not have")

        log.append((s.name, ev))
        if log_to is not None:
            tag = {GOOD: "ok  ", BAD: "BAD ", UNSURE: "????"}[ev.verdict]
            where = f"{ev.failed}: " if ev.failed else ""
            print(f"   [{tag}] {s.name:18s} {ev.form:18s} {where}{ev.why}", file=log_to)
        if ev.verdict == BAD and first_bad is None:
            first_bad = (s.name, ev.why)
        if ev.verdict == UNSURE and first_unsure is None:
            first_unsure = (s.name, ev.why)

        if s.formula == Atom('$false'):
            has_false = True
        cx.steps[name] = s
        if first_bad:
            break

    if first_bad:
        return "VerifiedBad", f"step {first_bad[0]}: {first_bad[1]}", log
    if not has_false:
        return "VerifiedBad", "refutation never derives $false", log
    if first_unsure:
        return "Unknown", f"step {first_unsure[0]}: {first_unsure[1]}", log
    # A proof is only accepted on complete evidence: every step must have
    # passed exactly the obligations SPEC lists for its form.
    for name, ev in log:
        if not ev.complete():
            return "Unknown", f"step {name}: evidence is incomplete", log
    return "VerifiedGood", "all steps verified", log


def open_formula(steps):
    """The name of the first step whose formula has free variables, if any."""
    for s in steps:
        if free_vars(s.formula):
            return s.name
    return None

def unparsed(text, spans):
    """What is left of a file once its comments and the fof/cnf formulas at
    `spans` are removed."""
    rest, last = [], 0
    for a, b in spans:
        rest.append(text[last:a]); last = b
    rest.append(text[last:])
    return re.sub(r"[\s.]", "", "".join(rest))

def _read(text, deadline):
    text = strip_comments(text)
    spans = []
    steps = [parse_annotated(lang, u)
             for lang, u in annotated_units(text, deadline, spans)]
    return steps, unparsed(text, spans)

PROFILES = ("strict", "tolerant")

def verify(problem_text, proof_text, deadline=None, log_to=None, problem_dir=None,
           profile="strict", problem_file=None):
    """Check a proof. `problem_file` is the name of the problem file when it
    was located from the proof itself; the strict profile then requires every
    file directive to name that file."""
    if profile not in PROFILES:
        raise ValueError(f"unknown profile {profile!r}")
    deadline = deadline or Deadline()
    try:
        problem_steps, problem_rest = _read(expand_includes(problem_text, problem_dir), deadline)
        proof_steps, proof_rest = _read(proof_text, deadline)
    except OutOfTime:
        raise
    except (SyntaxError, RecursionError) as e:
        return "Unknown", f"parse error: {e}", []
    if profile == "tolerant":
        verdict, reason, log = check_proof(problem_steps, proof_steps, deadline, log_to)
        is_open = open_formula(problem_steps) or open_formula(proof_steps)
        if verdict == "VerifiedGood" and is_open:
            return "Unknown", f"formula {is_open} has free variables", log
        return verdict, reason, log
    if problem_rest:
        return "Unknown", "the problem file has content that is not a fof or cnf formula", []
    verdict, reason, log = check_proof_strict(problem_steps, proof_steps, deadline,
                                              log_to, problem_file)
    if verdict == "VerifiedGood" and proof_rest:
        return "Unknown", "the proof file has content that is not a fof or cnf formula", log
    return verdict, reason, log
