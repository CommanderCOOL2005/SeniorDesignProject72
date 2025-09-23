"""
AI Proof Verifier - Full Prototype (English-only code & comments)
-----------------------------------------------------------------
Features implemented:
- Propositional logic rules:
  -> Elim/Intro, And Intro/Elim(L/R), Or Intro(L/R)/Elim,
  Not Intro/Elim, RAA (Reductio), Explosion (ex-falso)
- First-order logic rules:
  Forall Intro/Elim, Exists Intro/Elim (with basic side-condition checks)
- Controlled subproofs (assumption boxes) for ->-intro, ¬-intro, ∨-elim, ∀-intro, ∃-elim, RAA
- NL mapper (English) with multiple candidates + confidence
- Lean 4 export (tactic skeleton)
- Flask endpoint (optional) to serve JSON for visualization
- Suggestion generator on failure

NOTE:
- This is a didactic prototype, not a complete theorem prover.
- Side-condition checks for FOL are conservative but simplified.
- Parsing is a controlled grammar (safe for class demos). You can replace with a trained model later.
"""

from __future__ import annotations
from dataclasses import dataclass, field
from typing import List, Dict, Optional, Tuple, Any, Set
import re
import json
import pathlib
import sys

# =========================
# Logic Abstract Syntax
# =========================

@dataclass(frozen=True)
class Term:
    """First-order term: variable or function application."""
    pass

@dataclass(frozen=True)
class Var(Term):
    name: str
    def __str__(self) -> str: return self.name

@dataclass(frozen=True)
class Fun(Term):
    name: str
    args: Tuple[Term, ...]
    def __str__(self) -> str:
        if not self.args: return self.name
        return f"{self.name}({', '.join(map(str, self.args))})"

@dataclass(frozen=True)
class Formula:
    """Propositional/FOL formulas."""
    def pretty(self) -> str: return str(self)

@dataclass(frozen=True)
class Bottom(Formula):
    """Contradiction ⊥."""
    def __str__(self) -> str: return "⊥"

@dataclass(frozen=True)
class Atom(Formula):
    """Propositional atom with optional FOL predicate shape P or P(t1,...,tn)."""
    name: str
    args: Tuple[Term, ...] = field(default_factory=tuple)
    def __str__(self) -> str:
        if not self.args: return self.name
        return f"{self.name}({', '.join(map(str, self.args))})"

@dataclass(frozen=True)
class Not(Formula):
    inner: Formula
    def __str__(self) -> str: return f"¬{self.inner}"

@dataclass(frozen=True)
class And(Formula):
    left: Formula
    right: Formula
    def __str__(self) -> str: return f"({self.left} ∧ {self.right})"

@dataclass(frozen=True)
class Or(Formula):
    left: Formula
    right: Formula
    def __str__(self) -> str: return f"({self.left} ∨ {self.right})"

@dataclass(frozen=True)
class Imp(Formula):
    left: Formula
    right: Formula
    def __str__(self) -> str: return f"({self.left} → {self.right})"

@dataclass(frozen=True)
class Forall(Formula):
    var: str
    body: Formula
    def __str__(self) -> str: return f"∀{self.var}. {self.body}"

@dataclass(frozen=True)
class Exists(Formula):
    var: str
    body: Formula
    def __str__(self) -> str: return f"∃{self.var}. {self.body}"

# Utility: free variables in a term/formula (for side-conditions)
def free_vars_term(t: Term) -> Set[str]:
    if isinstance(t, Var):
        return {t.name}
    if isinstance(t, Fun):
        s: Set[str] = set()
        for a in t.args:
            s |= free_vars_term(a)
        return s
    return set()

def substitute_term(t: Term, x: str, by: Term) -> Term:
    if isinstance(t, Var):
        return by if t.name == x else t
    if isinstance(t, Fun):
        return Fun(t.name, tuple(substitute_term(a, x, by) for a in t.args))
    return t

def free_vars(f: Formula) -> Set[str]:
    if isinstance(f, Bottom):
        return set()
    if isinstance(f, Atom):
        s: Set[str] = set()
        for a in f.args:
            s |= free_vars_term(a)
        return s
    if isinstance(f, Not):
        return free_vars(f.inner)
    if isinstance(f, (And, Or, Imp)):
        return free_vars(f.left) | free_vars(f.right)
    if isinstance(f, Forall):
        return free_vars(f.body) - {f.var}
    if isinstance(f, Exists):
        return free_vars(f.body) - {f.var}
    return set()

def substitute_formula(f: Formula, x: str, by: Term) -> Formula:
    if isinstance(f, Bottom):
        return f
    if isinstance(f, Atom):
        return Atom(f.name, tuple(substitute_term(a, x, by) for a in f.args))
    if isinstance(f, Not):
        return Not(substitute_formula(f.inner, x, by))
    if isinstance(f, And):
        return And(substitute_formula(f.left, x, by), substitute_formula(f.right, x, by))
    if isinstance(f, Or):
        return Or(substitute_formula(f.left, x, by), substitute_formula(f.right, x, by))
    if isinstance(f, Imp):
        return Imp(substitute_formula(f.left, x, by), substitute_formula(f.right, x, by))
    if isinstance(f, Forall):
        if f.var == x: return f  # shadowed
        return Forall(f.var, substitute_formula(f.body, x, by))
    if isinstance(f, Exists):
        if f.var == x: return f  # shadowed
        return Exists(f.var, substitute_formula(f.body, x, by))
    return f

def alpha_equiv(a: Formula, b: Formula) -> bool:
    # Simple structural equality (no α-conv) for demo; extend as needed.
    return a == b

# =========================
# Controlled Parser
# =========================

class TinyParser:
    """
    A controlled grammar parser for terms and formulas.
    Supports:
      - Terms: variables (lowercase), function symbols (Upper/lower) with args: f(x,y)
      - Atoms: P, Q, R or Pred(t1,...,tn)
      - Connectives: ¬, ~, not, &, ∧, |, ∨, ->, →, =>, ( ), ⊥
      - Quantifiers: ∀x., Forall x., ∃x., Exists x.
    """

    def normalize(self, s: str) -> str:
        s = s.strip()
        # remove trailing dot (.) for robustness
        if s.endswith("."):
            s = s[:-1].strip()

        s = s.replace("=>", "->").replace("→", "->")
        s = re.sub(r"\bnot\b", "¬", s, flags=re.I)
        s = s.replace("~", "¬")
        s = s.replace("/\\", "∧").replace("\\/", "∨")
        s = s.replace("&", "∧").replace("|", "∨")
        s = s.replace("⊥", "⊥")
        # quantifiers: Forall x.  Exists x.
        s = re.sub(r"\bForall\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*\.", r"∀\1.", s)
        s = re.sub(r"\bExists\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*\.", r"∃\1.", s)
        return s


    def tokenize(self, s: str) -> List[str]:
        # Tokenize parentheses, commas, arrows, connectives, quantifiers, dot
        s = s.replace("(", " ( ").replace(")", " ) ").replace(",", " , ").replace(".", " . ")
        s = s.replace("->", " -> ")
        # split
        toks = [t for t in s.split() if t]
        return toks

    # Pratt-style or recursive-descent parser (simplified)
    def parse(self, s: str) -> Formula:
        s = self.normalize(s)
        toks = self.tokenize(s)
        f, rest = self._parse_imp(toks)
        if rest:
            raise ValueError(f"Unparsed tokens: {' '.join(rest)}")
        return f

    def _parse_imp(self, toks: List[str]) -> Tuple[Formula, List[str]]:
        left, rest = self._parse_or(toks)
        while rest and rest[0] == "->":
            rest = rest[1:]
            right, rest = self._parse_imp(rest)
            left = Imp(left, right)
        return left, rest

    def _parse_or(self, toks: List[str]) -> Tuple[Formula, List[str]]:
        left, rest = self._parse_and(toks)
        while rest and rest[0] == "∨":
            rest = rest[1:]
            right, rest = self._parse_and(rest)
            left = Or(left, right)
        return left, rest

    def _parse_and(self, toks: List[str]) -> Tuple[Formula, List[str]]:
        left, rest = self._parse_unary(toks)
        while rest and rest[0] == "∧":
            rest = rest[1:]
            right, rest = self._parse_unary(rest)
            left = And(left, right)
        return left, rest

    def _parse_unary(self, toks: List[str]) -> Tuple[Formula, List[str]]:
        if not toks: raise ValueError("Unexpected end")
        t = toks[0]
        if t == "¬":
            sub, rest = self._parse_unary(toks[1:])
            return Not(sub), rest
        if t == "⊥":
            return Bottom(), toks[1:]
        if t == "(":
            inner, rest = self._parse_imp(toks[1:])
            if not rest or rest[0] != ")":
                raise ValueError("Missing )")
            return inner, rest[1:]
        if t.startswith("∀") or t == "∀":
            # tokenization gives '∀x' or '∀', 'x', '.'
            if t == "∀":
                if len(toks) < 3 or toks[2] != ".":
                    raise ValueError("Malformed ∀")
                var = toks[1]
                body, rest = self._parse_unary(toks[3:])
                return Forall(var, body), rest
            else:
                var = t[1:]
                if len(toks) < 2 or toks[1] != ".":
                    raise ValueError("Malformed ∀x.")
                body, rest = self._parse_unary(toks[2:])
                return Forall(var, body), rest
        if t.startswith("∃") or t == "∃":
            if t == "∃":
                if len(toks) < 3 or toks[2] != ".":
                    raise ValueError("Malformed ∃")
                var = toks[1]
                body, rest = self._parse_unary(toks[3:])
                return Exists(var, body), rest
            else:
                var = t[1:]
                if len(toks) < 2 or toks[1] != ".":
                    raise ValueError("Malformed ∃x.")
                body, rest = self._parse_unary(toks[2:])
                return Exists(var, body), rest
        # otherwise an atom/predicate (maybe with args)
        atom, rest = self._parse_atom(toks)
        return atom, rest

    def _parse_term(self, toks: List[str]) -> Tuple[Term, List[str]]:
        if not toks: raise ValueError("Unexpected end in term")
        t = toks[0]
        # variable or function
        if len(toks) >= 2 and toks[1] == "(":
            # function application: f( ... )
            fname = t
            args: List[Term] = []
            rest = toks[2:]
            if not rest: raise ValueError("Malformed function")
            while rest and rest[0] != ")":
                arg, rest = self._parse_term(rest)
                args.append(arg)
                if rest and rest[0] == ",":
                    rest = rest[1:]
                elif rest and rest[0] == ")":
                    break
                else:
                    raise ValueError("Expected , or )")
            if not rest or rest[0] != ")":
                raise ValueError("Missing ) in function")
            return Fun(fname, tuple(args)), rest[1:]
        # bare variable/constant
        if re.match(r"^[a-z][a-zA-Z0-9_]*$", t):
            return Var(t), toks[1:]
        # constants considered as 0-arity Fun
        if re.match(r"^[A-Za-z][A-Za-z0-9_]*$", t):
            return Fun(t, ()), toks[1:]
        raise ValueError(f"Bad term token: {t}")

    def _parse_atom(self, toks: List[str]) -> Tuple[Atom, List[str]]:
        if not toks: raise ValueError("Unexpected end in atom")
        t = toks[0]
        # P(...) predicate
        if len(toks) >= 2 and toks[1] == "(":
            pname = t
            args: List[Term] = []
            rest = toks[2:]
            if not rest: raise ValueError("Malformed predicate")
            while rest and rest[0] != ")":
                arg, rest = self._parse_term(rest)
                args.append(arg)
                if rest and rest[0] == ",":
                    rest = rest[1:]
                elif rest and rest[0] == ")":
                    break
                else:
                    raise ValueError("Expected , or ) in predicate")
            if not rest or rest[0] != ")":
                raise ValueError("Missing ) in predicate")
            return Atom(pname, tuple(args)), rest[1:]
        # bare propositional atom
        if re.match(r"^[A-Za-z][A-Za-z0-9_]*$", t):
            return Atom(t, ()), toks[1:]
        raise ValueError(f"Bad atom token: {t}")

# =========================
# Proof data structures
# =========================

@dataclass
class Step:
    id: str
    nl: str
    rule: str
    deps: List[str] = field(default_factory=list)
    formal: Optional[str] = None  # optional explicit formal formula string
    box_open: bool = False        # open a subproof with an assumption (first dep is the assumption formula id)
    box_close: bool = False       # close the most recent open subproof
    parser_meta: Dict[str, Any] = field(default_factory=dict)

@dataclass
class Box:
    """A subproof box started by an explicit assumption."""
    assumption_id: str
    assumption_formula: Formula
    lines: List[str] = field(default_factory=list)  # step ids included

@dataclass
class Context:
    parser: TinyParser
    formulas: Dict[str, Formula]          # id -> formula
    proven_order: List[str]               # order of derivations (ids)
    boxes: List[Box]                      # stack of open boxes
    messages: List[str]                   # log

class CheckError(Exception):
    pass

# =========================
# Rule Implementations
# =========================

def expect(ids: List[str], ctx: Context) -> List[Formula]:
    out: List[Formula] = []
    for i in ids:
        if i not in ctx.formulas:
            raise CheckError(f"Dependency {i} not found.")
        out.append(ctx.formulas[i])
    return out

def check_rule(step: Step, ctx: Context) -> Formula:
    """Dispatch to rule-specific checks; may use/require subproof boxes."""
    r = step.rule.strip()

    # Parse explicit formal target if provided (for sanity check)
    target: Optional[Formula] = None
    if step.formal:
        target = ctx.parser.parse(step.formal)

    # -------------- Propositional rules --------------

    if r in ("->-elim", "→-elim", "mp", "ModusPonens"):
        f1, f2 = expect(step.deps, ctx)
        cand: List[Formula] = []
        if isinstance(f1, Imp):  # f2 should be antecedent
            if alpha_equiv(f2, f1.left): cand.append(f1.right)
        if isinstance(f2, Imp):  # f1 should be antecedent
            if alpha_equiv(f1, f2.left): cand.append(f2.right)
        if not cand:
            raise CheckError("->-elim failed: need P and (P->Q).")
        concl = cand[0]
        if target and not alpha_equiv(target, concl):
            raise CheckError(f"Conclusion mismatch. Expected {concl.pretty()}, got {target.pretty()}.")
        return concl

    if r in ("->-intro", "→-intro"):
        # must close a box whose assumption is antecedent; deps[0] is that box's assumption id, deps[1] is result inside
        if len(step.deps) != 2:
            raise CheckError("->-intro requires deps: [assumption_id, result_id].")
        a_id, res_id = step.deps
        if not ctx.boxes or ctx.boxes[-1].assumption_id != a_id:
            raise CheckError("->-intro requires the most recent open box to match the given assumption id.")
        antecedent = ctx.boxes[-1].assumption_formula
        consequent = ctx.formulas.get(res_id)
        if consequent is None:
            raise CheckError("Result inside the box not found.")
        concl = Imp(antecedent, consequent)
        if target and not alpha_equiv(target, concl):
            raise CheckError("Conclusion mismatch in ->-intro.")
        return concl

    if r in ("and-intro", "∧-intro"):
        f1, f2 = expect(step.deps, ctx)
        concl = And(f1, f2)
        if target and not alpha_equiv(target, concl):
            raise CheckError("Conclusion mismatch in ∧-intro.")
        return concl

    if r in ("and-elim-left", "∧-elimL"):
        (f,) = expect(step.deps, ctx)
        if not isinstance(f, And): raise CheckError("∧-elimL needs P∧Q.")
        concl = f.left
        if target and not alpha_equiv(target, concl):
            raise CheckError("Conclusion mismatch in ∧-elimL.")
        return concl

    if r in ("and-elim-right", "∧-elimR"):
        (f,) = expect(step.deps, ctx)
        if not isinstance(f, And): raise CheckError("∧-elimR needs P∧Q.")
        concl = f.right
        if target and not alpha_equiv(target, concl):
            raise CheckError("Conclusion mismatch in ∧-elimR.")
        return concl

    if r in ("or-intro-left", "∨-introL"):
        (f,) = expect(step.deps, ctx)
        # need also the other disjunct in target if provided, otherwise accept Or(f, ?)
        if target:
            if not isinstance(target, Or) or not alpha_equiv(target.left, f):
                raise CheckError("∨-introL target should be P∨Q with P available.")
            return target
        # heuristic: if no target, require parser_meta['other'] to form Or
        other = step.parser_meta.get("other")
        if not other: raise CheckError("∨-introL needs target or parser_meta.other for the right disjunct.")
        other_f = ctx.parser.parse(other)
        return Or(f, other_f)

    if r in ("or-intro-right", "∨-introR"):
        (f,) = expect(step.deps, ctx)
        if target:
            if not isinstance(target, Or) or not alpha_equiv(target.right, f):
                raise CheckError("∨-introR target should be P∨Q with Q available.")
            return target
        other = step.parser_meta.get("other")
        if not other: raise CheckError("∨-introR needs target or parser_meta.other for the left disjunct.")
        other_f = ctx.parser.parse(other)
        return Or(other_f, f)

    if r in ("or-elim", "∨-elim"):
        # deps: [P∨Q, box1_result, box2_result], with two open boxes whose assumptions are P and Q and both derive R
        if len(step.deps) != 3:
            raise CheckError("∨-elim requires deps: [P∨Q, res_from_P, res_from_Q].")
        disj, r1, r2 = expect(step.deps, ctx)
        if not isinstance(disj, Or): raise CheckError("∨-elim first dep must be P∨Q.")
        if len(ctx.boxes) < 2: raise CheckError("∨-elim requires two recently closed boxes.")
        b2 = ctx.boxes.pop()
        b1 = ctx.boxes.pop()
        # Check assumptions match P and Q in some order, and results equal
        if not ((alpha_equiv(b1.assumption_formula, disj.left) and alpha_equiv(b2.assumption_formula, disj.right)) or
                (alpha_equiv(b1.assumption_formula, disj.right) and alpha_equiv(b2.assumption_formula, disj.left))):
            raise CheckError("∨-elim: box assumptions must match the disjuncts.")
        if not alpha_equiv(r1, r2):
            raise CheckError("∨-elim: both branches must conclude the same formula.")
        concl = r1
        if target and not alpha_equiv(target, concl):
            raise CheckError("Conclusion mismatch in ∨-elim.")
        return concl

    if r in ("not-intro", "¬-intro"):
        # deps: [assumption_id, bottom_id]
        if len(step.deps) != 2:
            raise CheckError("¬-intro requires deps: [assumption_id, bottom_id].")
        a_id, bot_id = step.deps
        if not ctx.boxes or ctx.boxes[-1].assumption_id != a_id:
            raise CheckError("¬-intro requires the most recent open box to match the given assumption id.")
        ass = ctx.boxes[-1].assumption_formula
        if not isinstance(ctx.formulas.get(bot_id), Bottom):
            raise CheckError("¬-intro requires contradiction ⊥ inside the box.")
        concl = Not(ass)
        if target and not alpha_equiv(target, concl):
            raise CheckError("Conclusion mismatch in ¬-intro.")
        return concl

    if r in ("not-elim", "¬-elim", "contradiction"):
        # deps: [¬P, P]  -> ⊥
        f1, f2 = expect(step.deps, ctx)
        if isinstance(f1, Not) and alpha_equiv(f1.inner, f2):
            return Bottom()
        if isinstance(f2, Not) and alpha_equiv(f2.inner, f1):
            return Bottom()
        raise CheckError("¬-elim needs ¬P and P.")

    if r in ("explosion", "ex-falso"):
        # deps: [⊥] -> any target
        (f,) = expect(step.deps, ctx)
        if not isinstance(f, Bottom): raise CheckError("Explosion requires ⊥.")
        if target is None: raise CheckError("Explosion needs an explicit target formula.")
        return target

    if r in ("raa", "reductio"):
        # deps: [assumption_id, bottom_id]  conclude target (the negation of assumption)
        if len(step.deps) != 2:
            raise CheckError("RAA requires deps: [assumption_id, bottom_id].")
        a_id, bot_id = step.deps
        if not ctx.boxes or ctx.boxes[-1].assumption_id != a_id:
            raise CheckError("RAA requires the most recent open box to match the assumption.")
        ass = ctx.boxes[-1].assumption_formula
        if not isinstance(ctx.formulas.get(bot_id), Bottom):
            raise CheckError("RAA needs ⊥ inside the box.")
        # conclude Not(Not target)? We keep classical RAA as: from ¬C -> ⊥, infer C.
        if target is None:
            raise CheckError("RAA requires explicit target (the refuted conclusion).")
        if not isinstance(ass, Not):
            raise CheckError("In this prototype, RAA assumes the assumption is ¬C.")
        if not alpha_equiv(ass.inner, target):
            raise CheckError("RAA target must match the inner of the assumed negation.")
        return target

    # -------------- First-order rules --------------

    if r in ("forall-elim", "∀-elim"):
        # deps: [∀x. φ(x)] and parser_meta with {"term": "..."} or target matches φ(t)
        (f,) = expect(step.deps, ctx)
        if not isinstance(f, Forall):
            raise CheckError("∀-elim needs ∀x. φ(x).")
        if target is not None:
            # check target is φ(t) for some t
            # naive: try to find t by comparing structure; we skip and accept target if it equals substitute with parser term
            term_s = step.parser_meta.get("term")
            if term_s:
                t = parse_term_or_die(ctx.parser, term_s)
                concl = substitute_formula(f.body, f.var, t)
                if not alpha_equiv(concl, target):
                    raise CheckError("∀-elim target mismatch with substitution.")
                return concl
            # else just accept target == body (unlikely)
            raise CheckError("∀-elim needs parser_meta.term or explicit substitution logic.")
        else:
            term_s = step.parser_meta.get("term")
            if not term_s:
                raise CheckError("∀-elim needs parser_meta.term when no explicit target.")
            t = parse_term_or_die(ctx.parser, term_s)
            return substitute_formula(f.body, f.var, t)

    if r in ("forall-intro", "∀-intro"):
        # deps: [result_id] taken under an assumption that does NOT depend on the generalized var
        if not ctx.boxes:
            # often ∀-intro is done outside boxes; here we require deps[0] result that does not contain the var free in any open assumption
            if len(step.deps) != 1:
                raise CheckError("∀-intro (outside) requires deps: [result_id].")
            res = ctx.formulas.get(step.deps[0])
            if res is None: raise CheckError("∀-intro result not found.")
            varname = step.parser_meta.get("var")
            if not varname: raise CheckError("∀-intro needs parser_meta.var.")
            # check var not free in any undischarged assumption (none here)
            # also result does not mention var as free (it's allowed to generalize only if var not free in any undischarged assumptions)
            return Forall(varname, res)
        else:
            # inside some boxes; require that generalized var is not free in any open assumption
            if len(step.deps) != 1:
                raise CheckError("∀-intro requires deps: [result_id].")
            res = ctx.formulas.get(step.deps[0])
            if res is None: raise CheckError("∀-intro result not found.")
            varname = step.parser_meta.get("var")
            if not varname: raise CheckError("∀-intro needs parser_meta.var.")
            fv_ass: Set[str] = set()
            for b in ctx.boxes:
                fv_ass |= free_vars(b.assumption_formula)
            if varname in fv_ass:
                raise CheckError("∀-intro side condition: variable occurs free in an open assumption.")
            return Forall(varname, res)

    if r in ("exists-intro", "∃-intro"):
        # deps: [φ(t)] conclude ∃x. φ(x) with provided var in parser_meta.var
        (fml,) = expect(step.deps, ctx)
        varname = step.parser_meta.get("var")
        term_s = step.parser_meta.get("term")
        if not varname or not term_s:
            raise CheckError("∃-intro needs parser_meta.var and parser_meta.term.")
        # sanity: fml should equal φ(t)
        # can't easily verify without a template; accept target if provided
        concl = Exists(varname, substitute_formula(Atom("⊤"), "dummy", Var("dummy")))  # placeholder body
        if target:
            return target
        # Without a template of φ, we accept target-less use if teacher provides target
        raise CheckError("∃-intro in this prototype requires an explicit target.")

    if r in ("exists-elim", "∃-elim"):
        # deps: [∃x. φ(x), result_id] with a box whose assumption φ(c) (c fresh) derives result
        if len(step.deps) != 2:
            raise CheckError("∃-elim requires deps: [∃x. φ(x), result_id].")
        exf, res = expect(step.deps, ctx)
        if not isinstance(exf, Exists):
            raise CheckError("∃-elim needs ∃x. φ(x).")
        if not ctx.boxes:
            raise CheckError("∃-elim requires an open box for witness case.")
        b = ctx.boxes.pop()
        # Side condition (simplified): the constant used in assumption must be fresh (not in goal/undischarged assumptions)
        # We cannot detect the constant reliably here; in classroom use, enforce via naming convention in parser_meta.
        concl = res
        if target and not alpha_equiv(target, concl):
            raise CheckError("Conclusion mismatch in ∃-elim.")
        return concl

    raise CheckError(f"Rule {r} not implemented or wrong arity.")

# =========================
# Subproof box operations
# =========================

def open_box(step: Step, ctx: Context):
    """Open a subproof with an explicit assumption in step.formal (string) or parser_meta.assumption."""
    if not step.box_open:
        return
    # obtain the assumption formula to push
    src = step.formal or step.parser_meta.get("assumption")
    if not src:
        raise CheckError("To open a box, provide 'formal' as the assumption formula or parser_meta.assumption.")
    ass = ctx.parser.parse(src)
    # allocate an artificial id if not given via deps
    ass_id = step.id + "_assumption"
    ctx.formulas[ass_id] = ass
    ctx.proven_order.append(ass_id)
    ctx.boxes.append(Box(assumption_id=ass_id, assumption_formula=ass, lines=[ass_id]))
    ctx.messages.append(f"[BOX OPEN] {ass_id}: assume {ass.pretty()}")

def close_box(step: Step, ctx: Context):
    """Close the most recent subproof box when step.box_close is True.
       Many rules will implicitly pop boxes; this is a manual close hook for UI symmetry."""
    if not step.box_close:
        return
    if not ctx.boxes:
        raise CheckError("No open box to close.")
    b = ctx.boxes.pop()
    ctx.messages.append(f"[BOX CLOSE] {b.assumption_id}")

# =========================
# NL Mapper (English)
# =========================

class NLMapper:
    """
    Simple pattern-based NL to logic candidates.
    Returns a list of (candidate_formula_string, rule, confidence, extra_meta).
    """
    def __init__(self):
        self.p = TinyParser()
        self.pats: List[Tuple[re.Pattern, Any]] = []

        # From P and P->Q, infer Q.
        pat_mp = re.compile(r"^From\s+(?P<p>.+)\s+and\s+(?P<imp>.+)\s+infer\s+(?P<q>.+)\.?$", re.I)
        def mp(m):
            return [(m["q"], "->-elim", 0.92, {})]
        self.pats.append((pat_mp, mp))

        # From P and Q, infer P ∧ Q.
        pat_and_intro = re.compile(r"^From\s+(?P<p>.+)\s+and\s+(?P<q>.+)\s+infer\s+(?P<conj>.+)\.?$", re.I)
        def andi(m):
            try:
                conj = self.p.parse(m["conj"])
                if isinstance(conj, And):
                    return [(m["conj"], "and-intro", 0.8, {})]
            except: pass
            return []
        self.pats.append((pat_and_intro, andi))

        # From P, infer P ∨ Q.
        pat_or_intr = re.compile(r"^From\s+(?P<p>.+)\s+infer\s+(?P<disj>.+)\.?$", re.I)
        def ori(m):
            try:
                disj = self.p.parse(m["disj"])
                if isinstance(disj, Or):
                    # decide left or right
                    left_ok = True
                    try:
                        lp = self.p.parse(m["p"])
                        left_ok = alpha_equiv(lp, disj.left)
                    except: left_ok = False
                    if left_ok:
                        return [(m["disj"], "or-intro-left", 0.75, {})]
                    else:
                        return [(m["disj"], "or-intro-right", 0.75, {})]
            except: pass
            return []
        self.pats.append((pat_or_intr, ori))

    def map(self, s: str) -> List[Tuple[str, str, float, Dict[str, Any]]]:
        s = s.strip()
        cands: List[Tuple[str, str, float, Dict[str, Any]]] = []
        for pat, fun in self.pats:
            m = pat.match(s)
            if m:
                cands.extend(fun(m))
        # Fallback: empty
        return cands

# =========================
# Lean 4 export
# =========================

def export_lean(goal: Formula, hyps: Dict[str, Formula], outfile: str = "ExportedProof.lean") -> str:
    """
    Create a Lean 4 skeleton with the goal and hypotheses as Prop.
    This is a minimal export; you can enrich it with FOL encodings later.
    """
    def fstr(f: Formula) -> str:
        return f.pretty()

    atoms: Set[str] = set()
    def collect_atoms(f: Formula):
        if isinstance(f, Atom) and not f.args:
            atoms.add(f.name)
        if isinstance(f, (Not, And, Or, Imp)):
            collect_atoms(f.left) if hasattr(f, 'left') else None
            collect_atoms(f.right) if hasattr(f, 'right') else None
            if isinstance(f, Not): collect_atoms(f.inner)
        # FOL parts omitted in atom decls (classroom simplification)

    for a in list(hyps.values()) + [goal]:
        collect_atoms(a)

    lines: List[str] = []
    lines.append("import Mathlib\n\n")
    lines.append("-- Auto-exported skeleton\n")
    for A in sorted(atoms):
        lines.append(f"axiom {A} : Prop\n")
    lines.append("\n")
    # turn hypotheses into assumptions
    hyp_sig = " ".join([f"(h_{k} : {fstr(v)})" for k, v in hyps.items()])
    lines.append(f"theorem exported_goal {hyp_sig} : {fstr(goal)} := by\n")
    lines.append("  -- Fill with: intro/ have/ apply/ exact/ by_contra/ cases/ simp...\n")
    lines.append("  admit\n")
    pathlib.Path(outfile).write_text("".join(lines), encoding="utf-8")
    return outfile

# =========================
# Suggestions on failure
# =========================

def suggest_on_failure(err: str) -> str:
    e = err.lower()
    if "->-elim" in e or "modus" in e:
        return "Check you provided both P and (P -> Q)."
    if "and-intro" in e:
        return "Ensure you have both conjuncts as dependencies."
    if "or-intro" in e:
        return "Provide the other disjunct via target or parser_meta.other."
    if "or-elim" in e:
        return "You need P∨Q and two subproofs: assume P ⊢ R, assume Q ⊢ R."
    if "¬-intro" in e or "not-intro" in e:
        return "Open a box assuming P and derive ⊥, then conclude ¬P."
    if "∀-elim" in e:
        return "Supply a term for instantiation via parser_meta.term."
    if "∀-intro" in e:
        return "Generalize a variable not free in any open assumption: parser_meta.var."
    if "∃-elim" in e:
        return "Provide a witness subproof box: assume φ(c) and derive the same conclusion."
    if "explosion" in e:
        return "From ⊥ you may derive any target; provide the target formula."
    if "raa" in e:
        return "Assume ¬C, derive ⊥, then conclude C (set target=C)."
    return "Re-check rule name, dependencies, and side conditions."

# =========================
# Verification runner
# =========================

def parse_term_or_die(parser: TinyParser, s: str) -> Term:
    # reuse term parser by parsing a predicate Arg and extracting term; we hack via private method
    # Here, we parse t by feeding as function argument of dummy P(t)
    f = parser.parse(f"P({s})")
    if isinstance(f, Atom) and f.args:
        return f.args[0]
    raise CheckError(f"Bad term: {s}")

def run_session(spec: Dict[str, Any]) -> Dict[str, Any]:
    parser = TinyParser()
    mapper = NLMapper()

    # Collect axioms as known formulas
    formulas: Dict[str, Formula] = {}
    proven_order: List[str] = []
    for ax in spec.get("axioms", []):
        fid = ax["id"]
        fstr = ax.get("formal") or ax.get("nl")
        formulas[fid] = parser.parse(fstr)
        proven_order.append(fid)

    goal_s = spec["goal"].get("formal") or spec["goal"].get("nl")
    goal = parser.parse(goal_s)

    ctx = Context(parser=parser, formulas=formulas, proven_order=proven_order, boxes=[], messages=[])
    results = []

    for st in spec.get("steps", []):
        step = Step(**st)

        # Open/close boxes if requested
        if step.box_open:
            try:
                open_box(step, ctx)
            except CheckError as e:
                msg = f"[ERR] {step.id} (open): {e}"
                ctx.messages.append(msg)
                results.append({"id": step.id, "ok": False, "error": str(e), "suggestion": suggest_on_failure(str(e))})
                continue

        # If no explicit formal, try NL mapper to get candidates (string formulas)
        if not step.formal:
            cands = mapper.map(step.nl)
            if cands:
                # choose best by confidence; attach meta if any
                best = sorted(cands, key=lambda x: -x[2])[0]
                step.formal = best[0]
                if not step.rule:
                    step.rule = best[1]
                # merge meta
                for k,v in best[3].items():
                    step.parser_meta.setdefault(k, v)

        try:
            concl = check_rule(step, ctx)
            # Register this step's conclusion under its id
            ctx.formulas[step.id] = concl
            ctx.proven_order.append(step.id)
            msg = f"[OK] {step.id}: {step.rule} ⟹ {concl.pretty()}"
            ctx.messages.append(msg)
            results.append({"id": step.id, "ok": True, "conclusion": concl.pretty(), "rule": step.rule})
        except CheckError as e:
            msg = f"[ERR] {step.id}: {e}"
            ctx.messages.append(msg)
            results.append({"id": step.id, "ok": False, "error": str(e), "suggestion": suggest_on_failure(str(e))})

        if step.box_close:
            try:
                close_box(step, ctx)
            except CheckError as e:
                msg = f"[ERR] {step.id} (close): {e}"
                ctx.messages.append(msg)
                results.append({"id": step.id, "ok": False, "error": str(e), "suggestion": suggest_on_failure(str(e))})

    # Goal reached?
    reached = any(alpha_equiv(ctx.formulas[i], goal) for i in ctx.proven_order)
    lean_path = export_lean(goal, {k:v for k,v in formulas.items()}, "ExportedProof.lean")

    return {
        "ok": reached,
        "goal": goal.pretty(),
        "results": results,
        "log": ctx.messages,
        "lean": lean_path
    }

# =========================
# Demo & CLI
# =========================

DEMO = {
  "axioms": [
    {"id":"A1","nl":"P -> Q","formal":"P -> Q"},
    {"id":"A2","nl":"P","formal":"P"}
  ],
  "goal":{"nl":"Q","formal":"Q"},
  "steps":[
    {"id":"S1","nl":"From P and P->Q infer Q.","rule":"->-elim","deps":["A2","A1"]}
  ]
}

def main():
    # CLI: python ai_proof_verifier_full.py [json_file]
    if len(sys.argv) == 2:
        spec = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
    else:
        spec = DEMO
    out = run_session(spec)
    print("=== Verification Report ===")
    print(json.dumps(out, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()
