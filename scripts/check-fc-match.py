#!/usr/bin/env python3
"""Check that Challenge.lean states Formal Conjectures' jacobian_implication, and nothing else.

Palomar's Comparator checks that Solution proves the statement of Challenge.lean, with the same
definitions. This script checks the other link: that Challenge.lean is Formal Conjectures' text.

The check is a whitelist, not a search. Challenge.lean must consist of exactly:

* an optional header comment, `module`, `public import Mathlib` and a module docstring;
* `@[expose] public section`;
* Formal Conjectures' `RegularFunction.lean` from `namespace MvPolynomial` up to and including
  `RegularFunction.id`, paragraph for paragraph, then `end RegularFunction` and `end MvPolynomial`;
* `namespace MvPolynomial`, Formal Conjectures' `variable` line and its `poissonBracket`
  definition, `end MvPolynomial`;
* `namespace JacobianConjecture`, `open MvPolynomial RegularFunction`, Formal Conjectures'
  `JacobianConjectureProp`, `end JacobianConjecture`;
* `namespace Arxiv.«math.0608009»`, `open MvPolynomial JacobianConjecture`, Formal Conjectures'
  `variable` line, its `IsPoissonEndomorphism` and `PoissonConjectureFor`,
  `end Arxiv.«math.0608009»`;
* `namespace PoissonConjecture`, `open MvPolynomial JacobianConjecture Arxiv.«math.0608009»`, the
  same `variable` line, Formal Conjectures' statement of
  `poisson_conjecture.variants.jacobian_implication` with its docstring and without its
  `category`/`AMS` attribute, the body `by sorry`, and `end PoissonConjecture`. (Palomar rejects
  escaped name components such as `«math.0608009»` in theorem names; the definitions keep their
  names, so the statement is the same term.)

Each paragraph is compared character for character with Formal Conjectures at FC_COMMIT, where it
must occur exactly once. Free-text comments may not contain `/-`, so nested comments cannot hide
or expose code.

On the Formal Conjectures side the script checks that nothing before the copied text, in each of
the four source files, can change its meaning: every top-level command that is not a declaration
(a `variable`, `open`, `omit`, `universe`, `notation`, `set_option`, `instance`, `attribute`, a
macro, ... , including one behind an attribute or a modifier such as `public`) must be on a fixed
list, and so must the names of the declarations before it, which could otherwise shadow a name the
copied text uses.

Two of the four files also import Formal Conjectures' `FormalConjecturesUtil`, which this script
does not read. Its effect was checked once by hand instead: in Formal Conjectures' own build, the
statement and all eight definitions print (`pp.all`) exactly as in Challenge.lean, except that
`JacobianConjectureProp`'s universe parameters are named `u_2, u_3` there and `u_1, u_2` here.

`JacPoisson/Defs.lean` and `JacPoisson/FormalTarget.lean` are checked textually too, as a
regression check; Comparator is what guarantees that they agree with Challenge.lean.

Usage:
  check-fc-match.py [FC_CHECKOUT]   check; without an argument, download FC at FC_COMMIT
  check-fc-match.py --self-test [FC_CHECKOUT]
                                    check, then confirm that a list of altered Challenge,
                                    FormalTarget and Formal Conjectures files all fail
"""
import re
import sys
import urllib.request
from pathlib import Path

FC_COMMIT = "a64e959c32c270df4dd0d96d2027481f15750534"
REGULAR = "FormalConjecturesForMathlib/Algebra/MvPolynomial/RegularFunction.lean"
BRACKET = "FormalConjecturesForMathlib/Algebra/MvPolynomial/PoissonBracket.lean"
JACOBIAN = "FormalConjectures/Wikipedia/JacobianConjecture.lean"
CONJECTURE = "FormalConjectures/Arxiv/math.0608009/PoissonConjecture.lean"
NAMESPACE = "Arxiv.«math.0608009»"
# Palomar rejects escaped name components such as «math.0608009» in theorem names, so
# Challenge.lean states the theorem here, with Formal Conjectures' leaf name.
PALOMAR_NAMESPACE = "PoissonConjecture"
THEOREM = "poisson_conjecture.variants.jacobian_implication"
VAR_R = "variable {R σ : Type*} [CommRing R] [Fintype σ]"
VAR_K = "variable {K : Type*} [Field K] [CharZero K]"
ATTRIBUTE = "@[category research solved, AMS 14 17]\n"

# What Formal Conjectures' files may contain before the copied text: top-level commands that are
# not declarations, and the names of the declarations. Anything else fails the check.
FC_CONTEXT = {
    REGULAR: (["module", "public import Mathlib.Algebra.MvPolynomial.Monad",
               "public import Mathlib.Algebra.MvPolynomial.PDeriv",
               "public import Mathlib.Data.Matrix.Basic", "@[expose] public section",
               "namespace MvPolynomial", "variable {k : Type*} [CommRing k]",
               "variable {σ τ ι : Type*}", "namespace RegularFunction"],
              ["RegularFunction", "Jacobian", "comp"]),
    BRACKET: (["module", "public import Mathlib.Algebra.MvPolynomial.CommRing",
               "public import Mathlib.Algebra.MvPolynomial.PDeriv", "public section",
               "namespace MvPolynomial", VAR_R],
              []),
    JACOBIAN: (["module", "public import FormalConjecturesUtil", "@[expose] public section",
                "namespace JacobianConjecture", "section Conjecture",
                "open MvPolynomial RegularFunction", "variable (k : Type*)",
                "name_poly_vars X, Y, Z over k"],
               ["F", "G", "det_jacobian_F", "det_jacobian_G", "aeval_F_eq", "aeval_G_eq"]),
    CONJECTURE: (["module", "public import FormalConjectures.Wikipedia.JacobianConjecture",
                  "public import FormalConjecturesUtil", "@[expose] public section",
                  f"namespace {NAMESPACE}", "open MvPolynomial JacobianConjecture", VAR_K],
                 ["IsPoissonEndomorphism", "PoissonConjectureFor", "isPoissonEndomorphism_one_iff",
                  "poissonConjectureFor_one_iff", "poisson_conjecture",
                  "poisson_conjecture.variants.dimension_one",
                  "poisson_conjecture.variants.dimension_two",
                  "poisson_conjecture.variants.dimension_three",
                  "poisson_conjecture.variants.dimension_ge_two"]),
}
# The last copied declaration of each file; the context check covers everything before it.
LAST_USED = {REGULAR: "noncomputable def id ", BRACKET: "noncomputable def poissonBracket ",
             JACOBIAN: "def JacobianConjectureProp ", CONJECTURE: f"theorem {THEOREM} "}

# A block comment's body: no `-/` (which would end it) and no `/-` (which would nest).
COMMENT_BODY = r"(?:(?!-/|/-).)*"
# Attributes and modifiers that may stand before a command or declaration keyword.
PREFIX = r"(?:@\[[^\]]*\]\s*)*(?:(?:public|private|protected|noncomputable|unsafe|partial)\s+)*"
DECLARATION = re.compile(PREFIX + r"(theorem|lemma|def|abbrev|example)\b\s*([^\s:({\[]*)")


def fc_source(root, path):
    if root is not None:
        return (Path(root) / path).read_text(encoding="utf-8")
    url = f"https://raw.githubusercontent.com/google-deepmind/formal-conjectures/{FC_COMMIT}/{path}"
    with urllib.request.urlopen(url) as response:
        return response.read().decode("utf-8").replace("\r\n", "\n")


def strip_comments(text):
    """`text` with block comments (nested) and line comments replaced by spaces."""
    out, depth, i = [], 0, 0
    while i < len(text):
        two = text[i:i + 2]
        if two == "/-":
            depth, i = depth + 1, i + 2
            out.append("  ")
        elif two == "-/" and depth:
            depth, i = depth - 1, i + 2
            out.append("  ")
        elif two == "--" and not depth:
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            out.append(" " * (end - i))
            i = end
        else:
            out.append(text[i] if not depth or text[i] == "\n" else " ")
            i += 1
    return "".join(out)


def paragraph(text, marker):
    """The unique blank-line separated paragraph of `text` containing `marker`."""
    found = [p for p in text.split("\n\n") if marker in p]
    if len(found) != 1:
        raise SystemExit(f"error: expected one paragraph containing `{marker}`, found {len(found)}")
    return found[0]


def context(code):
    """Top-level commands that are not declarations, and the declarations' names, in `code`
    (comment-stripped). A line ending in ` in` scopes one command to the next declaration and is
    part of that declaration."""
    commands, names = [], []
    lines = code.split("\n")
    i = 0
    while i < len(lines):
        line = lines[i].rstrip()
        if not line or line[0].isspace():
            i += 1
            continue
        # Scoped `... in` lines, attributes standing on their own lines (possibly several lines
        # long) and blanked docstrings all belong to the declaration that follows.
        start = i
        while True:
            if i >= len(lines):
                # A prefix of the declaration the region ends at, which is copied verbatim.
                return commands, names
            s = lines[i].strip()
            if i > start and not s:
                i += 1
            elif s.endswith(" in"):
                i += 1
            elif s.startswith("@["):
                j, depth = i, 0
                while True:
                    depth += lines[j].count("[") - lines[j].count("]")
                    if depth <= 0:
                        break
                    j += 1
                if lines[j].rstrip().endswith("]"):
                    i = j + 1
                else:
                    break
            else:
                break
        m = DECLARATION.match(lines[i]) if i > start else None
        m = m or DECLARATION.match(lines[start])
        if m:
            names.append(m.group(2))
        else:
            commands.append(" ".join(lines[j].strip() for j in range(start, i + 1)).strip())
        i += 1
    return commands, names


def check_fc_context(sources):
    """Check that nothing in Formal Conjectures' files changes the copied text's meaning."""
    failures = []
    for path, (want_commands, want_names) in FC_CONTEXT.items():
        code = strip_comments(sources[path])
        last = code.index(LAST_USED[path])
        commands, names = context(code[:last])
        if commands != want_commands:
            failures.append(f"Formal Conjectures {path}: the commands before the copied text "
                            f"changed: {commands}")
        if names != want_names:
            failures.append(f"Formal Conjectures {path}: the declarations before the copied text "
                            f"changed: {names}")
    if f"{THEOREM} (n : ℕ)" not in sources[CONJECTURE]:
        failures.append("Formal Conjectures: the statement was not found")
    return failures


def regular_paragraphs(regular):
    """Formal Conjectures' RegularFunction.lean from `namespace MvPolynomial` to `id`."""
    start = regular.index("namespace MvPolynomial\n")
    end = regular.index("noncomputable def id ")
    end = regular.index("\n\n", end)
    return regular[start:end].split("\n\n")


def theorem_paragraph(conjecture):
    """Formal Conjectures' statement, docstring kept, attribute dropped."""
    text = paragraph(conjecture, f"theorem {THEOREM} ")
    if text.count(ATTRIBUTE) != 1:
        raise SystemExit("error: the statement's attribute changed in Formal Conjectures")
    return text.replace(ATTRIBUTE, "")


def expected_paragraphs(sources):
    """Challenge.lean's body, paragraph by paragraph."""
    regular, bracket, jacobian, conjecture = (sources[p] for p in (REGULAR, BRACKET, JACOBIAN,
                                                                  CONJECTURE))
    return [
        *regular_paragraphs(regular),
        "end RegularFunction",
        "end MvPolynomial",
        "namespace MvPolynomial",
        paragraph(bracket, VAR_R),
        paragraph(bracket, "noncomputable def poissonBracket "),
        "end MvPolynomial",
        "namespace JacobianConjecture",
        "open MvPolynomial RegularFunction",
        paragraph(jacobian, "def JacobianConjectureProp "),
        "end JacobianConjecture",
        f"namespace {NAMESPACE}",
        "open MvPolynomial JacobianConjecture",
        paragraph(conjecture, VAR_K),
        paragraph(conjecture, "def IsPoissonEndomorphism "),
        paragraph(conjecture, "def PoissonConjectureFor "),
        f"end {NAMESPACE}",
        f"namespace {PALOMAR_NAMESPACE}",
        f"open MvPolynomial JacobianConjecture {NAMESPACE}",
        VAR_K,
        theorem_paragraph(conjecture),
        f"end {PALOMAR_NAMESPACE}",
    ]


HEADER = re.compile(
    r"(?:/-" + COMMENT_BODY + r"-/\n)?"
    r"module\n\n"
    r"public import Mathlib\n\n"
    r"/-!" + COMMENT_BODY + r"-/\n\n"
    r"@\[expose\] public section\n\n",
    re.S,
)


def check_challenge(challenge, expected):
    """Failures of Challenge.lean against the whitelist; empty if it passes."""
    header = HEADER.match(challenge)
    if header is None:
        return ["Challenge.lean: the header (comment, `module`, `public import Mathlib`, module "
                "docstring, `@[expose] public section`) is not in the expected form"]
    body = challenge[header.end():]
    if not body.endswith("\n") or body.endswith("\n\n"):
        return ["Challenge.lean: the file must end with one newline after the last `end`"]
    paragraphs = body[:-1].split("\n\n")
    if len(paragraphs) != len(expected):
        return [f"Challenge.lean: {len(paragraphs)} top-level paragraphs, expected "
                f"{len(expected)}"]
    failures = []
    for index, (actual, wanted) in enumerate(zip(paragraphs, expected), 1):
        if actual != wanted:
            first = actual.splitlines()[0] if actual else ""
            failures.append(f"Challenge.lean: paragraph {index} (`{first}`) is not Formal "
                            "Conjectures' text")
    return failures


def statement(text):
    """`theorem THEOREM ... :=`, without docstring, attributes or proof."""
    return re.findall(r"theorem " + re.escape(THEOREM) + r"(?=[ \n]).*?:=", text, re.S)


def type_guard():
    """The `example` in FormalTarget.lean equating the types under both namespaces."""
    return (f"example : type_of% @{NAMESPACE}.{THEOREM}.{{w}} =\n"
            f"    type_of% @{PALOMAR_NAMESPACE}.{THEOREM}.{{w}} :=\n  rfl")


def check_regression(defs, target, sources):
    """Textual checks of the proof's own copies; Comparator is the real check of these."""
    failures = []
    regular, bracket, jacobian, conjecture = (sources[p] for p in (REGULAR, BRACKET, JACOBIAN,
                                                                  CONJECTURE))
    whole = regular[regular.index("namespace MvPolynomial\n"):].rstrip("\n")
    wanted = [whole, paragraph(bracket, VAR_R), paragraph(bracket, "noncomputable def poissonBracket "),
              paragraph(jacobian, "def JacobianConjectureProp "), paragraph(conjecture, VAR_K),
              paragraph(conjecture, "def IsPoissonEndomorphism "),
              paragraph(conjecture, "def PoissonConjectureFor ")]
    for text in wanted:
        if defs.count(text) != 1:
            failures.append(f"JacPoisson/Defs.lean: `{text.splitlines()[0]}` ... differs from "
                            "Formal Conjectures")
    commands, _ = context(strip_comments(defs))
    want = ["module", "public import Mathlib", "@[expose] public section",
            "namespace MvPolynomial", "variable {k : Type*} [CommRing k]", "variable {σ τ ι : Type*}",
            "namespace RegularFunction", "end RegularFunction", "end MvPolynomial",
            "namespace MvPolynomial", VAR_R, "end MvPolynomial", "namespace JacobianConjecture",
            "open MvPolynomial RegularFunction", "end JacobianConjecture", f"namespace {NAMESPACE}",
            "open MvPolynomial JacobianConjecture", VAR_K, f"end {NAMESPACE}"]
    if commands != want:
        failures.append(f"JacPoisson/Defs.lean: the context of the definitions changed: {commands}")
    code = strip_comments(target)
    fc_statement = statement(conjecture)
    found = statement(code)
    if len(found) != 2 or any(s != fc_statement[0] for s in found):
        failures.append("JacPoisson/FormalTarget.lean: the statements differ from Formal "
                        "Conjectures'")
    if code.count(type_guard()) != 1:
        failures.append("JacPoisson/FormalTarget.lean: the `example` checking that both names have "
                        "the same statement is missing or changed")
    commands, _ = context(code)
    want = ["module", "public import JacPoisson.Main", "@[expose] public section",
            f"namespace {NAMESPACE}", "open MvPolynomial JacobianConjecture", VAR_K,
            f"end {NAMESPACE}", f"namespace {PALOMAR_NAMESPACE}",
            f"open MvPolynomial JacobianConjecture {NAMESPACE}", VAR_K, f"end {PALOMAR_NAMESPACE}",
            "section", "universe w", "end"]
    if commands != want:
        failures.append(f"JacPoisson/FormalTarget.lean: the context of the statements changed: "
                        f"{commands}")
    return failures


def mutations(challenge):
    """Altered Challenge files that must all fail. Each is (description, text)."""
    ns = f"namespace {NAMESPACE}\n"
    docstring = "/--\nThe Jacobian conjecture in dimension $2n$ implies"
    cases = [
        ("universe of K restricted", challenge.replace(VAR_K, VAR_K.replace("Type*", "Type"))),
        ("extra instance binder", challenge.replace(VAR_K + "\n", VAR_K + "\n\nvariable "
                                                    "[DecidableEq K]\n")),
        ("shadowing variable before the theorem", challenge.replace(
            docstring, "variable {K : Type 1} [Field K] [CharZero K]\n\n" + docstring)),
        ("local Function.Bijective", challenge.replace(
            ns, ns + "\ndef Function.Bijective {α β : Type*} (_ : α → β) : Prop := True\n")),
        ("duplicated Fintype binder", challenge.replace(VAR_R, VAR_R + " [Fintype σ]")),
        ("set_option before the theorem", challenge.replace(
            docstring, "set_option autoImplicit true\n\n" + docstring)),
        ("public notation before the theorem", challenge.replace(
            docstring, "public notation \"‖\" x \"‖\" => x\n\n" + docstring)),
        ("attributed instance in a namespace", challenge.replace(
            ns, ns + "\n@[instance] private def inst : Inhabited ℕ := ⟨1⟩\n")),
        ("open Classical added", challenge.replace("open MvPolynomial RegularFunction\n",
                                                   "open MvPolynomial RegularFunction Classical\n")),
        ("changed hypothesis", challenge.replace("(Fin (2 * n))", "(Fin (2 * n + 1))")),
        ("changed definition body", challenge.replace("Function.Bijective φ",
                                                      "Function.Injective φ")),
        ("changed Jacobian condition", challenge.replace("IsUnit F.Jacobian.det",
                                                         "F.Jacobian.det ≠ 0")),
        ("one-sided inverse", challenge.replace("G.comp F = id k σ ∧\n    F.comp G = id k σ",
                                                "G.comp F = id k σ")),
        ("RegularFunction.aeval added", challenge.replace(
            "end RegularFunction\n", "noncomputable def aeval : ℕ := 0\n\nend RegularFunction\n")),
        ("nested comment in the docstring", challenge.replace(
            docstring, "/-- /- -/\nThe Jacobian conjecture in dimension $2n$ implies")),
        ("code hidden after the module docstring", challenge.replace(
            "@[expose] public section", "instance : Inhabited Nat := ⟨1⟩\n\n"
                                        "@[expose] public section")),
        ("extra import", challenge.replace("public import Mathlib\n",
                                           "public import Mathlib\npublic import Batteries\n")),
        ("Mathlib submodule import", challenge.replace("public import Mathlib\n",
                                                       "public import Mathlib.Logic.Basic\n")),
        ("proof other than sorry", challenge.replace(": PoissonConjectureFor K n := by\n  sorry",
                                                     ": PoissonConjectureFor K n := by\n  "
                                                     "exact sorry")),
        ("theorem in another namespace", challenge.replace(
            f"namespace {PALOMAR_NAMESPACE}\n", f"namespace {PALOMAR_NAMESPACE}.Other\n")),
        ("category attribute kept", challenge.replace(
            "-/\ntheorem poisson_conjecture", "-/\n@[simp]\ntheorem poisson_conjecture")),
    ]
    for description, text in cases:
        if text == challenge:
            raise SystemExit(f"error: self-test mutation `{description}` did not apply")
    return cases


def target_mutations(target):
    """Altered FormalTarget files that must all fail."""
    guard = type_guard()
    cases = [
        ("universe of K restricted", target.replace(VAR_K, VAR_K.replace("Type*", "Type"), 1)),
        ("extra instance binder", target.replace(VAR_K + "\n", VAR_K + "\n\nvariable "
                                                 "[DecidableEq K]\n", 1)),
        ("type check commented out", target.replace(guard, "/-\n" + guard + "\n-/")),
        ("type check at a fixed universe", target.replace(guard, guard.replace("{w}", "{0}"))),
        ("set_option before the theorems", target.replace(
            f"namespace {NAMESPACE}\n", f"set_option autoImplicit true\n\nnamespace {NAMESPACE}\n")),
    ]
    for description, text in cases:
        if text == target:
            raise SystemExit(f"error: self-test mutation `{description}` did not apply")
    return cases


def fc_mutations(sources):
    """Formal Conjectures files whose context could change the copied text. Each is
    (description, path, text)."""
    jac = sources[JACOBIAN]
    conj = sources[CONJECTURE]
    reg = sources[REGULAR]
    jns = "namespace JacobianConjecture\n"
    cases = [
        ("FC variable before JacobianConjectureProp", JACOBIAN,
         jac.replace(jns, jns + "\nvariable {σ : Type 1}\n", 1)),
        ("FC public notation before the statement", CONJECTURE,
         conj.replace(VAR_K, "public notation \"‖\" x \"‖\" => x\n\n" + VAR_K, 1)),
        ("FC public notation with a comment after the modifier", CONJECTURE,
         conj.replace(VAR_K, "public /- c -/ notation \"‖\" x \"‖\" => x\n\n" + VAR_K, 1)),
        ("FC attributed instance before RegularFunction", REGULAR,
         reg.replace("namespace RegularFunction\n",
                     "namespace RegularFunction\n\n@[instance] def inst : Inhabited ℕ := ⟨1⟩\n", 1)),
        ("FC shadowing definition before the statement", CONJECTURE,
         conj.replace(VAR_K, VAR_K + "\n\ndef Fin (n : ℕ) : Type := Unit", 1)),
        ("FC set_option before poissonBracket", BRACKET,
         sources[BRACKET].replace(VAR_R, "set_option autoImplicit true\n\n" + VAR_R, 1)),
    ]
    for description, path, text in cases:
        if text == sources[path]:
            raise SystemExit(f"error: self-test mutation `{description}` did not apply")
    return cases


def main():
    args = sys.argv[1:]
    self_test = "--self-test" in args
    args = [a for a in args if a != "--self-test"]
    root = args[0] if args else None
    source = f"checkout {root}" if root else f"GitHub at {FC_COMMIT}"
    sources = {path: fc_source(root, path) for path in (REGULAR, BRACKET, JACOBIAN, CONJECTURE)}
    repo = Path(__file__).resolve().parent.parent
    challenge = (repo / "Challenge.lean").read_text(encoding="utf-8")
    defs = (repo / "JacPoisson" / "Defs.lean").read_text(encoding="utf-8")
    target = (repo / "JacPoisson" / "FormalTarget.lean").read_text(encoding="utf-8")
    expected = expected_paragraphs(sources)
    failures = (check_fc_context(sources) + check_challenge(challenge, expected)
                + check_regression(defs, target, sources))
    if failures:
        print("\n".join(failures), file=sys.stderr)
        raise SystemExit(1)
    print(f"OK: Challenge.lean is Formal Conjectures' definitions and statement, and nothing else "
          f"(Formal Conjectures from {source})")
    if self_test:
        passed = [d for d, text in mutations(challenge) if not check_challenge(text, expected)]
        passed += [f"FormalTarget: {d}" for d, text in target_mutations(target)
                   if not check_regression(defs, text, sources)]
        for d, path, text in fc_mutations(sources):
            if not check_fc_context({**sources, path: text}):
                passed.append(d)
        if passed:
            print("self-test FAILED, these altered files passed: " + "; ".join(passed),
                  file=sys.stderr)
            raise SystemExit(1)
        n = len(mutations(challenge)) + len(target_mutations(target)) + len(fc_mutations(sources))
        print(f"OK: self-test, all {n} altered files fail")


if __name__ == "__main__":
    main()
