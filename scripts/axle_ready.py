#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
axle_ready.py

Rewrite already-copied Lean audit files into AXLE-ready statement/proof files.

This script DOES NOT:
- call AXLE
- call an API
- call `axle verify-proof`
- create verification certificates

It DOES:
- rewrite imports to `import Mathlib`
- remove local project opens like `open Lehmer.Basic`
- normalize common Lean Unicode syntax
- rewrite common `rcases h with ⟨...⟩` patterns to ASCII `cases`
- parameterize selected local defs with explicit dependency arguments
- rewrite applications of those local defs
- inject dependency binders into theorem/lemma signatures
- rewrite calls to local theorems with explicit dependency arguments
- turn statement theorem/lemma bodies into `by sorry`
- preserve proof theorem/lemma bodies
- generate source-map JSON
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys
from typing import Any, Dict, List, Optional, Sequence, Tuple


# ---------------------------------------------------------------------------
# IO
# ---------------------------------------------------------------------------

def eprint(*args: Any) -> None:
    print(*args, file=sys.stderr)


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8", newline="\n")


def write_json(path: Path, data: Dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(data, indent=2, ensure_ascii=False),
        encoding="utf-8",
        newline="\n",
    )


def relpath_or_str(path: Optional[Path], root: Path) -> Optional[str]:
    if path is None:
        return None
    try:
        return path.resolve().relative_to(root.resolve()).as_posix()
    except ValueError:
        return path.resolve().as_posix()


# ---------------------------------------------------------------------------
# Config
# ---------------------------------------------------------------------------

class Config:
    def __init__(
        self,
        root: Path,
        audit_dir: Path,
        axle_dir: Path,
        statement_dir: Path,
        proof_dir: Path,
        source_map_dir: Path,
        mathlib_import: str,
    ) -> None:
        self.root = root
        self.audit_dir = audit_dir
        self.axle_dir = axle_dir
        self.statement_dir = statement_dir
        self.proof_dir = proof_dir
        self.source_map_dir = source_map_dir
        self.mathlib_import = mathlib_import

    @staticmethod
    def from_args(args: argparse.Namespace) -> "Config":
        root = Path(args.root).resolve() if args.root else Path.cwd().resolve()

        axle_dir = Path(args.axle_dir).resolve() if args.axle_dir else (
            root / "Lean" / "Lehmer" / "Audit-axle"
        )

        audit_dir = Path(args.audit_dir).resolve() if args.audit_dir else (
            root / "Lean" / "Lehmer" / "Audit"
        )

        statement_dir = Path(args.statement_dir).resolve() if args.statement_dir else (
            axle_dir / "Audit_statement"
        )

        proof_dir = Path(args.proof_dir).resolve() if args.proof_dir else (
            axle_dir / "Audit_proof"
        )

        source_map_dir = Path(args.source_map_dir).resolve() if args.source_map_dir else (
            axle_dir / "source-map"
        )

        return Config(
            root=root,
            audit_dir=audit_dir,
            axle_dir=axle_dir,
            statement_dir=statement_dir,
            proof_dir=proof_dir,
            source_map_dir=source_map_dir,
            mathlib_import=args.mathlib_import,
        )

    def ensure_dirs(self) -> None:
        self.axle_dir.mkdir(parents=True, exist_ok=True)
        self.statement_dir.mkdir(parents=True, exist_ok=True)
        self.proof_dir.mkdir(parents=True, exist_ok=True)
        self.source_map_dir.mkdir(parents=True, exist_ok=True)


def add_common_args(p: argparse.ArgumentParser) -> None:
    p.add_argument("--root", help="Project root. Default: current directory.")
    p.add_argument("--audit-dir", help="Original audit directory.")
    p.add_argument("--axle-dir", help="Audit-axle root directory.")
    p.add_argument("--statement-dir", help="Directory of *.statement.lean files.")
    p.add_argument("--proof-dir", help="Directory of *.proof.lean files.")
    p.add_argument("--source-map-dir", help="Directory of *.map.json files.")
    p.add_argument("--mathlib-import", default="Mathlib")


# ---------------------------------------------------------------------------
# Regex / Lean helpers
# ---------------------------------------------------------------------------

UNICODE_REPLACEMENTS = {
    "ℕ": "Nat",
    "→": "->",
    "∀": "forall",
    "∨": "\\/",
    "∧": "/\\",
    "λ": "fun ",
    "≤": "<=",
    "≥": ">=",
    "≠": "!=",
}

IMPORT_RE = re.compile(r"(?m)^\s*import\s+[A-Za-z0-9_.]+\s*$")

LOCAL_OPEN_RE = re.compile(
    r"(?m)^\s*open\s+Lehmer(?:\.[A-Za-z0-9_.]+)?(?:\s+[A-Za-z0-9_.]+)*\s*$"
)

LOCAL_OPEN_SCOPED_RE = re.compile(
    r"(?m)^\s*open\s+scoped\s+Lehmer(?:\.[A-Za-z0-9_.]+)?\s*$"
)

THEOREM_START_RE = re.compile(
    r"(?m)^\s*(?:@\[[^\]]+\]\s*)*(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'.]*)"
)

DECL_OR_END_BOUNDARY_RE = re.compile(
    r"(?m)^\s*(?:@\[[^\]]+\]\s*)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class)\b"
    r"|^\s*end\b"
)

DEF_HEADER_RE = re.compile(
    r"(?m)^(?P<indent>\s*)def\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)(?P<rest>[^\n]*)$"
)

THEOREM_HEADER_LINE_RE = re.compile(
    r"(?m)^(?P<indent>\s*)(?P<attrs>(?:@\[[^\]]+\]\s*)*)"
    r"(?P<kind>theorem|lemma)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)(?P<rest>[^\n]*)$"
)


def normalize_ascii(text: str) -> str:
    out = text.replace("\r\n", "\n").replace("\r", "\n")

    for src, dst in UNICODE_REPLACEMENTS.items():
        out = out.replace(src, dst)

    # Rewrite line-based:
    #   ¬ ∃ n : Nat, P
    # into:
    #   Not (Exists fun n : Nat => P)
    out = re.sub(
        r"¬\s*∃\s+([A-Za-z_][A-Za-z0-9_']*)\s*:\s*Nat\s*,\s*([^\n:]+)",
        r"Not (Exists fun \1 : Nat => \2)",
        out,
    )

    # Remaining simple negation.
    out = out.replace("¬", "Not ")

    # Fix spacing without touching newlines.
    out = re.sub(r"[ \t]+\):=", ") :=", out)
    out = re.sub(r"[ \t]+\)[ \t]*:=", ") :=", out)
    out = re.sub(r"Not[ \t]{2,}", "Not ", out)

    return out


def rewrite_rcases_tuple_to_cases(text: str) -> str:
    """
    Rewrite:

      rcases h with ⟨n, hA, hB⟩
      exact foo n hA hB

    into:

      cases h with
      | intro n hPair =>
          cases hPair with
          | intro hA hB =>
              exact foo n hA hB

    Supports tuple sizes 2 and 3.
    """
    lines = text.splitlines()
    out: List[str] = []

    pattern = re.compile(
        r"^(?P<indent>\s*)rcases\s+(?P<h>[A-Za-z_][A-Za-z0-9_']*)\s+with\s+⟨(?P<vars>[^⟩]+)⟩\s*$"
    )

    i = 0
    while i < len(lines):
        line = lines[i]
        m = pattern.match(line)

        if not m:
            out.append(line)
            i += 1
            continue

        indent = m.group("indent")
        h = m.group("h")
        vars_ = [v.strip() for v in m.group("vars").split(",") if v.strip()]
        next_line = lines[i + 1] if i + 1 < len(lines) else None
        next_payload = next_line.strip() if next_line is not None else None

        if len(vars_) == 2:
            a, b = vars_
            out.append(f"{indent}cases {h} with")
            out.append(f"{indent}| intro {a} {b} =>")
            if next_payload:
                out.append(f"{indent}    {next_payload}")
                i += 2
            else:
                i += 1
            continue

        if len(vars_) == 3:
            a, b, c = vars_
            out.append(f"{indent}cases {h} with")
            out.append(f"{indent}| intro {a} hPair =>")
            out.append(f"{indent}    cases hPair with")
            out.append(f"{indent}    | intro {b} {c} =>")
            if next_payload:
                out.append(f"{indent}        {next_payload}")
                i += 2
            else:
                i += 1
            continue

        out.append(line)
        i += 1

    return "\n".join(out) + ("\n" if text.endswith("\n") else "")


def parse_replace_items(items: Sequence[str]) -> List[Tuple[str, str]]:
    replacements: List[Tuple[str, str]] = []
    for item in items:
        if "=" not in item:
            raise ValueError(f"Invalid --replace value, expected FROM=TO: {item}")
        src, dst = item.split("=", 1)
        src = src.strip()
        dst = dst.strip()
        if not src or not dst:
            raise ValueError(f"Invalid --replace value, expected FROM=TO: {item}")
        replacements.append((src, dst))
    return replacements


def parse_dep_items(items: Sequence[str]) -> Tuple[List[str], Dict[str, str]]:
    deps: List[str] = []
    dep_binders: Dict[str, str] = {}

    for item in items:
        dep = item.strip()
        if not dep:
            continue

        m = re.match(r"([A-Za-z_][A-Za-z0-9_']*)\s*:", dep)
        if not m:
            raise ValueError(f"Invalid --dep binder, expected 'name : type': {dep}")

        deps.append(dep)
        dep_binders[m.group(1)] = dep

    return deps, dep_binders


def parse_def_param_items(items: Sequence[str]) -> Dict[str, List[str]]:
    result: Dict[str, List[str]] = {}

    for item in items:
        if "=" not in item:
            raise ValueError(f"Invalid --def-param, expected DefName=dep1,dep2: {item}")

        name, rhs = item.split("=", 1)
        name = name.strip()
        deps = [x.strip() for x in rhs.split(",") if x.strip()]

        if not name or not deps:
            raise ValueError(f"Invalid --def-param, expected DefName=dep1,dep2: {item}")

        result[name] = deps

    return result


def apply_replacements(text: str, replacements: Sequence[Tuple[str, str]]) -> str:
    out = text
    for src, dst in replacements:
        out = out.replace(src, dst)
    return out


def source_imports(text: str) -> List[str]:
    return re.findall(r"(?m)^\s*import\s+([A-Za-z0-9_.]+)\s*$", text)


def remove_imports_and_local_opens(text: str, mathlib_import: str) -> str:
    out = IMPORT_RE.sub("", text)
    out = LOCAL_OPEN_RE.sub("", out)
    out = LOCAL_OPEN_SCOPED_RE.sub("", out)

    lines = out.splitlines()
    while lines and lines[0].strip() == "":
        lines.pop(0)

    return f"import {mathlib_import}\n\n" + "\n".join(lines).rstrip() + "\n"


def theorem_names(text: str) -> List[str]:
    return [m.group(1) for m in THEOREM_START_RE.finditer(text)]


def contains_sorry_or_admit(text: str) -> bool:
    return bool(re.search(r"\b(sorry|admit)\b", text))


def non_ascii_chars(text: str, limit: int = 80) -> List[Dict[str, Any]]:
    found: List[Dict[str, Any]] = []
    for i, ch in enumerate(text):
        if ord(ch) > 127:
            found.append({"index": i, "char": ch, "codepoint": f"U+{ord(ch):04X}"})
            if len(found) >= limit:
                break
    return found


# ---------------------------------------------------------------------------
# Parametrization
# ---------------------------------------------------------------------------

def parametrize_def_headers(
    text: str,
    def_params: Dict[str, List[str]],
    dep_binders: Dict[str, str],
) -> str:
    def repl(m: re.Match[str]) -> str:
        name = m.group("name")
        if name not in def_params:
            return m.group(0)

        indent = m.group("indent")
        rest = m.group("rest")

        binders = []
        for dep_name in def_params[name]:
            if dep_name not in dep_binders:
                raise ValueError(f"Unknown dependency '{dep_name}' used in --def-param for {name}")
            binders.append(f"({dep_binders[dep_name]})")

        return f"{indent}def {name} " + " ".join(binders) + rest

    return DEF_HEADER_RE.sub(repl, text)


def rewrite_def_applications(
    text: str,
    def_params: Dict[str, List[str]],
) -> str:
    """
    Rewrite applications of local defs.

    Example:
      AuditCaseACandidate n
    becomes:
      AuditCaseACandidate LehmerComposite n

    For nullary local defs:
      CaseAEmptyAudit
    becomes:
      CaseAEmptyAudit LehmerComposite InCaseA

    Def declaration lines are skipped.
    """
    lines = text.splitlines()
    out: List[str] = []

    for line in lines:
        stripped = line.lstrip()

        skip_names = [
            name for name in def_params
            if re.match(rf"def\s+{re.escape(name)}\b", stripped)
        ]

        new_line = line

        for name, deps in def_params.items():
            if name in skip_names:
                continue

            dep_args = " ".join(deps)
            first_dep = deps[0]

            pattern = re.compile(rf"\b{re.escape(name)}\b(?!\s+{re.escape(first_dep)}\b)")
            new_line = pattern.sub(f"{name} {dep_args}", new_line)

        out.append(new_line)

    return "\n".join(out) + ("\n" if text.endswith("\n") else "")


def parenthesize_not_applications(text: str) -> str:
    """
    Fix Lean syntax after rewriting:
      Not AuditCaseAClass InCaseA n
    into:
      Not (AuditCaseAClass InCaseA n)

    Also:
      Not InCaseA n
    into:
      Not (InCaseA n)
    """
    lines = text.splitlines()
    out: List[str] = []

    pattern = re.compile(
        r"(?P<prefix>\bNot\s+)"
        r"(?P<head>[A-Za-z_][A-Za-z0-9_'.]*)"
        r"(?P<args>(?:\s+[A-Za-z_][A-Za-z0-9_'.]*)+)"
        r"(?P<suffix>\s*(?:$|:=|,|\)|->))"
    )

    for line in lines:
        if "Not (" in line:
            out.append(line)
            continue

        def repl(m: re.Match[str]) -> str:
            expr = f"{m.group('head')}{m.group('args')}"
            return f"Not ({expr}){m.group('suffix')}"

        out.append(pattern.sub(repl, line))

    return "\n".join(out) + ("\n" if text.endswith("\n") else "")


def inject_theorem_dependency_binders(
    text: str,
    deps: Sequence[str],
) -> str:
    """
    Add every dependency as an explicit binder to every theorem/lemma.

    theorem foo {n : Nat} : ...
    becomes:

    theorem foo
        (D1 : ...)
        (D2 : ...)
        {n : Nat} : ...
    """
    if not deps:
        return text

    dep_lines = "".join(f"\n    ({dep})" for dep in deps)

    def repl(m: re.Match[str]) -> str:
        indent = m.group("indent")
        attrs = m.group("attrs")
        kind = m.group("kind")
        name = m.group("name")
        rest = m.group("rest")

        following = text[m.end(): m.end() + 500]
        if deps and f"({deps[0]})" in following:
            return m.group(0)

        return f"{indent}{attrs}{kind} {name}{dep_lines}{rest}"

    return THEOREM_HEADER_LINE_RE.sub(repl, text)


def rewrite_theorem_calls(
    text: str,
    theorem_names_: Sequence[str],
    dep_names: Sequence[str],
) -> str:
    """
    Rewrite local theorem calls to pass explicit dependency arguments.

    Example:
      exact caseA_empty_audit n hCand hA

    becomes:
      exact caseA_empty_audit LehmerComposite InCaseA ... n hCand hA
    """
    if not dep_names:
        return text

    dep_args = " ".join(dep_names)
    first_dep = dep_names[0]

    lines = text.splitlines()
    out: List[str] = []

    for line in lines:
        stripped = line.lstrip()

        if re.match(r"(?:@\[[^\]]+\]\s*)?(theorem|lemma)\s+", stripped):
            out.append(line)
            continue

        new_line = line

        for name in theorem_names_:
            pattern = re.compile(
                rf"\b{re.escape(name)}\b(?!\s+{re.escape(first_dep)}\b)"
            )
            new_line = pattern.sub(f"{name} {dep_args}", new_line)

        out.append(new_line)

    return "\n".join(out) + ("\n" if text.endswith("\n") else "")


# ---------------------------------------------------------------------------
# Statementize
# ---------------------------------------------------------------------------

def find_theorem_blocks(text: str) -> List[Tuple[int, int]]:
    starts = list(THEOREM_START_RE.finditer(text))
    boundaries = list(DECL_OR_END_BOUNDARY_RE.finditer(text))

    blocks: List[Tuple[int, int]] = []

    for start_match in starts:
        start = start_match.start()
        end = len(text)

        for boundary in boundaries:
            b = boundary.start()
            if b > start:
                end = b
                break

        blocks.append((start, end))

    return blocks


def statementize_theorem_block(block: str) -> str:
    idx = block.find(":=")
    if idx == -1:
        return block.rstrip() + " := by\n  sorry\n"

    header = block[:idx].rstrip()
    header = re.sub(r"[ \t]+\):\s*$", ") :", header)
    header = re.sub(r"[ \t]+\)[ \t]*:=$", ") :=", header)
    return header + " := by\n  sorry\n"


def statementize_all_theorems(text: str) -> str:
    blocks = find_theorem_blocks(text)
    if not blocks:
        return text

    out_parts: List[str] = []
    cursor = 0

    for start, end in blocks:
        out_parts.append(text[cursor:start])
        block = text[start:end]
        out_parts.append(statementize_theorem_block(block))
        cursor = end

    out_parts.append(text[cursor:])
    return "".join(out_parts).rstrip() + "\n"


# ---------------------------------------------------------------------------
# Core prepare
# ---------------------------------------------------------------------------

def normalize_spacing(text: str) -> str:
    out = text
    out = re.sub(r"[ \t]+\):=", ") :=", out)
    out = re.sub(r"[ \t]+\)[ \t]*:=", ") :=", out)
    out = re.sub(r"Not[ \t]{2,}", "Not ", out)
    out = out.replace(" ) := by", ") := by")
    out = out.replace(" ):= by", ") := by")
    return out


def prepare_text(
    raw_text: str,
    *,
    deps: Sequence[str],
    dep_names: Sequence[str],
    dep_binders: Dict[str, str],
    def_params: Dict[str, List[str]],
    replacements: Sequence[Tuple[str, str]],
    mathlib_import: str,
    make_statement: bool,
    ascii_mode: bool,
) -> str:
    text = raw_text

    if ascii_mode:
        text = normalize_ascii(text)

    text = apply_replacements(text, replacements)
    text = remove_imports_and_local_opens(text, mathlib_import)

    all_theorem_names = theorem_names(text)

    text = parametrize_def_headers(text, def_params, dep_binders)
    text = rewrite_def_applications(text, def_params)
    text = parenthesize_not_applications(text)
    text = inject_theorem_dependency_binders(text, deps)

    if not make_statement:
        text = rewrite_rcases_tuple_to_cases(text)
        text = rewrite_theorem_calls(text, all_theorem_names, dep_names)

    if make_statement:
        text = statementize_all_theorems(text)

    text = normalize_spacing(text)
    return text.rstrip() + "\n"


def build_map(
    *,
    base: str,
    source_file: Optional[Path],
    statement_file: Path,
    proof_file: Path,
    map_file: Path,
    deps: Sequence[str],
    def_params: Dict[str, List[str]],
    replacements: Sequence[Tuple[str, str]],
    statement_text: str,
    proof_text: str,
    cfg: Config,
) -> Dict[str, Any]:
    st_theorems = theorem_names(statement_text)
    pr_theorems = theorem_names(proof_text)

    theorem_rows: List[Dict[str, Any]] = []
    for name in sorted(set(st_theorems) | set(pr_theorems)):
        theorem_rows.append({
            "source_name": name,
            "axle_name": name,
            "in_statement": name in st_theorems,
            "in_proof": name in pr_theorems,
            "abstracted_dependencies": list(deps),
        })

    return {
        "base": base,
        "source_file": relpath_or_str(source_file, cfg.root) if source_file else None,
        "statement_file": relpath_or_str(statement_file, cfg.root),
        "proof_file": relpath_or_str(proof_file, cfg.root),
        "map_file": relpath_or_str(map_file, cfg.root),
        "mathlib_import": cfg.mathlib_import,
        "replacements": [{"from": a, "to": b} for a, b in replacements],
        "abstracted_dependencies": list(deps),
        "def_params": def_params,
        "theorems": theorem_rows,
    }


# ---------------------------------------------------------------------------
# Commands
# ---------------------------------------------------------------------------

def cmd_init(args: argparse.Namespace) -> int:
    cfg = Config.from_args(args)
    cfg.ensure_dirs()

    print(json.dumps({
        "created": True,
        "root": str(cfg.root),
        "statement_dir": str(cfg.statement_dir),
        "proof_dir": str(cfg.proof_dir),
        "source_map_dir": str(cfg.source_map_dir),
    }, indent=2, ensure_ascii=False))

    return 0


def cmd_prepare_one(args: argparse.Namespace) -> int:
    cfg = Config.from_args(args)
    cfg.ensure_dirs()

    base = args.base

    statement_file = cfg.statement_dir / f"{base}.statement.lean"
    proof_file = cfg.proof_dir / f"{base}.proof.lean"
    source_file = cfg.audit_dir / f"{base}.lean"
    map_file = cfg.source_map_dir / f"{base}.map.json"

    if not statement_file.exists():
        eprint(f"ERROR: statement file not found: {statement_file}")
        return 2

    if not proof_file.exists():
        eprint(f"ERROR: proof file not found: {proof_file}")
        return 2

    deps, dep_binders = parse_dep_items(args.dep or [])
    dep_names = list(dep_binders.keys())
    def_params = parse_def_param_items(args.def_param or [])
    replacements = parse_replace_items(args.replace or [])

    raw_statement = read_text(statement_file)
    raw_proof = read_text(proof_file)

    statement_text = prepare_text(
        raw_statement,
        deps=deps,
        dep_names=dep_names,
        dep_binders=dep_binders,
        def_params=def_params,
        replacements=replacements,
        mathlib_import=cfg.mathlib_import,
        make_statement=True,
        ascii_mode=args.ascii,
    )

    proof_text = prepare_text(
        raw_proof,
        deps=deps,
        dep_names=dep_names,
        dep_binders=dep_binders,
        def_params=def_params,
        replacements=replacements,
        mathlib_import=cfg.mathlib_import,
        make_statement=False,
        ascii_mode=args.ascii,
    )

    if not args.dry_run:
        write_text(statement_file, statement_text)
        write_text(proof_file, proof_text)

    map_data = build_map(
        base=base,
        source_file=source_file if source_file.exists() else None,
        statement_file=statement_file,
        proof_file=proof_file,
        map_file=map_file,
        deps=deps,
        def_params=def_params,
        replacements=replacements,
        statement_text=statement_text,
        proof_text=proof_text,
        cfg=cfg,
    )

    if not args.dry_run:
        write_json(map_file, map_data)

    result = {
        "prepared": True,
        "dry_run": args.dry_run,
        "base": base,
        "statement_file": relpath_or_str(statement_file, cfg.root),
        "proof_file": relpath_or_str(proof_file, cfg.root),
        "map_file": relpath_or_str(map_file, cfg.root),
        "statement_imports": source_imports(statement_text),
        "proof_imports": source_imports(proof_text),
        "statement_theorems": theorem_names(statement_text),
        "proof_theorems": theorem_names(proof_text),
        "statement_non_ascii": non_ascii_chars(statement_text),
        "proof_non_ascii": non_ascii_chars(proof_text),
        "proof_contains_sorry_or_admit": contains_sorry_or_admit(proof_text),
        "abstracted_dependencies": deps,
        "def_params": def_params,
        "replacements": [{"from": a, "to": b} for a, b in replacements],
    }

    print(json.dumps(result, indent=2, ensure_ascii=False))
    return 0


def cmd_check_one(args: argparse.Namespace) -> int:
    cfg = Config.from_args(args)

    base = args.base
    statement_file = cfg.statement_dir / f"{base}.statement.lean"
    proof_file = cfg.proof_dir / f"{base}.proof.lean"
    map_file = cfg.source_map_dir / f"{base}.map.json"

    errors: List[str] = []
    warnings: List[str] = []

    if not statement_file.exists():
        errors.append(f"missing_statement:{statement_file}")

    if not proof_file.exists():
        errors.append(f"missing_proof:{proof_file}")

    statement_text = read_text(statement_file) if statement_file.exists() else ""
    proof_text = read_text(proof_file) if proof_file.exists() else ""

    if statement_text and source_imports(statement_text) != [cfg.mathlib_import]:
        warnings.append("statement_imports_are_not_exactly_mathlib")

    if proof_text and source_imports(proof_text) != [cfg.mathlib_import]:
        warnings.append("proof_imports_are_not_exactly_mathlib")

    if proof_text and contains_sorry_or_admit(proof_text):
        errors.append("proof_contains_sorry_or_admit")

    st_theorems = theorem_names(statement_text)
    pr_theorems = theorem_names(proof_text)

    missing_in_proof = sorted(set(st_theorems) - set(pr_theorems))
    missing_in_statement = sorted(set(pr_theorems) - set(st_theorems))

    if missing_in_proof:
        errors.append("theorems_missing_in_proof")

    if missing_in_statement:
        errors.append("theorems_missing_in_statement")

    st_non_ascii = non_ascii_chars(statement_text)
    pr_non_ascii = non_ascii_chars(proof_text)

    if st_non_ascii:
        warnings.append("statement_contains_non_ascii")

    if pr_non_ascii:
        warnings.append("proof_contains_non_ascii")

    result = {
        "okay": len(errors) == 0,
        "errors": errors,
        "warnings": warnings,
        "statement_file": relpath_or_str(statement_file, cfg.root),
        "proof_file": relpath_or_str(proof_file, cfg.root),
        "map_file": relpath_or_str(map_file, cfg.root),
        "map_exists": map_file.exists(),
        "statement_imports": source_imports(statement_text),
        "proof_imports": source_imports(proof_text),
        "statement_theorems": st_theorems,
        "proof_theorems": pr_theorems,
        "missing_in_proof": missing_in_proof,
        "missing_in_statement": missing_in_statement,
        "statement_non_ascii": st_non_ascii,
        "proof_non_ascii": pr_non_ascii,
    }

    print(json.dumps(result, indent=2, ensure_ascii=False))
    return 0 if result["okay"] else 2


def cmd_status(args: argparse.Namespace) -> int:
    cfg = Config.from_args(args)

    rows: List[Dict[str, Any]] = []

    for statement_file in sorted(cfg.statement_dir.glob("*.statement.lean")):
        base = statement_file.name.removesuffix(".statement.lean")
        proof_file = cfg.proof_dir / f"{base}.proof.lean"
        map_file = cfg.source_map_dir / f"{base}.map.json"

        statement_text = read_text(statement_file)
        proof_text = read_text(proof_file) if proof_file.exists() else ""

        errors: List[str] = []
        if not proof_file.exists():
            errors.append("missing_proof")
        if proof_text and contains_sorry_or_admit(proof_text):
            errors.append("proof_contains_sorry_or_admit")

        rows.append({
            "base": base,
            "statement_file": relpath_or_str(statement_file, cfg.root),
            "proof_file": relpath_or_str(proof_file, cfg.root),
            "map_file": relpath_or_str(map_file, cfg.root),
            "map_exists": map_file.exists(),
            "ready": len(errors) == 0,
            "errors": errors,
            "statement_theorems": theorem_names(statement_text),
            "proof_theorems": theorem_names(proof_text),
        })

    summary = {
        "count": len(rows),
        "ready_count": sum(1 for r in rows if r["ready"]),
        "not_ready_count": sum(1 for r in rows if not r["ready"]),
        "rows": rows,
    }

    print(json.dumps(summary, indent=2, ensure_ascii=False))
    return 0 if summary["not_ready_count"] == 0 else 2


# ---------------------------------------------------------------------------
# Parser
# ---------------------------------------------------------------------------

def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Rewrite existing Lean audit copies into AXLE-ready statement/proof files."
    )

    sub = parser.add_subparsers(dest="command", required=True)

    p_init = sub.add_parser("init", help="Create directories only.")
    add_common_args(p_init)
    p_init.set_defaults(func=cmd_init)

    p_prepare = sub.add_parser("prepare-one", help="Rewrite one existing statement/proof pair.")
    add_common_args(p_prepare)
    p_prepare.add_argument("--base", required=True)
    p_prepare.add_argument(
        "--dep",
        action="append",
        default=[],
        help="Lean binder, e.g. 'LehmerComposite : Nat -> Prop'. Repeatable.",
    )
    p_prepare.add_argument(
        "--def-param",
        action="append",
        default=[],
        help="Parameterize local def, e.g. 'AuditCaseACandidate=LehmerComposite'. Repeatable.",
    )
    p_prepare.add_argument(
        "--replace",
        action="append",
        default=[],
        help="Text replacement FROM=TO, e.g. 'Pivot.foo=foo'. Repeatable.",
    )
    p_prepare.add_argument(
        "--ascii",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="Normalize common Unicode symbols to ASCII.",
    )
    p_prepare.add_argument("--dry-run", action="store_true")
    p_prepare.set_defaults(func=cmd_prepare_one)

    p_check = sub.add_parser("check-one", help="Check one prepared pair.")
    add_common_args(p_check)
    p_check.add_argument("--base", required=True)
    p_check.set_defaults(func=cmd_check_one)

    p_status = sub.add_parser("status", help="Show status of all prepared pairs.")
    add_common_args(p_status)
    p_status.set_defaults(func=cmd_status)

    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)

    try:
        return args.func(args)
    except KeyboardInterrupt:
        eprint("Interrupted.")
        return 130
    except Exception as exc:
        eprint(f"ERROR: {type(exc).__name__}: {exc}")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())