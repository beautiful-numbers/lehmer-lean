#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
axle_manifest.py

Version réduite et ciblée.

Commandes gardées :
- generate      : reconstruit une liste simple de fichiers, en préservant les entrées existantes
- status        : affiche les stats du manifest
- list-empty    : liste les entrées sans deps/def_params/replacements
- show-entry    : affiche une entrée
- fill-deps     : remplit deps pour une entrée existante à partir de detected_imports/detected_symbols

Commandes supprimées :
- inférence globale generate --infer-deps
- force-infer
- scanning symbolique complet
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple


# ---------------------------------------------------------------------------
# IO
# ---------------------------------------------------------------------------

def eprint(*args: Any) -> None:
    print(*args, file=sys.stderr, flush=True)


def read_json(path: Path) -> Dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def write_json(path: Path, data: Dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(data, indent=2, ensure_ascii=False),
        encoding="utf-8",
        newline="\n",
    )


def relpath_or_str(path: Path, root: Path) -> str:
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
        manifest: Path,
        lake_exe: Path,
    ) -> None:
        self.root = root
        self.audit_dir = audit_dir
        self.axle_dir = axle_dir
        self.manifest = manifest
        self.lake_exe = lake_exe

    @staticmethod
    def from_args(args: argparse.Namespace) -> "Config":
        root = Path(args.root).resolve() if args.root else Path.cwd().resolve()

        audit_dir = Path(args.audit_dir).resolve() if args.audit_dir else (
            root / "Lean" / "Lehmer" / "Audit"
        )

        axle_dir = Path(args.axle_dir).resolve() if args.axle_dir else (
            root / "Lean" / "Lehmer" / "Audit-axle"
        )

        manifest = Path(args.manifest).resolve() if args.manifest else (
            axle_dir / "axle-manifest.json"
        )

        lake_exe = Path(args.lake_exe).resolve() if args.lake_exe else (
            Path.home() / ".elan" / "bin" / "lake.exe"
        )

        return Config(
            root=root,
            audit_dir=audit_dir,
            axle_dir=axle_dir,
            manifest=manifest,
            lake_exe=lake_exe,
        )


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

IMPORT_RE = re.compile(r"(?m)^\s*import\s+([A-Za-z0-9_.]+)\s*$")

UNICODE_REPLACEMENTS = {
    "ℕ": "Nat",
    "→": "->",
    "∀": "forall",
    "∃": "Exists",
    "¬": "Not",
    "∧": "/\\",
    "∨": "\\/",
    "≤": "<=",
    "≥": ">=",
    "≠": "!=",
}

SKIP_SYMBOLS: Set[str] = {
    "String",
    "Repr",
    "DecidableEq",
    "Classical.choose",
    "Classical.choose_spec",
    "False.elim",
    "Or.inl",
    "Or.inr",
    "Eq.trans",
    "HEq",
    "HEq.rfl",
    "Nat.succ",
    "Nat.le_of_lt",
    "Nat.lt_of_not_ge",
    "Nat.not_lt_of_ge",
    "Nonempty",
    "WellFounded",
    "by_cases",
    "le_rfl",
    "le_trans",
    "lt_of_le_of_lt",
    "noncomputable",
}

LEAN_KEYWORDS: Set[str] = {
    "by",
    "exact",
    "intro",
    "intros",
    "fun",
    "forall",
    "exists",
    "Exists",
    "match",
    "with",
    "cases",
    "rcases",
    "simp",
    "simpa",
    "rw",
    "rfl",
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "instance",
    "structure",
    "class",
    "inductive",
    "namespace",
    "end",
    "open",
    "import",
    "where",
    "let",
    "have",
    "show",
    "calc",
    "from",
    "if",
    "then",
    "else",
    "Type",
    "Prop",
    "Sort",
    "Nat",
    "Int",
    "Bool",
    "True",
    "False",
    "And",
    "Or",
    "Not",
    "Iff",
    "Set",
    "List",
    "Option",
    "none",
    "some",
    "Unit",
    "PUnit",
    "Subtype",
    "Decidable",
    "Classical",
    "Mathlib",
}


# ---------------------------------------------------------------------------
# Manifest basics
# ---------------------------------------------------------------------------

def base_from_lean_file(path: Path, audit_dir: Path) -> str:
    return path.resolve().relative_to(audit_dir.resolve()).with_suffix("").as_posix()


def scan_audit_bases(cfg: Config) -> List[str]:
    if not cfg.audit_dir.exists():
        raise FileNotFoundError(f"audit_dir does not exist: {cfg.audit_dir}")

    return [
        base_from_lean_file(path, cfg.audit_dir)
        for path in sorted(cfg.audit_dir.rglob("*.lean"))
    ]


def empty_active_entry(base: str) -> Dict[str, Any]:
    return {
        "base": base,
        "status": "active",
        "deps": [],
        "def_params": [],
        "replacements": [],
        "detected_imports": [],
        "detected_symbols": [],
        "checked_dependencies": [],
        "notes": "No external dependency inferred; batch will try deps=[]",
    }


def normalize_entry(entry: Dict[str, Any]) -> Dict[str, Any]:
    out = dict(entry)

    base = out.get("base")
    if not isinstance(base, str) or not base.strip():
        raise ValueError(f"invalid manifest entry without base: {entry}")

    out["base"] = base.strip()
    out.setdefault("status", "active")
    out.setdefault("deps", [])
    out.setdefault("def_params", [])
    out.setdefault("replacements", [])
    out.setdefault("detected_imports", [])
    out.setdefault("detected_symbols", [])
    out.setdefault("checked_dependencies", [])

    if out.get("skip") is True:
        out["status"] = "skipped"
        out.pop("skip", None)

    return out


def load_manifest_entries(path: Path) -> Dict[str, Dict[str, Any]]:
    if not path.exists():
        return {}

    data = read_json(path)
    files = data.get("files", [])

    if not isinstance(files, list):
        raise ValueError("manifest must contain top-level field: files")

    out: Dict[str, Dict[str, Any]] = {}

    for item in files:
        if isinstance(item, dict) and item.get("base"):
            normalized = normalize_entry(item)
            out[normalized["base"]] = normalized

    return out


def find_manifest_entry(data: Dict[str, Any], base: str) -> Optional[Dict[str, Any]]:
    files = data.get("files", [])

    if not isinstance(files, list):
        return None

    for item in files:
        if isinstance(item, dict) and item.get("base") == base:
            return item

    return None


def stats(data: Dict[str, Any]) -> Dict[str, Any]:
    files = data.get("files", [])

    counts: Dict[str, int] = {}
    buckets: Dict[str, List[str]] = {}

    for item in files:
        if not isinstance(item, dict):
            continue

        base = item.get("base")
        status = item.get("status", "active")

        counts[status] = counts.get(status, 0) + 1
        buckets.setdefault(status, []).append(base)

    return {
        "files": len(files),
        "by_status": counts,
        "bases_by_status": buckets,
    }


# ---------------------------------------------------------------------------
# Lean helpers
# ---------------------------------------------------------------------------

def normalize_ascii_type(text: str) -> str:
    out = text
    for a, b in UNICODE_REPLACEMENTS.items():
        out = out.replace(a, b)
    out = re.sub(r"\s+", " ", out).strip()
    return out


def run_command(cmd: Sequence[str], *, cwd: Path, timeout_seconds: int) -> Dict[str, Any]:
    env = os.environ.copy()
    env["PYTHONUTF8"] = "1"
    env["PYTHONIOENCODING"] = "utf-8"

    try:
        proc = subprocess.run(
            list(cmd),
            cwd=str(cwd),
            text=True,
            encoding="utf-8",
            errors="replace",
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout_seconds,
            shell=False,
            env=env,
        )

        return {
            "returncode": proc.returncode,
            "stdout": proc.stdout,
            "stderr": proc.stderr,
            "command": list(cmd),
        }

    except subprocess.TimeoutExpired as exc:
        return {
            "returncode": 124,
            "stdout": exc.stdout or "",
            "stderr": exc.stderr or "",
            "command": list(cmd),
            "error": f"timeout_after_{timeout_seconds}_seconds",
        }


def parse_check_message(msg: str) -> Optional[Tuple[str, str]]:
    msg = msg.strip()
    msg = re.sub(r"\s+", " ", msg)

    if not msg:
        return None

    msg = re.sub(r"^(?:info|information):\s*", "", msg).strip()

    if " : " not in msg:
        return None

    name, typ = msg.split(" : ", 1)
    name = name.strip()
    typ = typ.strip()

    if not name or not typ:
        return None

    if not re.match(r"^[A-Za-z_][A-Za-z0-9_'.]*$", name):
        return None

    return name, normalize_ascii_type(typ)


def parse_lean_check_output(
    output: str,
    *,
    line_to_symbol: Dict[int, str],
) -> Dict[str, str]:
    result: Dict[str, str] = {}

    current_line: Optional[int] = None
    current_msg: List[str] = []

    line_re = re.compile(
        r"^.*?:(?P<line>\d+):(?P<col>\d+):\s+"
        r"(?:info|information):\s*(?P<msg>.*)$"
    )

    def flush() -> None:
        nonlocal current_line, current_msg

        if current_line is None:
            return

        requested = line_to_symbol.get(current_line)
        msg = "\n".join(current_msg).strip()

        if requested:
            parsed = parse_check_message(msg)
            if parsed is not None:
                printed_name, typ = parsed

                requested_short = requested.split(".")[-1]
                printed_short = printed_name.split(".")[-1]

                if requested_short == printed_short or requested == printed_name:
                    result[printed_name] = typ

        current_line = None
        current_msg = []

    for raw in output.splitlines():
        line = raw.rstrip()
        m = line_re.match(line)

        if m:
            flush()
            current_line = int(m.group("line"))
            current_msg = [m.group("msg")]
            continue

        if current_line is not None:
            current_msg.append(line)

    flush()
    return result


def build_check_file(
    *,
    imports: Sequence[str],
    symbols: Sequence[str],
) -> Tuple[str, Dict[int, str]]:
    lines: List[str] = []
    line_to_symbol: Dict[int, str] = {}

    clean_imports = [imp.strip() for imp in imports if isinstance(imp, str) and imp.strip()]

    if clean_imports:
        for imp in clean_imports:
            lines.append(f"import {imp}")
    else:
        lines.append("import Mathlib")

    lines.extend([
        "",
        "set_option autoImplicit true",
        "set_option pp.universes false",
        "set_option pp.all false",
        "",
        "namespace Lehmer",
        "namespace Audit",
        "",
        "open Lehmer.Basic",
        "open Lehmer.Pipeline",
        "",
    ])

    for sym in symbols:
        lines.append(f"#check {sym}")
        line_to_symbol[len(lines)] = sym

    lines.extend([
        "",
        "end Audit",
        "end Lehmer",
        "",
    ])

    return "\n".join(lines), line_to_symbol


def lean_check_symbols(
    *,
    imports: Sequence[str],
    symbols: Sequence[str],
    cfg: Config,
    timeout_seconds: int,
    chunk_size: int,
) -> Dict[str, str]:
    checked: Dict[str, str] = {}

    clean_symbols = [s for s in symbols if isinstance(s, str) and s.strip() and not s.startswith(".")]

    for start in range(0, len(clean_symbols), chunk_size):
        chunk = clean_symbols[start:start + chunk_size]

        content, line_to_symbol = build_check_file(
            imports=imports,
            symbols=chunk,
        )

        with tempfile.TemporaryDirectory(prefix="axle_manifest_") as tmp:
            tmp_path = Path(tmp) / "Check.lean"
            tmp_path.write_text(content, encoding="utf-8", newline="\n")

            result = run_command(
                [str(cfg.lake_exe), "env", "lean", str(tmp_path)],
                cwd=cfg.root,
                timeout_seconds=timeout_seconds,
            )

            combined = f"{result.get('stdout', '')}\n{result.get('stderr', '')}"
            parsed = parse_lean_check_output(combined, line_to_symbol=line_to_symbol)
            checked.update(parsed)

    return checked


# ---------------------------------------------------------------------------
# fill-deps logic
# ---------------------------------------------------------------------------

def is_local_projection(sym: str) -> bool:
    if "." not in sym:
        return False

    parts = sym.split(".")
    first = parts[0]

    if not first:
        return True

    if first.startswith("h") and len(first) <= 4:
        return True

    if first in {
        "A", "B", "C", "D", "E", "F", "G", "I", "K", "N", "O", "P", "R",
        "T", "U", "X",
    }:
        return True

    if first in {
        "input",
        "closureInput",
        "gapToClosure",
        "terminal",
        "closure",
        "package",
        "routing",
        "data",
        "nonIntegrality",
        "branch",
    }:
        return True

    if any(part.isdigit() for part in parts):
        return True

    return False


def is_module_symbol(sym: str, detected_imports: Sequence[str]) -> bool:
    if sym in detected_imports:
        return True

    if sym.startswith("Lehmer."):
        final = sym.split(".")[-1]

        # Module-like names often have final component uppercase and no underscore.
        # Keep names with underscores because they are often theorem names.
        if final and final[0].isupper() and "_" not in final:
            return True

    return False


def filter_symbols(
    detected_symbols: Sequence[Any],
    detected_imports: Sequence[Any],
    *,
    max_candidates: int,
) -> List[str]:
    imports = [x for x in detected_imports if isinstance(x, str)]

    out: List[str] = []
    seen: Set[str] = set()

    for raw in detected_symbols:
        if not isinstance(raw, str):
            continue

        sym = raw.strip()

        if not sym:
            continue

        if sym in seen:
            continue

        if sym in SKIP_SYMBOLS or sym in LEAN_KEYWORDS:
            continue

        if sym.startswith("."):
            continue

        if is_local_projection(sym):
            continue

        if is_module_symbol(sym, imports):
            continue

        if not re.match(r"^[A-Za-z_][A-Za-z0-9_'.]*$", sym):
            continue

        out.append(sym)
        seen.add(sym)

        if max_candidates > 0 and len(out) >= max_candidates:
            break

    return out


def namespace_prefixes_from_imports(detected_imports: Sequence[Any]) -> List[str]:
    prefixes: List[str] = []
    seen: Set[str] = set()

    def add(prefix: str) -> None:
        prefix = prefix.strip().strip(".")
        if not prefix:
            return
        if prefix in seen:
            return
        prefixes.append(prefix)
        seen.add(prefix)

    for prefix in [
        "Lehmer.Basic",
        "Lehmer.Pipeline",
        "Lehmer.Audit",
        "Lehmer.Pivot",
        "Lehmer.CaseB",
        "Lehmer.CaseC",
    ]:
        add(prefix)

    for raw in detected_imports:
        if not isinstance(raw, str):
            continue

        imp = raw.strip()
        if not imp.startswith("Lehmer."):
            continue

        parts = imp.split(".")

        for end in range(len(parts), 1, -1):
            add(".".join(parts[:end]))

    return prefixes


def expand_symbols(symbols: Sequence[str], detected_imports: Sequence[Any]) -> List[str]:
    prefixes = namespace_prefixes_from_imports(detected_imports)

    expanded: List[str] = []
    seen: Set[str] = set()

    def add(sym: str) -> None:
        if not sym:
            return
        if sym in seen:
            return
        expanded.append(sym)
        seen.add(sym)

    for sym in symbols:
        add(sym)

        if "." in sym:
            continue

        for prefix in prefixes:
            add(f"{prefix}.{sym}")

    return expanded


def dep_name_for_symbol(symbol: str) -> str:
    return symbol.split(".")[-1]


def make_deps_and_replacements(
    checked: Dict[str, str],
    *,
    max_deps: int,
) -> Tuple[List[str], List[str], List[Dict[str, str]]]:
    deps: List[str] = []
    replacements: List[str] = []
    rows: List[Dict[str, str]] = []

    used_dep_names: Set[str] = set()

    for symbol in sorted(checked):
        typ = checked[symbol]
        dep_name = dep_name_for_symbol(symbol)

        if dep_name in used_dep_names:
            dep_name = symbol.replace(".", "_")

        used_dep_names.add(dep_name)

        deps.append(f"{dep_name} : {typ}")

        if "." in symbol:
            replacements.append(f"{symbol}={dep_name}")

        rows.append({
            "symbol": symbol,
            "dep_name": dep_name,
            "type": typ,
        })

        if len(deps) >= max_deps:
            break

    return deps, replacements, rows


def merge_string_lists(a: Sequence[Any], b: Sequence[Any]) -> List[str]:
    out: List[str] = []
    seen: Set[str] = set()

    for raw in list(a) + list(b):
        if not isinstance(raw, str):
            continue

        value = raw.strip()

        if not value:
            continue

        if value in seen:
            continue

        out.append(value)
        seen.add(value)

    return out


# ---------------------------------------------------------------------------
# Commands
# ---------------------------------------------------------------------------

def cmd_generate(args: argparse.Namespace) -> int:
    cfg = Config.from_args(args)

    bases = scan_audit_bases(cfg)
    existing = load_manifest_entries(cfg.manifest)

    files: List[Dict[str, Any]] = []

    for base in bases:
        if base in existing:
            files.append(normalize_entry(existing[base]))
        else:
            files.append(empty_active_entry(base))

    data = {"files": files}

    if not args.dry_run:
        write_json(cfg.manifest, data)

    print(json.dumps({
        "generated": True,
        "dry_run": args.dry_run,
        "audit_dir": relpath_or_str(cfg.audit_dir, cfg.root),
        "manifest": relpath_or_str(cfg.manifest, cfg.root),
        "stats": stats(data),
    }, indent=2, ensure_ascii=False))

    return 0


def cmd_status(args: argparse.Namespace) -> int:
    cfg = Config.from_args(args)

    if not cfg.manifest.exists():
        eprint(f"ERROR: manifest not found: {cfg.manifest}")
        return 2

    data = read_json(cfg.manifest)

    print(json.dumps({
        "manifest": relpath_or_str(cfg.manifest, cfg.root),
        "stats": stats(data),
    }, indent=2, ensure_ascii=False))

    return 0


def cmd_list_empty(args: argparse.Namespace) -> int:
    cfg = Config.from_args(args)

    if not cfg.manifest.exists():
        eprint(f"ERROR: manifest not found: {cfg.manifest}")
        return 2

    data = read_json(cfg.manifest)
    files = data.get("files", [])

    rows: List[Dict[str, Any]] = []

    for item in files:
        if not isinstance(item, dict):
            continue

        status = item.get("status", "active")

        if status == "skipped":
            continue

        if not item.get("deps") and not item.get("def_params") and not item.get("replacements"):
            rows.append({
                "base": item.get("base"),
                "status": status,
                "notes": item.get("notes", ""),
            })

    print(json.dumps({
        "empty_entries": len(rows),
        "rows": rows,
    }, indent=2, ensure_ascii=False))

    return 0


def cmd_show_entry(args: argparse.Namespace) -> int:
    cfg = Config.from_args(args)

    if not cfg.manifest.exists():
        eprint(f"ERROR: manifest not found: {cfg.manifest}")
        return 2

    data = read_json(cfg.manifest)
    entry = find_manifest_entry(data, args.base)

    if entry is None:
        eprint(f"ERROR: base not found in manifest: {args.base}")
        return 2

    print(json.dumps(entry, indent=2, ensure_ascii=False))
    return 0


def cmd_fill_deps(args: argparse.Namespace) -> int:
    cfg = Config.from_args(args)

    if not cfg.manifest.exists():
        eprint(f"ERROR: manifest not found: {cfg.manifest}")
        return 2

    data = read_json(cfg.manifest)
    entry = find_manifest_entry(data, args.base)

    if entry is None:
        eprint(f"ERROR: base not found in manifest: {args.base}")
        return 2

    detected_imports = entry.get("detected_imports", [])
    detected_symbols = entry.get("detected_symbols", [])

    if not isinstance(detected_imports, list):
        detected_imports = []

    if not isinstance(detected_symbols, list):
        detected_symbols = []

    symbols = filter_symbols(
        detected_symbols,
        detected_imports,
        max_candidates=args.max_candidates,
    )

    probe_symbols = expand_symbols(symbols, detected_imports)

    checked = lean_check_symbols(
        imports=[x for x in detected_imports if isinstance(x, str)],
        symbols=probe_symbols,
        cfg=cfg,
        timeout_seconds=args.timeout_seconds,
        chunk_size=args.chunk_size,
    )

    deps, inferred_replacements, dep_rows = make_deps_and_replacements(
        checked,
        max_deps=args.max_deps,
    )

    existing_replacements = entry.get("replacements", [])
    if not isinstance(existing_replacements, list):
        existing_replacements = []

    replacements = merge_string_lists(existing_replacements, inferred_replacements)

    entry["deps"] = deps
    entry.setdefault("def_params", [])
    entry["replacements"] = replacements
    entry["checked_dependencies"] = dep_rows

    if deps or replacements:
        entry["status"] = "needs_review"
        entry["notes"] = (
            "Deps inferred from existing detected_symbols with local Lean #check; "
            "review before batch."
        )
    else:
        entry["status"] = "active"
        entry["notes"] = "No deps found by fill-deps."

    write_json(cfg.manifest, data)

    print(json.dumps({
        "base": args.base,
        "filled": True,
        "checked_symbols": len(symbols),
        "probe_symbols": len(probe_symbols),
        "checked_dependencies": len(dep_rows),
        "deps": len(deps),
        "new_replacements": len(inferred_replacements),
        "total_replacements": len(replacements),
        "status": entry.get("status"),
        "manifest": relpath_or_str(cfg.manifest, cfg.root),
    }, indent=2, ensure_ascii=False))

    return 0


# ---------------------------------------------------------------------------
# Parser
# ---------------------------------------------------------------------------

def add_common_args(p: argparse.ArgumentParser) -> None:
    p.add_argument("--root", help="Project root. Default: current directory.")
    p.add_argument("--audit-dir", help="Audit source directory.")
    p.add_argument("--axle-dir", help="Audit-axle directory.")
    p.add_argument("--manifest", help="Path to axle-manifest.json.")
    p.add_argument("--lake-exe", help="Path to lake.exe.")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Reduced AXLE manifest helper."
    )

    sub = parser.add_subparsers(dest="command", required=True)

    p_generate = sub.add_parser("generate", help="Scan audit_dir and update manifest, preserving existing entries.")
    add_common_args(p_generate)
    p_generate.add_argument("--dry-run", action="store_true")
    p_generate.set_defaults(func=cmd_generate)

    p_status = sub.add_parser("status", help="Show manifest status.")
    add_common_args(p_status)
    p_status.set_defaults(func=cmd_status)

    p_empty = sub.add_parser("list-empty", help="List entries with empty deps/def_params/replacements.")
    add_common_args(p_empty)
    p_empty.set_defaults(func=cmd_list_empty)

    p_show = sub.add_parser("show-entry", help="Show one manifest entry.")
    add_common_args(p_show)
    p_show.add_argument("--base", required=True)
    p_show.set_defaults(func=cmd_show_entry)

    p_fill = sub.add_parser("fill-deps", help="Fill deps for one existing manifest entry.")
    add_common_args(p_fill)
    p_fill.add_argument("--base", required=True)
    p_fill.add_argument("--timeout-seconds", type=int, default=120)
    p_fill.add_argument("--chunk-size", type=int, default=30)
    p_fill.add_argument("--max-candidates", type=int, default=120)
    p_fill.add_argument("--max-deps", type=int, default=80)
    p_fill.set_defaults(func=cmd_fill_deps)

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