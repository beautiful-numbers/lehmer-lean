#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
axle_go.py

Run AXLE verification through the AXLE HTTP API, save certificates,
update source maps, and check certificate validity.

This script DOES:
- read AXLE-ready statement/proof files
- call AXLE verify_proof API
- save certificate JSON files
- update/create source-map JSON files
- check existing certificates without calling AXLE

This script DOES NOT:
- transform Lean files
- edit statement/proof files
- call `axle verify-proof` CLI

Expected structure:

Lean/Lehmer/Audit-axle/
  Audit_statement/
    CaseAClosure.statement.lean
  Audit_proof/
    CaseAClosure.proof.lean
  source-map/
    CaseAClosure.map.json
  certificate/
    CaseAClosure.axle.json
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import sys
import time
import urllib.error
import urllib.request
from typing import Any, Dict, List, Optional, Sequence, Tuple


# ---------------------------------------------------------------------------
# IO
# ---------------------------------------------------------------------------

def eprint(*args: Any) -> None:
    print(*args, file=sys.stderr)


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def write_json(path: Path, data: Dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(data, indent=2, ensure_ascii=False),
        encoding="utf-8",
        newline="\n",
    )


def load_json(path: Path) -> Dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def relpath_or_str(path: Optional[Path], root: Path) -> Optional[str]:
    if path is None:
        return None
    try:
        return path.resolve().relative_to(root.resolve()).as_posix()
    except ValueError:
        return path.resolve().as_posix()


def now_unix_ms() -> int:
    return int(time.time() * 1000)


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
        certificate_dir: Path,
        environment: str,
        api_url: str,
        api_key_env: str,
        timeout_seconds: int,
        ignore_imports: bool,
        use_def_eq: bool,
        permitted_sorries: List[str],
    ) -> None:
        self.root = root
        self.audit_dir = audit_dir
        self.axle_dir = axle_dir
        self.statement_dir = statement_dir
        self.proof_dir = proof_dir
        self.source_map_dir = source_map_dir
        self.certificate_dir = certificate_dir
        self.environment = environment
        self.api_url = api_url
        self.api_key_env = api_key_env
        self.timeout_seconds = timeout_seconds
        self.ignore_imports = ignore_imports
        self.use_def_eq = use_def_eq
        self.permitted_sorries = permitted_sorries

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

        certificate_dir = Path(args.certificate_dir).resolve() if args.certificate_dir else (
            axle_dir / "certificate"
        )

        return Config(
            root=root,
            audit_dir=audit_dir,
            axle_dir=axle_dir,
            statement_dir=statement_dir,
            proof_dir=proof_dir,
            source_map_dir=source_map_dir,
            certificate_dir=certificate_dir,
            environment=args.environment,
            api_url=args.api_url,
            api_key_env=args.api_key_env,
            timeout_seconds=args.timeout_seconds,
            ignore_imports=args.ignore_imports,
            use_def_eq=args.use_def_eq,
            permitted_sorries=args.permitted_sorries or [],
        )

    def ensure_dirs(self) -> None:
        self.source_map_dir.mkdir(parents=True, exist_ok=True)
        self.certificate_dir.mkdir(parents=True, exist_ok=True)


def add_common_args(p: argparse.ArgumentParser) -> None:
    p.add_argument("--root", help="Project root. Default: current directory.")
    p.add_argument("--audit-dir", help="Original audit directory.")
    p.add_argument("--axle-dir", help="Audit-axle root directory.")
    p.add_argument("--statement-dir", help="Directory of *.statement.lean files.")
    p.add_argument("--proof-dir", help="Directory of *.proof.lean files.")
    p.add_argument("--source-map-dir", help="Directory of *.map.json files.")
    p.add_argument("--certificate-dir", help="Directory of *.axle.json files.")

    p.add_argument("--environment", default="lean-4.28.0")
    p.add_argument("--api-url", default="https://axle.axiommath.ai/api/v1/verify_proof")
    p.add_argument("--api-key-env", default="AXLE_API_KEY")
    p.add_argument("--timeout-seconds", type=int, default=180)

    p.add_argument("--ignore-imports", action="store_true")
    p.add_argument("--use-def-eq", action="store_true")
    p.add_argument("--permitted-sorries", nargs="*", default=[])


# ---------------------------------------------------------------------------
# Lean helpers
# ---------------------------------------------------------------------------

THEOREM_RE = re.compile(
    r"(?m)^\s*(?:@\[[^\]]+\]\s*)*(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'.]*)"
)

IMPORT_RE = re.compile(r"(?m)^\s*import\s+([A-Za-z0-9_.]+)\s*$")


def theorem_names(text: str) -> List[str]:
    return [m.group(1) for m in THEOREM_RE.finditer(text)]


def imports(text: str) -> List[str]:
    return [m.group(1) for m in IMPORT_RE.finditer(text)]


def contains_sorry_or_admit(text: str) -> bool:
    return bool(re.search(r"\b(sorry|admit)\b", text))


def non_ascii_chars(text: str, limit: int = 30) -> List[Dict[str, Any]]:
    found: List[Dict[str, Any]] = []
    for i, ch in enumerate(text):
        if ord(ch) > 127:
            found.append({
                "index": i,
                "char": ch,
                "codepoint": f"U+{ord(ch):04X}",
            })
            if len(found) >= limit:
                break
    return found


# ---------------------------------------------------------------------------
# Path helpers
# ---------------------------------------------------------------------------

def base_from_statement(path: Path) -> str:
    name = path.name
    if not name.endswith(".statement.lean"):
        raise ValueError(f"Statement file must end with .statement.lean: {path}")
    return name[:-len(".statement.lean")]


def base_from_proof(path: Path) -> str:
    name = path.name
    if not name.endswith(".proof.lean"):
        raise ValueError(f"Proof file must end with .proof.lean: {path}")
    return name[:-len(".proof.lean")]


def paths_for_base(base: str, cfg: Config) -> Tuple[Path, Path, Path, Path, Optional[Path]]:
    statement = cfg.statement_dir / f"{base}.statement.lean"
    proof = cfg.proof_dir / f"{base}.proof.lean"
    source_map = cfg.source_map_dir / f"{base}.map.json"
    certificate = cfg.certificate_dir / f"{base}.axle.json"

    source = cfg.audit_dir / f"{base}.lean"
    if not source.exists():
        source = None

    return statement, proof, source_map, certificate, source


# ---------------------------------------------------------------------------
# Precheck
# ---------------------------------------------------------------------------

def precheck_pair(statement_path: Path, proof_path: Path) -> Dict[str, Any]:
    errors: List[str] = []
    warnings: List[str] = []

    if not statement_path.exists():
        errors.append(f"missing_statement:{statement_path}")

    if not proof_path.exists():
        errors.append(f"missing_proof:{proof_path}")

    statement_text = read_text(statement_path) if statement_path.exists() else ""
    proof_text = read_text(proof_path) if proof_path.exists() else ""

    if statement_text:
        statement_imports = imports(statement_text)
        if statement_imports != ["Mathlib"]:
            warnings.append("statement_imports_not_exactly_mathlib")
    else:
        statement_imports = []

    if proof_text:
        proof_imports = imports(proof_text)
        if proof_imports != ["Mathlib"]:
            warnings.append("proof_imports_not_exactly_mathlib")
    else:
        proof_imports = []

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

    statement_non_ascii = non_ascii_chars(statement_text)
    proof_non_ascii = non_ascii_chars(proof_text)

    if statement_non_ascii:
        warnings.append("statement_contains_non_ascii")

    if proof_non_ascii:
        warnings.append("proof_contains_non_ascii")

    return {
        "okay": len(errors) == 0,
        "errors": errors,
        "warnings": warnings,
        "statement_imports": statement_imports,
        "proof_imports": proof_imports,
        "statement_theorems": st_theorems,
        "proof_theorems": pr_theorems,
        "missing_in_proof": missing_in_proof,
        "missing_in_statement": missing_in_statement,
        "statement_non_ascii": statement_non_ascii,
        "proof_non_ascii": proof_non_ascii,
    }


# ---------------------------------------------------------------------------
# AXLE API
# ---------------------------------------------------------------------------

def call_axle_api(
    *,
    statement_text: str,
    proof_text: str,
    cfg: Config,
) -> Dict[str, Any]:
    api_key = os.environ.get(cfg.api_key_env)

    if not api_key:
        return {
            "okay": False,
            "api_called": False,
            "error": f"missing_environment_variable:{cfg.api_key_env}",
            "failed_declarations": [],
        }

    payload = {
        "formal_statement": statement_text,
        "content": proof_text,
        "environment": cfg.environment,
        "ignore_imports": cfg.ignore_imports,
        "use_def_eq": cfg.use_def_eq,
        "permitted_sorries": cfg.permitted_sorries,
    }

    data = json.dumps(payload).encode("utf-8")

    request = urllib.request.Request(
        cfg.api_url,
        data=data,
        method="POST",
        headers={
            "Content-Type": "application/json",
            "Authorization": f"Bearer {api_key}",
        },
    )

    try:
        with urllib.request.urlopen(request, timeout=cfg.timeout_seconds) as response:
            raw = response.read().decode("utf-8", errors="replace")
            parsed = json.loads(raw)

            if isinstance(parsed, dict):
                parsed["api_called"] = True
                return parsed

            return {
                "okay": False,
                "api_called": True,
                "error": "api_response_not_json_object",
                "raw": parsed,
                "failed_declarations": [],
            }

    except urllib.error.HTTPError as exc:
        raw = exc.read().decode("utf-8", errors="replace")
        try:
            parsed_error = json.loads(raw)
        except json.JSONDecodeError:
            parsed_error = {"raw": raw}

        return {
            "okay": False,
            "api_called": True,
            "http_status": exc.code,
            "error": "http_error",
            "response": parsed_error,
            "failed_declarations": [],
        }

    except Exception as exc:
        return {
            "okay": False,
            "api_called": True,
            "error": f"{type(exc).__name__}: {exc}",
            "failed_declarations": [],
        }


# ---------------------------------------------------------------------------
# Certificate / source map
# ---------------------------------------------------------------------------

def extract_api_result(certificate: Dict[str, Any]) -> Dict[str, Any]:
    """
    Supports both:
    - wrapped certificate created by this script: {"result": {...}}
    - raw AXLE API output saved directly
    """
    result = certificate.get("result")
    if isinstance(result, dict):
        return result
    return certificate


def cert_is_okay(certificate: Dict[str, Any]) -> bool:
    result = extract_api_result(certificate)
    return (
        result.get("okay") is True
        and result.get("failed_declarations", []) == []
    )


def make_certificate(
    *,
    base: str,
    statement_path: Path,
    proof_path: Path,
    source_file: Optional[Path],
    source_map_path: Path,
    api_result: Dict[str, Any],
    precheck: Dict[str, Any],
    cfg: Config,
) -> Dict[str, Any]:
    return {
        "schema": "axle-certificate-v1",
        "created_unix_ms": now_unix_ms(),
        "base": base,
        "source_file": relpath_or_str(source_file, cfg.root) if source_file else None,
        "statement_file": relpath_or_str(statement_path, cfg.root),
        "proof_file": relpath_or_str(proof_path, cfg.root),
        "source_map_file": relpath_or_str(source_map_path, cfg.root),
        "environment": cfg.environment,
        "api_url": cfg.api_url,
        "precheck": precheck,
        "result": api_result,
        "valid_certificate": (
            api_result.get("okay") is True
            and api_result.get("failed_declarations", []) == []
        ),
    }


def make_or_update_source_map(
    *,
    base: str,
    statement_path: Path,
    proof_path: Path,
    source_file: Optional[Path],
    source_map_path: Path,
    certificate_path: Path,
    certificate: Dict[str, Any],
    statement_text: str,
    proof_text: str,
    cfg: Config,
) -> Dict[str, Any]:
    old: Dict[str, Any] = {}
    if source_map_path.exists():
        try:
            old = load_json(source_map_path)
        except Exception:
            old = {}

    statement_theorems = theorem_names(statement_text)
    proof_theorems = theorem_names(proof_text)

    old_theorems = old.get("theorems", [])
    old_theorem_by_name: Dict[str, Dict[str, Any]] = {}

    if isinstance(old_theorems, list):
        for row in old_theorems:
            if isinstance(row, dict):
                name = row.get("axle_name") or row.get("source_name")
                if isinstance(name, str):
                    old_theorem_by_name[name] = row

    theorem_rows: List[Dict[str, Any]] = []
    for name in sorted(set(statement_theorems) | set(proof_theorems)):
        previous = old_theorem_by_name.get(name, {})
        theorem_rows.append({
            **previous,
            "source_name": previous.get("source_name", name),
            "axle_name": previous.get("axle_name", name),
            "in_statement": name in statement_theorems,
            "in_proof": name in proof_theorems,
            "certificate_okay": cert_is_okay(certificate),
        })

    result = extract_api_result(certificate)

    source_map = {
        **old,
        "schema": "axle-source-map-v1",
        "updated_unix_ms": now_unix_ms(),
        "base": base,
        "source_file": relpath_or_str(source_file, cfg.root) if source_file else old.get("source_file"),
        "statement_file": relpath_or_str(statement_path, cfg.root),
        "proof_file": relpath_or_str(proof_path, cfg.root),
        "certificate_file": relpath_or_str(certificate_path, cfg.root),
        "environment": cfg.environment,
        "statement_imports": imports(statement_text),
        "proof_imports": imports(proof_text),
        "statement_theorems": statement_theorems,
        "proof_theorems": proof_theorems,
        "axle_okay": result.get("okay") is True,
        "failed_declarations": result.get("failed_declarations", []),
        "valid_certificate": cert_is_okay(certificate),
        "theorems": theorem_rows,
    }

    return source_map


# ---------------------------------------------------------------------------
# Commands
# ---------------------------------------------------------------------------

def cmd_verify_one(args: argparse.Namespace) -> int:
    cfg = Config.from_args(args)
    cfg.ensure_dirs()

    if args.base:
        base = args.base
        statement_path, proof_path, source_map_path, certificate_path, source_file = paths_for_base(base, cfg)
    else:
        if not args.statement or not args.proof:
            eprint("ERROR: use --base or both --statement and --proof")
            return 2

        statement_path = Path(args.statement).resolve()
        proof_path = Path(args.proof).resolve()
        base = base_from_statement(statement_path)
        source_map_path = Path(args.map_out).resolve() if args.map_out else cfg.source_map_dir / f"{base}.map.json"
        certificate_path = Path(args.certificate_out).resolve() if args.certificate_out else cfg.certificate_dir / f"{base}.axle.json"
        source_candidate = cfg.audit_dir / f"{base}.lean"
        source_file = source_candidate if source_candidate.exists() else None

    if args.map_out:
        source_map_path = Path(args.map_out).resolve()
    if args.certificate_out:
        certificate_path = Path(args.certificate_out).resolve()

    precheck = precheck_pair(statement_path, proof_path)

    if not precheck["okay"] and not args.no_precheck_fail:
        certificate = make_certificate(
            base=base,
            statement_path=statement_path,
            proof_path=proof_path,
            source_file=source_file,
            source_map_path=source_map_path,
            api_result={
                "okay": False,
                "api_called": False,
                "skipped": True,
                "reason": "precheck_failed",
                "failed_declarations": [],
            },
            precheck=precheck,
            cfg=cfg,
        )
        write_json(certificate_path, certificate)

        print(json.dumps({
            "okay": False,
            "api_called": False,
            "reason": "precheck_failed",
            "certificate_file": relpath_or_str(certificate_path, cfg.root),
            "precheck_errors": precheck["errors"],
            "precheck_warnings": precheck["warnings"],
        }, indent=2, ensure_ascii=False))
        return 2

    statement_text = read_text(statement_path)
    proof_text = read_text(proof_path)

    api_result = call_axle_api(
        statement_text=statement_text,
        proof_text=proof_text,
        cfg=cfg,
    )

    certificate = make_certificate(
        base=base,
        statement_path=statement_path,
        proof_path=proof_path,
        source_file=source_file,
        source_map_path=source_map_path,
        api_result=api_result,
        precheck=precheck,
        cfg=cfg,
    )

    write_json(certificate_path, certificate)

    source_map = make_or_update_source_map(
        base=base,
        statement_path=statement_path,
        proof_path=proof_path,
        source_file=source_file,
        source_map_path=source_map_path,
        certificate_path=certificate_path,
        certificate=certificate,
        statement_text=statement_text,
        proof_text=proof_text,
        cfg=cfg,
    )

    write_json(source_map_path, source_map)

    result = extract_api_result(certificate)

    print(json.dumps({
        "base": base,
        "okay": result.get("okay") is True,
        "valid_certificate": cert_is_okay(certificate),
        "failed_declarations": result.get("failed_declarations", []),
        "certificate_file": relpath_or_str(certificate_path, cfg.root),
        "source_map_file": relpath_or_str(source_map_path, cfg.root),
        "request_id": (
            result.get("info", {}).get("request_id")
            if isinstance(result.get("info"), dict)
            else None
        ),
    }, indent=2, ensure_ascii=False))

    return 0 if cert_is_okay(certificate) else 2


def cmd_verify_all(args: argparse.Namespace) -> int:
    cfg = Config.from_args(args)
    cfg.ensure_dirs()

    statements = sorted(cfg.statement_dir.glob(args.pattern))

    results: List[Dict[str, Any]] = []
    okay_count = 0
    fail_count = 0

    for statement_path in statements:
        if not statement_path.name.endswith(".statement.lean"):
            continue

        base = base_from_statement(statement_path)
        proof_path = cfg.proof_dir / f"{base}.proof.lean"
        source_map_path = cfg.source_map_dir / f"{base}.map.json"
        certificate_path = cfg.certificate_dir / f"{base}.axle.json"
        source_candidate = cfg.audit_dir / f"{base}.lean"
        source_file = source_candidate if source_candidate.exists() else None

        precheck = precheck_pair(statement_path, proof_path)

        if not precheck["okay"] and not args.no_precheck_fail:
            certificate = make_certificate(
                base=base,
                statement_path=statement_path,
                proof_path=proof_path,
                source_file=source_file,
                source_map_path=source_map_path,
                api_result={
                    "okay": False,
                    "api_called": False,
                    "skipped": True,
                    "reason": "precheck_failed",
                    "failed_declarations": [],
                },
                precheck=precheck,
                cfg=cfg,
            )
            write_json(certificate_path, certificate)

            fail_count += 1
            results.append({
                "base": base,
                "okay": False,
                "skipped": True,
                "reason": "precheck_failed",
                "errors": precheck["errors"],
                "certificate_file": relpath_or_str(certificate_path, cfg.root),
            })
            continue

        statement_text = read_text(statement_path)
        proof_text = read_text(proof_path)

        api_result = call_axle_api(
            statement_text=statement_text,
            proof_text=proof_text,
            cfg=cfg,
        )

        certificate = make_certificate(
            base=base,
            statement_path=statement_path,
            proof_path=proof_path,
            source_file=source_file,
            source_map_path=source_map_path,
            api_result=api_result,
            precheck=precheck,
            cfg=cfg,
        )

        write_json(certificate_path, certificate)

        source_map = make_or_update_source_map(
            base=base,
            statement_path=statement_path,
            proof_path=proof_path,
            source_file=source_file,
            source_map_path=source_map_path,
            certificate_path=certificate_path,
            certificate=certificate,
            statement_text=statement_text,
            proof_text=proof_text,
            cfg=cfg,
        )

        write_json(source_map_path, source_map)

        valid = cert_is_okay(certificate)
        if valid:
            okay_count += 1
        else:
            fail_count += 1

        result = extract_api_result(certificate)

        results.append({
            "base": base,
            "okay": result.get("okay") is True,
            "valid_certificate": valid,
            "failed_declarations": result.get("failed_declarations", []),
            "certificate_file": relpath_or_str(certificate_path, cfg.root),
            "source_map_file": relpath_or_str(source_map_path, cfg.root),
        })

        if args.stop_on_fail and not valid:
            break

    summary = {
        "schema": "axle-batch-summary-v1",
        "created_unix_ms": now_unix_ms(),
        "processed": len(results),
        "okay": okay_count,
        "failed": fail_count,
        "results": results,
    }

    summary_path = cfg.certificate_dir / "batch-summary.json"
    write_json(summary_path, summary)

    print(json.dumps(summary, indent=2, ensure_ascii=False))
    return 0 if fail_count == 0 else 2


def cmd_check_certs(args: argparse.Namespace) -> int:
    cfg = Config.from_args(args)

    certs = sorted(cfg.certificate_dir.glob(args.pattern))

    rows: List[Dict[str, Any]] = []
    okay_count = 0
    fail_count = 0

    for cert_path in certs:
        if cert_path.name == "batch-summary.json":
            continue

        try:
            certificate = load_json(cert_path)
            result = extract_api_result(certificate)

            okay = result.get("okay") is True
            failed_declarations = result.get("failed_declarations", [])
            failed_decl_ok = failed_declarations == []
            valid = okay and failed_decl_ok

            if valid:
                okay_count += 1
            else:
                fail_count += 1

            rows.append({
                "certificate_file": relpath_or_str(cert_path, cfg.root),
                "base": certificate.get("base", cert_path.name.removesuffix(".axle.json")),
                "okay": okay,
                "failed_declarations_empty": failed_decl_ok,
                "valid_certificate": valid,
                "failed_declarations": failed_declarations,
                "request_id": (
                    result.get("info", {}).get("request_id")
                    if isinstance(result.get("info"), dict)
                    else None
                ),
            })

        except Exception as exc:
            fail_count += 1
            rows.append({
                "certificate_file": relpath_or_str(cert_path, cfg.root),
                "valid_certificate": False,
                "error": f"{type(exc).__name__}: {exc}",
            })

    summary = {
        "checked": len(rows),
        "valid": okay_count,
        "invalid": fail_count,
        "rows": rows,
    }

    print(json.dumps(summary, indent=2, ensure_ascii=False))
    return 0 if fail_count == 0 else 2


def cmd_show_cert(args: argparse.Namespace) -> int:
    cfg = Config.from_args(args)

    if args.base:
        cert_path = cfg.certificate_dir / f"{args.base}.axle.json"
    else:
        cert_path = Path(args.certificate).resolve()

    certificate = load_json(cert_path)
    result = extract_api_result(certificate)

    print(json.dumps({
        "certificate_file": relpath_or_str(cert_path, cfg.root),
        "base": certificate.get("base", cert_path.name.removesuffix(".axle.json")),
        "okay": result.get("okay") is True,
        "failed_declarations": result.get("failed_declarations", []),
        "valid_certificate": cert_is_okay(certificate),
        "request_id": (
            result.get("info", {}).get("request_id")
            if isinstance(result.get("info"), dict)
            else None
        ),
        "lean_errors": (
            result.get("lean_messages", {}).get("errors", [])
            if isinstance(result.get("lean_messages"), dict)
            else []
        ),
        "tool_errors": (
            result.get("tool_messages", {}).get("errors", [])
            if isinstance(result.get("tool_messages"), dict)
            else []
        ),
    }, indent=2, ensure_ascii=False))

    return 0 if cert_is_okay(certificate) else 2


# ---------------------------------------------------------------------------
# Parser
# ---------------------------------------------------------------------------

def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Run AXLE API verification and manage certificates/source maps."
    )

    sub = parser.add_subparsers(dest="command", required=True)

    p_one = sub.add_parser("verify-one", help="Verify one statement/proof pair through AXLE API.")
    add_common_args(p_one)
    p_one.add_argument("--base")
    p_one.add_argument("--statement")
    p_one.add_argument("--proof")
    p_one.add_argument("--certificate-out")
    p_one.add_argument("--map-out")
    p_one.add_argument("--no-precheck-fail", action="store_true")
    p_one.set_defaults(func=cmd_verify_one)

    p_all = sub.add_parser("verify-all", help="Verify all *.statement.lean files through AXLE API.")
    add_common_args(p_all)
    p_all.add_argument("--pattern", default="*.statement.lean")
    p_all.add_argument("--no-precheck-fail", action="store_true")
    p_all.add_argument("--stop-on-fail", action="store_true")
    p_all.set_defaults(func=cmd_verify_all)

    p_check = sub.add_parser("check-certs", help="Check certificates already saved; no API call.")
    add_common_args(p_check)
    p_check.add_argument("--pattern", default="*.axle.json")
    p_check.set_defaults(func=cmd_check_certs)

    p_show = sub.add_parser("show-cert", help="Show one certificate status; no API call.")
    add_common_args(p_show)
    p_show.add_argument("--base")
    p_show.add_argument("--certificate")
    p_show.set_defaults(func=cmd_show_cert)

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