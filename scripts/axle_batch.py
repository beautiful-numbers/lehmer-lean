#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
axle_batch.py

Orchestrate the full AXLE audit pipeline, file by file.

For each entry in a manifest:
1. copy original Lean file into Audit_statement/Base.statement.lean
2. copy original Lean file into Audit_proof/Base.proof.lean
3. run axle_ready.py prepare-one
4. locally compile the prepared proof with `lake env lean`
5. locally compile the prepared statement with `lake env lean`
6. run axle_go.py verify-one through the AXLE API
7. check the generated certificate with axle_go.py show-cert
8. write a batch report

This script does NOT:
- guess dependencies
- loop/retry forever
- call AXLE if local Lean checks fail

Important:
- deps: [] is allowed.
- deps: [] means: try this file without dependency abstraction.
- If it fails, the report tells you where it failed.
"""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence


# ---------------------------------------------------------------------------
# IO / logging
# ---------------------------------------------------------------------------

def eprint(*args: Any) -> None:
    print(*args, file=sys.stderr, flush=True)


def log(message: str) -> None:
    print(message, flush=True)


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


def now_unix_ms() -> int:
    return int(time.time() * 1000)


def pct(base: str, percent: int, message: str) -> None:
    log(f"[{base}] {percent:3d}% | {message}")


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
        scripts_dir: Path,
        ready_script: Path,
        go_script: Path,
        lake_exe: Path,
        environment: str,
        report_dir: Path,
    ) -> None:
        self.root = root
        self.audit_dir = audit_dir
        self.axle_dir = axle_dir
        self.statement_dir = statement_dir
        self.proof_dir = proof_dir
        self.source_map_dir = source_map_dir
        self.certificate_dir = certificate_dir
        self.scripts_dir = scripts_dir
        self.ready_script = ready_script
        self.go_script = go_script
        self.lake_exe = lake_exe
        self.environment = environment
        self.report_dir = report_dir

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

        scripts_dir = Path(args.scripts_dir).resolve() if args.scripts_dir else (
            root / "scripts"
        )

        ready_script = Path(args.ready_script).resolve() if args.ready_script else (
            scripts_dir / "axle_ready.py"
        )

        go_script = Path(args.go_script).resolve() if args.go_script else (
            scripts_dir / "axle_go.py"
        )

        lake_exe = Path(args.lake_exe).resolve() if args.lake_exe else (
            Path.home() / ".elan" / "bin" / "lake.exe"
        )

        report_dir = Path(args.report_dir).resolve() if args.report_dir else (
            axle_dir / "batch-report"
        )

        return Config(
            root=root,
            audit_dir=audit_dir,
            axle_dir=axle_dir,
            statement_dir=statement_dir,
            proof_dir=proof_dir,
            source_map_dir=source_map_dir,
            certificate_dir=certificate_dir,
            scripts_dir=scripts_dir,
            ready_script=ready_script,
            go_script=go_script,
            lake_exe=lake_exe,
            environment=args.environment,
            report_dir=report_dir,
        )

    def ensure_dirs(self) -> None:
        self.axle_dir.mkdir(parents=True, exist_ok=True)
        self.statement_dir.mkdir(parents=True, exist_ok=True)
        self.proof_dir.mkdir(parents=True, exist_ok=True)
        self.source_map_dir.mkdir(parents=True, exist_ok=True)
        self.certificate_dir.mkdir(parents=True, exist_ok=True)
        self.report_dir.mkdir(parents=True, exist_ok=True)


# ---------------------------------------------------------------------------
# Shell helpers
# ---------------------------------------------------------------------------

def run_command(
    cmd: Sequence[str],
    *,
    cwd: Path,
    timeout_seconds: Optional[int] = None,
) -> Dict[str, Any]:
    started = now_unix_ms()

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
        )

        ended = now_unix_ms()

        return {
            "command": list(cmd),
            "returncode": proc.returncode,
            "stdout": proc.stdout,
            "stderr": proc.stderr,
            "duration_ms": ended - started,
            "timed_out": False,
        }

    except subprocess.TimeoutExpired as exc:
        ended = now_unix_ms()

        return {
            "command": list(cmd),
            "returncode": 124,
            "stdout": exc.stdout or "",
            "stderr": exc.stderr or "",
            "duration_ms": ended - started,
            "timed_out": True,
            "error": f"timeout_after_{timeout_seconds}_seconds",
        }


def command_ok(result: Dict[str, Any]) -> bool:
    return result.get("returncode") == 0


def parse_json_stdout(result: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    stdout = result.get("stdout", "")
    if not isinstance(stdout, str) or not stdout.strip():
        return None

    try:
        parsed = json.loads(stdout)
        if isinstance(parsed, dict):
            return parsed
    except json.JSONDecodeError:
        return None

    return None


# ---------------------------------------------------------------------------
# Manifest
# ---------------------------------------------------------------------------

def load_manifest(path: Path) -> List[Dict[str, Any]]:
    data = read_json(path)

    files = data.get("files")
    if not isinstance(files, list):
        raise ValueError("Manifest must contain a top-level list field: files")

    normalized: List[Dict[str, Any]] = []

    for i, item in enumerate(files):
        if not isinstance(item, dict):
            raise ValueError(f"Manifest entry #{i} is not an object")

        base = item.get("base")
        if not isinstance(base, str) or not base.strip():
            raise ValueError(f"Manifest entry #{i} is missing string field: base")

        deps = item.get("deps", [])
        def_params = item.get("def_params", [])
        replacements = item.get("replacements", [])

        if not isinstance(deps, list):
            raise ValueError(f"Manifest entry {base}: deps must be a list")
        if not isinstance(def_params, list):
            raise ValueError(f"Manifest entry {base}: def_params must be a list")
        if not isinstance(replacements, list):
            raise ValueError(f"Manifest entry {base}: replacements must be a list")

        normalized.append({
            "base": base.strip(),
            "deps": [str(x) for x in deps],
            "def_params": [str(x) for x in def_params],
            "replacements": [str(x) for x in replacements],
            "skip": bool(item.get("skip", False)),
            "status": str(item.get("status", "active")),
            "notes": item.get("notes", ""),
        })

    return normalized


def filter_manifest(
    files: List[Dict[str, Any]],
    *,
    only: Optional[str],
    from_base: Optional[str],
    max_files: Optional[int],
) -> List[Dict[str, Any]]:
    selected = files

    if only:
        selected = [x for x in selected if x["base"] == only]

    if from_base:
        seen = False
        after: List[Dict[str, Any]] = []
        for x in selected:
            if x["base"] == from_base:
                seen = True
            if seen:
                after.append(x)
        selected = after

    if max_files is not None:
        selected = selected[:max_files]

    return selected


# ---------------------------------------------------------------------------
# Paths / certificates
# ---------------------------------------------------------------------------

def certificate_path_for(base: str, cfg: Config) -> Path:
    return cfg.certificate_dir / f"{base}.axle.json"


def source_map_path_for(base: str, cfg: Config) -> Path:
    return cfg.source_map_dir / f"{base}.map.json"


def statement_path_for(base: str, cfg: Config) -> Path:
    return cfg.statement_dir / f"{base}.statement.lean"


def proof_path_for(base: str, cfg: Config) -> Path:
    return cfg.proof_dir / f"{base}.proof.lean"


def source_path_for(base: str, cfg: Config) -> Path:
    return cfg.audit_dir / f"{base}.lean"


def cert_json_is_valid(data: Dict[str, Any]) -> bool:
    result = data.get("result")
    if not isinstance(result, dict):
        result = data

    return (
        result.get("okay") is True
        and result.get("failed_declarations", []) == []
    )


def existing_certificate_valid(base: str, cfg: Config) -> bool:
    path = certificate_path_for(base, cfg)

    if not path.exists():
        log(f"[resume] {base}: no certificate found")
        return False

    try:
        data = read_json(path)
        valid = cert_json_is_valid(data)

        if valid:
            log(f"[resume] {base}: existing certificate is valid")
        else:
            log(f"[resume] {base}: existing certificate is NOT valid")

        return valid

    except Exception as exc:
        log(f"[resume] {base}: cannot read certificate: {type(exc).__name__}: {exc}")
        return False


# ---------------------------------------------------------------------------
# Pipeline stages
# ---------------------------------------------------------------------------

def copy_source_to_axle_pair(base: str, cfg: Config) -> Dict[str, Any]:
    source = source_path_for(base, cfg)
    statement = statement_path_for(base, cfg)
    proof = proof_path_for(base, cfg)

    if not source.exists():
        return {
            "okay": False,
            "stage": "copy_source",
            "error": f"missing_source:{source}",
        }

    statement.parent.mkdir(parents=True, exist_ok=True)
    proof.parent.mkdir(parents=True, exist_ok=True)

    shutil.copy2(source, statement)
    shutil.copy2(source, proof)

    return {
        "okay": True,
        "stage": "copy_source",
        "source_file": relpath_or_str(source, cfg.root),
        "statement_file": relpath_or_str(statement, cfg.root),
        "proof_file": relpath_or_str(proof, cfg.root),
    }


def run_axle_ready(
    entry: Dict[str, Any],
    cfg: Config,
    *,
    timeout_seconds: Optional[int],
) -> Dict[str, Any]:
    cmd: List[str] = [
        sys.executable,
        str(cfg.ready_script),
        "prepare-one",
        "--root",
        str(cfg.root),
        "--base",
        entry["base"],
    ]

    for dep in entry["deps"]:
        cmd.extend(["--dep", dep])

    for def_param in entry["def_params"]:
        cmd.extend(["--def-param", def_param])

    for replacement in entry["replacements"]:
        cmd.extend(["--replace", replacement])

    result = run_command(cmd, cwd=cfg.root, timeout_seconds=timeout_seconds)
    parsed = parse_json_stdout(result)

    return {
        "okay": command_ok(result),
        "stage": "axle_ready",
        "command_result": result,
        "json": parsed,
    }


def run_local_lean(
    path: Path,
    cfg: Config,
    *,
    stage: str,
    timeout_seconds: Optional[int],
) -> Dict[str, Any]:
    cmd = [
        str(cfg.lake_exe),
        "env",
        "lean",
        str(path),
    ]

    result = run_command(cmd, cwd=cfg.root, timeout_seconds=timeout_seconds)

    return {
        "okay": command_ok(result),
        "stage": stage,
        "file": relpath_or_str(path, cfg.root),
        "command_result": result,
    }


def run_axle_go_verify_one(
    base: str,
    cfg: Config,
    *,
    timeout_seconds: Optional[int],
    no_precheck_fail: bool,
) -> Dict[str, Any]:
    cmd: List[str] = [
        sys.executable,
        str(cfg.go_script),
        "verify-one",
        "--root",
        str(cfg.root),
        "--base",
        base,
        "--environment",
        cfg.environment,
    ]

    if no_precheck_fail:
        cmd.append("--no-precheck-fail")

    result = run_command(cmd, cwd=cfg.root, timeout_seconds=timeout_seconds)
    parsed = parse_json_stdout(result)

    okay = command_ok(result)
    if parsed is not None:
        okay = okay and parsed.get("valid_certificate") is True

    return {
        "okay": okay,
        "stage": "axle_go_verify",
        "command_result": result,
        "json": parsed,
    }


def run_axle_go_show_cert(
    base: str,
    cfg: Config,
    *,
    timeout_seconds: Optional[int],
) -> Dict[str, Any]:
    cmd = [
        sys.executable,
        str(cfg.go_script),
        "show-cert",
        "--root",
        str(cfg.root),
        "--base",
        base,
    ]

    result = run_command(cmd, cwd=cfg.root, timeout_seconds=timeout_seconds)
    parsed = parse_json_stdout(result)

    okay = command_ok(result)
    if parsed is not None:
        okay = okay and parsed.get("valid_certificate") is True

    return {
        "okay": okay,
        "stage": "check_certificate",
        "command_result": result,
        "json": parsed,
    }


# ---------------------------------------------------------------------------
# Reporting helpers
# ---------------------------------------------------------------------------

def slim_command_result(result: Dict[str, Any], *, keep_output: bool) -> Dict[str, Any]:
    slim = {
        "returncode": result.get("returncode"),
        "duration_ms": result.get("duration_ms"),
        "timed_out": result.get("timed_out", False),
        "command": result.get("command"),
    }

    if keep_output:
        slim["stdout"] = result.get("stdout", "")
        slim["stderr"] = result.get("stderr", "")
    else:
        stdout = result.get("stdout", "")
        stderr = result.get("stderr", "")

        slim["stdout_tail"] = stdout[-2000:] if isinstance(stdout, str) else ""
        slim["stderr_tail"] = stderr[-2000:] if isinstance(stderr, str) else ""

    if "error" in result:
        slim["error"] = result["error"]

    return slim


def slim_stage(stage: Dict[str, Any], *, keep_output: bool) -> Dict[str, Any]:
    out = {
        "stage": stage.get("stage"),
        "okay": stage.get("okay"),
    }

    if "file" in stage:
        out["file"] = stage["file"]

    if "error" in stage:
        out["error"] = stage["error"]

    if "json" in stage and stage["json"] is not None:
        out["json"] = stage["json"]

    if "command_result" in stage:
        out["command_result"] = slim_command_result(
            stage["command_result"],
            keep_output=keep_output,
        )

    for key in ["source_file", "statement_file", "proof_file"]:
        if key in stage:
            out[key] = stage[key]

    return out


def finish_row(
    base: str,
    stages: List[Dict[str, Any]],
    *,
    keep_output: bool,
) -> Dict[str, Any]:
    okay = bool(stages) and all(stage.get("okay") is True for stage in stages)
    failed_stage = None

    for stage in stages:
        if stage.get("okay") is not True:
            failed_stage = stage.get("stage")
            break

    return {
        "base": base,
        "okay": okay,
        "failed_stage": failed_stage,
        "stages": [
            slim_stage(stage, keep_output=keep_output)
            for stage in stages
        ],
    }


# ---------------------------------------------------------------------------
# One file pipeline
# ---------------------------------------------------------------------------

def process_one(
    entry: Dict[str, Any],
    cfg: Config,
    *,
    resume: bool,
    no_copy: bool,
    no_precheck_fail: bool,
    timeout_prepare: Optional[int],
    timeout_lean: Optional[int],
    timeout_axle: Optional[int],
    keep_output: bool,
) -> Dict[str, Any]:
    base = entry["base"]
    stages: List[Dict[str, Any]] = []

    pct(base, 0, "start")

    if entry.get("skip") or entry.get("status") == "skipped":
        pct(base, 100, "skipped by manifest")
        return {
            "base": base,
            "okay": True,
            "skipped": True,
            "stage": "manifest_skip",
            "notes": entry.get("notes", ""),
            "stages": [],
        }

    if resume:
        pct(base, 5, "checking existing certificate")
        if existing_certificate_valid(base, cfg):
            pct(base, 100, "resume skip: certificate already valid")
            return {
                "base": base,
                "okay": True,
                "skipped": True,
                "stage": "resume_valid_certificate",
                "certificate_file": relpath_or_str(certificate_path_for(base, cfg), cfg.root),
                "stages": [],
            }

    if not no_copy:
        pct(base, 10, "copy source -> statement/proof")
        copy_stage = copy_source_to_axle_pair(base, cfg)
        stages.append(copy_stage)
        if not copy_stage["okay"]:
            pct(base, 100, "FAIL at copy_source")
            return finish_row(base, stages, keep_output=keep_output)
    else:
        pct(base, 10, "copy skipped (--no-copy)")

    pct(base, 25, "prepare with axle_ready.py")
    ready_stage = run_axle_ready(
        entry,
        cfg,
        timeout_seconds=timeout_prepare,
    )
    stages.append(ready_stage)
    if not ready_stage["okay"]:
        pct(base, 100, "FAIL at axle_ready.py")
        return finish_row(base, stages, keep_output=keep_output)

    pct(base, 45, "local Lean compile proof")
    proof_stage = run_local_lean(
        proof_path_for(base, cfg),
        cfg,
        stage="local_proof_compile",
        timeout_seconds=timeout_lean,
    )
    stages.append(proof_stage)
    if not proof_stage["okay"]:
        pct(base, 100, "FAIL at local proof compile")
        return finish_row(base, stages, keep_output=keep_output)

    pct(base, 60, "local Lean compile statement")
    statement_stage = run_local_lean(
        statement_path_for(base, cfg),
        cfg,
        stage="local_statement_compile",
        timeout_seconds=timeout_lean,
    )
    stages.append(statement_stage)
    if not statement_stage["okay"]:
        pct(base, 100, "FAIL at local statement compile")
        return finish_row(base, stages, keep_output=keep_output)

    pct(base, 78, "AXLE API verify")
    verify_stage = run_axle_go_verify_one(
        base,
        cfg,
        timeout_seconds=timeout_axle,
        no_precheck_fail=no_precheck_fail,
    )
    stages.append(verify_stage)
    if not verify_stage["okay"]:
        pct(base, 100, "FAIL at AXLE verify")
        return finish_row(base, stages, keep_output=keep_output)

    pct(base, 92, "check certificate")
    cert_stage = run_axle_go_show_cert(
        base,
        cfg,
        timeout_seconds=timeout_prepare,
    )
    stages.append(cert_stage)

    if cert_stage["okay"]:
        pct(base, 100, "OK")
    else:
        pct(base, 100, "FAIL at certificate check")

    return finish_row(base, stages, keep_output=keep_output)


# ---------------------------------------------------------------------------
# Commands
# ---------------------------------------------------------------------------

def make_report(
    *,
    manifest_path: Path,
    cfg: Config,
    rows: List[Dict[str, Any]],
    total_selected: int,
) -> Dict[str, Any]:
    verified = sum(1 for r in rows if r.get("okay") is True and not r.get("skipped"))
    failed = sum(1 for r in rows if r.get("okay") is not True and not r.get("skipped"))
    skipped = sum(1 for r in rows if r.get("skipped"))
    certified = verified + skipped

    return {
        "schema": "axle-batch-orchestrator-v1",
        "created_unix_ms": now_unix_ms(),
        "manifest_file": relpath_or_str(manifest_path, cfg.root),
        "root": str(cfg.root),
        "total_selected": total_selected,
        "processed": len(rows),
        "verified": verified,
        "skipped": skipped,
        "certified_or_skipped_valid": certified,
        "failed": failed,
        "rows": rows,
    }


def cmd_run(args: argparse.Namespace) -> int:
    cfg = Config.from_args(args)
    cfg.ensure_dirs()

    manifest_path = Path(args.manifest).resolve()
    files = load_manifest(manifest_path)

    selected = filter_manifest(
        files,
        only=args.only,
        from_base=args.from_base,
        max_files=args.max_files,
    )

    report_rows: List[Dict[str, Any]] = []

    if not selected:
        log("[axle-batch] no files selected")
        return 2

    total = len(selected)
    log(f"[axle-batch] selected files: {total}")

    for entry in selected:
        index = len(report_rows) + 1
        global_percent = int((index - 1) * 100 / total)

        log("")
        log(f"[axle-batch] {index}/{total} | global {global_percent}% | processing {entry['base']}")

        row = process_one(
            entry,
            cfg,
            resume=args.resume,
            no_copy=args.no_copy,
            no_precheck_fail=args.no_precheck_fail,
            timeout_prepare=args.timeout_prepare,
            timeout_lean=args.timeout_lean,
            timeout_axle=args.timeout_axle,
            keep_output=args.keep_output,
        )

        report_rows.append(row)

        global_done = int(len(report_rows) * 100 / total)
        status = "OK" if row.get("okay") else "FAIL"
        failed_stage = row.get("failed_stage")

        if failed_stage:
            log(f"[axle-batch] {entry['base']}: {status} at {failed_stage} | global {global_done}%")
        else:
            log(f"[axle-batch] {entry['base']}: {status} | global {global_done}%")

        partial_report = make_report(
            manifest_path=manifest_path,
            cfg=cfg,
            rows=report_rows,
            total_selected=total,
        )
        progress_path = cfg.report_dir / "batch-progress.json"
        write_json(progress_path, partial_report)
        log(f"[axle-batch] progress report written: {relpath_or_str(progress_path, cfg.root)}")

        if args.stop_on_fail and not row.get("okay"):
            log("[axle-batch] stop-on-fail enabled; stopping")
            break

    report = make_report(
        manifest_path=manifest_path,
        cfg=cfg,
        rows=report_rows,
        total_selected=total,
    )

    report_path = Path(args.report_out).resolve() if args.report_out else (
        cfg.report_dir / "batch-report.json"
    )
    write_json(report_path, report)

    log("")
    log("[axle-batch] done")
    log(f"[axle-batch] processed: {report['processed']}")
    log(f"[axle-batch] verified : {report['verified']}")
    log(f"[axle-batch] skipped  : {report['skipped']}")
    log(f"[axle-batch] failed   : {report['failed']}")
    log(f"[axle-batch] report   : {relpath_or_str(report_path, cfg.root)}")

    print(json.dumps({
        "processed": report["processed"],
        "verified": report["verified"],
        "skipped": report["skipped"],
        "failed": report["failed"],
        "report_file": relpath_or_str(report_path, cfg.root),
    }, indent=2, ensure_ascii=False))

    return 0 if report["failed"] == 0 else 2


def cmd_validate_manifest(args: argparse.Namespace) -> int:
    cfg = Config.from_args(args)
    manifest_path = Path(args.manifest).resolve()
    files = load_manifest(manifest_path)

    rows: List[Dict[str, Any]] = []
    errors = 0

    for entry in files:
        base = entry["base"]
        source = source_path_for(base, cfg)

        row_errors: List[str] = []

        if not source.exists():
            row_errors.append(f"missing_source:{source}")

        # deps: [] is allowed.
        # It means: try this file without dependency abstraction.
        for dep in entry["deps"]:
            if ":" not in dep:
                row_errors.append(f"invalid_dep:{dep}")

        for item in entry["def_params"]:
            if "=" not in item:
                row_errors.append(f"invalid_def_param:{item}")

        for item in entry["replacements"]:
            if "=" not in item:
                row_errors.append(f"invalid_replacement:{item}")

        if row_errors:
            errors += 1

        rows.append({
            "base": base,
            "status": entry.get("status", "active"),
            "okay": not row_errors,
            "errors": row_errors,
        })

    result = {
        "manifest_file": relpath_or_str(manifest_path, cfg.root),
        "files": len(files),
        "invalid_entries": errors,
        "rows": rows,
    }

    print(json.dumps(result, indent=2, ensure_ascii=False))
    return 0 if errors == 0 else 2


def cmd_resume_plan(args: argparse.Namespace) -> int:
    cfg = Config.from_args(args)
    manifest_path = Path(args.manifest).resolve()
    files = load_manifest(manifest_path)

    rows: List[Dict[str, Any]] = []

    for entry in files:
        base = entry["base"]
        cert = certificate_path_for(base, cfg)

        if entry.get("skip") or entry.get("status") == "skipped":
            rows.append({
                "base": base,
                "status": entry.get("status", "skipped"),
                "certificate_file": relpath_or_str(cert, cfg.root),
                "certificate_exists": cert.exists(),
                "certificate_valid": False,
                "action_if_resume": "skip_manifest",
            })
            continue

        valid = existing_certificate_valid(base, cfg)

        rows.append({
            "base": base,
            "status": entry.get("status", "active"),
            "certificate_file": relpath_or_str(cert, cfg.root),
            "certificate_exists": cert.exists(),
            "certificate_valid": valid,
            "action_if_resume": "skip" if valid else "process",
        })

    result = {
        "manifest_file": relpath_or_str(manifest_path, cfg.root),
        "rows": rows,
        "already_valid": sum(1 for r in rows if r["certificate_valid"]),
        "to_process": sum(1 for r in rows if r["action_if_resume"] == "process"),
        "manifest_skipped": sum(1 for r in rows if r["action_if_resume"] == "skip_manifest"),
    }

    print(json.dumps(result, indent=2, ensure_ascii=False))
    return 0


# ---------------------------------------------------------------------------
# Parser
# ---------------------------------------------------------------------------

def add_common_args(p: argparse.ArgumentParser) -> None:
    p.add_argument("--root", help="Project root. Default: current directory.")
    p.add_argument("--audit-dir", help="Original audit directory.")
    p.add_argument("--axle-dir", help="Audit-axle root directory.")
    p.add_argument("--statement-dir", help="Directory of *.statement.lean files.")
    p.add_argument("--proof-dir", help="Directory of *.proof.lean files.")
    p.add_argument("--source-map-dir", help="Directory of *.map.json files.")
    p.add_argument("--certificate-dir", help="Directory of *.axle.json files.")
    p.add_argument("--scripts-dir", help="Directory containing axle_ready.py and axle_go.py.")
    p.add_argument("--ready-script", help="Path to axle_ready.py.")
    p.add_argument("--go-script", help="Path to axle_go.py.")
    p.add_argument("--lake-exe", help="Path to lake.exe.")
    p.add_argument("--environment", default="lean-4.28.0")
    p.add_argument("--report-dir", help="Directory for batch reports.")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Run axle_ready.py + local Lean checks + axle_go.py file by file."
    )

    sub = parser.add_subparsers(dest="command", required=True)

    p_run = sub.add_parser("run", help="Run the full batch pipeline.")
    add_common_args(p_run)
    p_run.add_argument("--manifest", required=True)
    p_run.add_argument("--only", help="Only process one base from the manifest.")
    p_run.add_argument("--from-base", help="Start from this base in manifest order.")
    p_run.add_argument("--max-files", type=int)
    p_run.add_argument("--resume", action="store_true", help="Skip files with already valid certificates.")
    p_run.add_argument("--stop-on-fail", action="store_true")
    p_run.add_argument("--no-copy", action="store_true", help="Do not recopy source before preparing.")
    p_run.add_argument("--no-precheck-fail", action="store_true", help="Forward to axle_go.py verify-one.")
    p_run.add_argument("--timeout-prepare", type=int, default=120)
    p_run.add_argument("--timeout-lean", type=int, default=300)
    p_run.add_argument("--timeout-axle", type=int, default=300)
    p_run.add_argument("--keep-output", action="store_true", help="Keep full stdout/stderr in report.")
    p_run.add_argument("--report-out")
    p_run.set_defaults(func=cmd_run)

    p_validate = sub.add_parser("validate-manifest", help="Validate manifest shape and source files.")
    add_common_args(p_validate)
    p_validate.add_argument("--manifest", required=True)
    p_validate.set_defaults(func=cmd_validate_manifest)

    p_resume = sub.add_parser("resume-plan", help="Show what --resume would skip/process.")
    add_common_args(p_resume)
    p_resume.add_argument("--manifest", required=True)
    p_resume.set_defaults(func=cmd_resume_plan)

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