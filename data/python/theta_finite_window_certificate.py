#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
theta_finite_window_certificate.py

Certificat fini pour la borne explicite sur

    R(x) = |theta(x) - x| * (log x)^2 / x

sur une fenêtre finie [Y0, X_tail].

Objectif :
- fermer uniquement la fenêtre finie ;
- exposer les intervalles constants de thetaUpTo ;
- produire une borne globale M_finite ;
- afficher les résultats directement dans PowerShell ;
- n'écrire le JSON final que si la fenêtre est effectivement fermée.

Dépendance :
    pip install mpmath
"""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import sys
from dataclasses import dataclass, asdict
from datetime import datetime, timezone
from typing import Any, Dict, List, Optional

from mpmath import mp, iv


# ============================================================
# Paramètres
# ============================================================

Y0_DEFAULT = 30000
DEFAULT_DPS = 100


# ============================================================
# Structures
# ============================================================

@dataclass
class IntervalRecord:
    left: int
    right: int
    right_open: bool
    theta_const_lo: str
    theta_const_hi: str
    theta_semantics: str
    abs_diff_sup_lo: str
    abs_diff_sup_hi: str
    log_sq_over_x_sup_lo: str
    log_sq_over_x_sup_hi: str
    r_interval_hi: str


@dataclass
class PrimeRecord:
    prime: int
    theta_lo: str
    theta_hi: str
    r_at_prime_hi: str


# ============================================================
# Utilitaires interval arithmetic
# ============================================================

def iv_point(n: int) -> iv.mpf:
    return iv.mpf([n, n])


def iv_from_bounds(a: int, b: int) -> iv.mpf:
    return iv.mpf([a, b])


def iv_lo_str(x: iv.mpf, digits: int = 50) -> str:
    return mp.nstr(x.a, n=digits)


def iv_hi_str(x: iv.mpf, digits: int = 50) -> str:
    return mp.nstr(x.b, n=digits)


def mp_str(x: mp.mpf, digits: int = 50) -> str:
    return mp.nstr(x, n=digits)


def stable_hash_of_object(obj: Any) -> str:
    payload = json.dumps(
        obj,
        sort_keys=True,
        ensure_ascii=False,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


# ============================================================
# Crible
# ============================================================

def sieve_primes_up_to(n: int) -> List[int]:
    if n < 2:
        return []

    sieve = bytearray(b"\x01") * (n + 1)
    sieve[0:2] = b"\x00\x00"

    k = 2
    while k * k <= n:
        if sieve[k]:
            start = k * k
            step = k
            sieve[start:n + 1:step] = b"\x00" * (((n - start) // step) + 1)
        k += 1

    return [i for i in range(2, n + 1) if sieve[i]]


# ============================================================
# Theta
# ============================================================

def theta_prefix_sums_iv(primes: List[int]) -> List[iv.mpf]:
    """
    Renvoie theta(p_k) = sum_{p <= p_k} log p sous forme d'intervalles.
    """
    total = iv.mpf([0, 0])
    out: List[iv.mpf] = []
    for p in primes:
        total = total + iv.log(iv_point(p))
        out.append(total)
    return out


# ============================================================
# Briques analytiques locales
# ============================================================

def log_sq_over_x(x: iv.mpf) -> iv.mpf:
    """
    g(x) = (log x)^2 / x
    """
    return (iv.log(x) ** 2) / x


def log_sq_over_x_is_decreasing_on_window(y0: int) -> bool:
    """
    g'(x) = log(x)(2-log(x))/x^2
    Donc g décroît pour x > e^2.
    Ici on renvoie simplement si y0 >= ceil(e^2).
    """
    return y0 >= 8


def sup_log_sq_over_x_on_interval(a: int, b: int) -> iv.mpf:
    """
    Sur notre fenêtre (a >= 30000), g(x)=(log x)^2/x est décroissante,
    donc son sup sur [a,b) ou [a,b] est g(a).
    """
    if a < 8:
        raise ValueError("This monotonic bound is intended only for a >= 8.")
    return log_sq_over_x(iv_point(a))


def sup_abs_c_minus_x_on_interval(theta_const: iv.mpf, a: int, b: int) -> iv.mpf:
    """
    Calcule un majorant rigoureux de sup_{x in [a,b]} |c - x|
    où c appartient à l'intervalle theta_const.
    On majore par max(|c-a|, |c-b|), traité de façon rigoureuse.

    Comme theta_const est lui-même un intervalle [c_lo, c_hi],
    on borne :
        |c-a| <= max(|c_lo-a|, |c_hi-a|)
        |c-b| <= max(|c_lo-b|, |c_hi-b|)
    puis on prend le max global.
    """
    a_iv = iv_point(a)
    b_iv = iv_point(b)

    end_a = abs(theta_const - a_iv)
    end_b = abs(theta_const - b_iv)

    hi = max(end_a.b, end_b.b)
    return iv.mpf([mp.mpf("0"), hi])


def r_point(theta_const: iv.mpf, x: int) -> iv.mpf:
    """
    Valeur de R(x) en un point.
    """
    x_iv = iv_point(x)
    return abs(theta_const - x_iv) * log_sq_over_x(x_iv)


def interval_upper_bound_structured(theta_const: iv.mpf, a: int, b: int) -> Dict[str, iv.mpf]:
    """
    Majorant structuré sur [a,b) ou [a,b] :
        R(x) <= sup |theta_const - x| * sup ((log x)^2 / x)
    """
    abs_diff_sup = sup_abs_c_minus_x_on_interval(theta_const, a, b)
    log_sq_sup = sup_log_sq_over_x_on_interval(a, b)
    r_sup = abs_diff_sup * log_sq_sup
    return {
        "abs_diff_sup": abs_diff_sup,
        "log_sq_over_x_sup": log_sq_sup,
        "r_sup": r_sup,
    }


# ============================================================
# Génération du certificat
# ============================================================

def build_finite_window_certificate(
    y0: int,
    x_tail: int,
    dps: int,
    mode: str,
    include_prime_records: bool,
) -> Dict[str, Any]:
    if x_tail < y0:
        raise ValueError("x_tail must satisfy x_tail >= y0.")

    if not log_sq_over_x_is_decreasing_on_window(y0):
        raise ValueError("The structured interval bound assumes y0 >= 8.")

    mp.dps = dps

    all_primes = sieve_primes_up_to(x_tail)
    if not all_primes:
        raise ValueError("No primes found up to x_tail.")

    theta_vals = theta_prefix_sums_iv(all_primes)
    theta_by_prime = {p: t for p, t in zip(all_primes, theta_vals)}

    window_primes = [p for p in all_primes if y0 <= p <= x_tail]
    if not window_primes:
        raise ValueError("No primes found in [Y0, X_tail].")

    first_prime = window_primes[0]
    last_prime = window_primes[-1]

    idx_first = all_primes.index(first_prime)
    theta_before_window = iv.mpf([0, 0]) if idx_first == 0 else theta_vals[idx_first - 1]

    interval_records: List[IntervalRecord] = []
    prime_records: List[PrimeRecord] = []

    m_finite_hi = mp.mpf("0")
    max_interval_index = -1
    max_interval_hi = mp.mpf("0")

    # --- Prime records (mode debug surtout)
    if include_prime_records:
        for p in window_primes:
            theta_p = theta_by_prime[p]
            r_p = r_point(theta_p, p)
            r_p_hi = r_p.b

            prime_records.append(
                PrimeRecord(
                    prime=p,
                    theta_lo=iv_lo_str(theta_p),
                    theta_hi=iv_hi_str(theta_p),
                    r_at_prime_hi=iv_hi_str(r_p),
                )
            )

            if r_p_hi > m_finite_hi:
                m_finite_hi = r_p_hi

    # --- Intervalle initial [y0, first_prime)
    if y0 < first_prime:
        local = interval_upper_bound_structured(theta_before_window, y0, first_prime)
        r_hi = local["r_sup"].b

        interval_records.append(
            IntervalRecord(
                left=y0,
                right=first_prime,
                right_open=True,
                theta_const_lo=iv_lo_str(theta_before_window),
                theta_const_hi=iv_hi_str(theta_before_window),
                theta_semantics="thetaUpTo(x) is constant on [left,right) with value theta_const",
                abs_diff_sup_lo=iv_lo_str(local["abs_diff_sup"]),
                abs_diff_sup_hi=iv_hi_str(local["abs_diff_sup"]),
                log_sq_over_x_sup_lo=iv_lo_str(local["log_sq_over_x_sup"]),
                log_sq_over_x_sup_hi=iv_hi_str(local["log_sq_over_x_sup"]),
                r_interval_hi=iv_hi_str(local["r_sup"]),
            )
        )

        if r_hi > m_finite_hi:
            m_finite_hi = r_hi
            max_interval_index = len(interval_records) - 1
            max_interval_hi = r_hi

    # --- Intervalles [p_i, p_{i+1})
    for i in range(len(window_primes) - 1):
        p = window_primes[i]
        q = window_primes[i + 1]
        theta_const = theta_by_prime[p]

        local = interval_upper_bound_structured(theta_const, p, q)
        r_hi = local["r_sup"].b

        interval_records.append(
            IntervalRecord(
                left=p,
                right=q,
                right_open=True,
                theta_const_lo=iv_lo_str(theta_const),
                theta_const_hi=iv_hi_str(theta_const),
                theta_semantics="thetaUpTo(x) is constant on [left,right) with value theta_const",
                abs_diff_sup_lo=iv_lo_str(local["abs_diff_sup"]),
                abs_diff_sup_hi=iv_hi_str(local["abs_diff_sup"]),
                log_sq_over_x_sup_lo=iv_lo_str(local["log_sq_over_x_sup"]),
                log_sq_over_x_sup_hi=iv_hi_str(local["log_sq_over_x_sup"]),
                r_interval_hi=iv_hi_str(local["r_sup"]),
            )
        )

        if r_hi > m_finite_hi:
            m_finite_hi = r_hi
            max_interval_index = len(interval_records) - 1
            max_interval_hi = r_hi

    # --- Dernier intervalle [last_prime, x_tail]
    theta_last = theta_by_prime[last_prime]
    local = interval_upper_bound_structured(theta_last, last_prime, x_tail)
    r_hi = local["r_sup"].b

    interval_records.append(
        IntervalRecord(
            left=last_prime,
            right=x_tail,
            right_open=False,
            theta_const_lo=iv_lo_str(theta_last),
            theta_const_hi=iv_hi_str(theta_last),
            theta_semantics="thetaUpTo(x) is constant on [left,right] with value theta_const",
            abs_diff_sup_lo=iv_lo_str(local["abs_diff_sup"]),
            abs_diff_sup_hi=iv_hi_str(local["abs_diff_sup"]),
            log_sq_over_x_sup_lo=iv_lo_str(local["log_sq_over_x_sup"]),
            log_sq_over_x_sup_hi=iv_hi_str(local["log_sq_over_x_sup"]),
            r_interval_hi=iv_hi_str(local["r_sup"]),
        )
    )

    if r_hi > m_finite_hi:
        m_finite_hi = r_hi
        max_interval_index = len(interval_records) - 1
        max_interval_hi = r_hi

    proved_le_two = (m_finite_hi <= mp.mpf("2"))

    cert_core: Dict[str, Any] = {
        "scope": {
            "y0": y0,
            "x_tail": x_tail,
            "domain_convention": (
                "finite real window [Y0, X_tail]; "
                "coverage by intervals on which thetaUpTo is constant"
            ),
            "quantity": "R(x) = |theta(x) - x| * (log x)^2 / x",
            "certificate_role": "finite window only",
            "tail_strategy": (
                "finite window only; infinite tail handled separately in Lean "
                "by an analytic theorem"
            ),
            "interval_bound_strategy": (
                "R(x) <= sup(|theta_const - x|) * sup((log x)^2 / x) "
                "on each interval where thetaUpTo is constant"
            ),
        },
        "metadata": {
            "generated_at_utc": datetime.now(timezone.utc).isoformat(),
            "python_version": sys.version,
            "platform": platform.platform(),
            "mpmath_dps": dps,
            "mode": mode,
        },
        "summary": {
            "prime_count_up_to_x_tail": len(all_primes),
            "window_prime_count": len(window_primes),
            "first_prime_in_window": first_prime,
            "last_prime_in_window": last_prime,
            "interval_count": len(interval_records),
        },
        "global_bound": {
            "m_finite_hi": mp_str(m_finite_hi, digits=60),
            "proved_m_finite_le_2": proved_le_two,
            "threshold": "2",
            "worst_interval_index": max_interval_index,
            "worst_interval_hi": mp_str(max_interval_hi, digits=60),
        },
        "interval_records": [asdict(r) for r in interval_records],
    }

    if mode == "debug":
        cert_core["theta_data"] = {
            "theta_before_window_lo": iv_lo_str(theta_before_window),
            "theta_before_window_hi": iv_hi_str(theta_before_window),
        }
        cert_core["window_primes"] = window_primes
        if include_prime_records:
            cert_core["prime_records"] = [asdict(r) for r in prime_records]

    cert_hash = stable_hash_of_object(cert_core)
    cert_core["metadata"]["certificate_sha256"] = cert_hash

    return cert_core


# ============================================================
# Affichage console / PowerShell
# ============================================================

def print_console_summary(cert: Dict[str, Any], show_worst_interval: bool = True) -> None:
    scope = cert["scope"]
    meta = cert["metadata"]
    summary = cert["summary"]
    gb = cert["global_bound"]

    print("")
    print("=== Theta finite window certificate ===")
    print(f"Y0                      : {scope['y0']}")
    print(f"X_tail                  : {scope['x_tail']}")
    print(f"Mode                    : {meta['mode']}")
    print(f"Precision (mp.dps)      : {meta['mpmath_dps']}")
    print(f"Window prime count      : {summary['window_prime_count']}")
    print(f"Interval count          : {summary['interval_count']}")
    print(f"M_finite_hi             : {gb['m_finite_hi']}")
    print(f"Proved M_finite <= 2    : {gb['proved_m_finite_le_2']}")
    print(f"Certificate SHA256      : {meta['certificate_sha256']}")
    print("")

    if show_worst_interval and gb["worst_interval_index"] >= 0:
        idx = gb["worst_interval_index"]
        rec = cert["interval_records"][idx]
        br = ")" if rec["right_open"] else "]"
        print("Worst interval:")
        print(f"  index                 : {idx}")
        print(f"  domain                : [{rec['left']}, {rec['right']}{br}")
        print(f"  theta const hi        : {rec['theta_const_hi']}")
        print(f"  abs diff sup hi       : {rec['abs_diff_sup_hi']}")
        print(f"  log^2/x sup hi        : {rec['log_sq_over_x_sup_hi']}")
        print(f"  R interval hi         : {rec['r_interval_hi']}")
        print("")


def print_console_intervals(cert: Dict[str, Any], limit: Optional[int] = None) -> None:
    records = cert["interval_records"]
    n = len(records) if limit is None else min(limit, len(records))

    print("")
    print("=== Interval records ===")
    for i in range(n):
        rec = records[i]
        br = ")" if rec["right_open"] else "]"
        print(
            f"[{i}] domain=[{rec['left']}, {rec['right']}{br} "
            f"R_hi={rec['r_interval_hi']}"
        )
    print("")


# ============================================================
# Export JSON
# ============================================================

def write_json(path: str, cert: Dict[str, Any]) -> None:
    with open(path, "w", encoding="utf-8") as f:
        json.dump(cert, f, indent=2, ensure_ascii=False)


# ============================================================
# CLI
# ============================================================

def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate a finite-window theta certificate and print results in PowerShell."
    )

    parser.add_argument("--y0", type=int, default=Y0_DEFAULT, help="Lower bound of the finite window.")
    parser.add_argument("--x-tail", type=int, required=True, help="Upper bound of the finite window.")
    parser.add_argument("--dps", type=int, default=DEFAULT_DPS, help="mpmath working precision.")

    parser.add_argument(
        "--mode",
        choices=["final", "debug"],
        default="final",
        help="final = compact certificate; debug = keep more data.",
    )

    parser.add_argument(
        "--include-prime-records",
        action="store_true",
        help="Include detailed prime records (mostly useful in debug mode).",
    )

    parser.add_argument(
        "--json-out",
        type=str,
        default=None,
        help="Write JSON certificate only if the finite window is successfully closed.",
    )

    parser.add_argument(
        "--json-out-anyway",
        type=str,
        default=None,
        help="Write JSON certificate even if the finite window is not closed.",
    )

    parser.add_argument(
        "--print-intervals",
        action="store_true",
        help="Print interval summaries to console.",
    )

    parser.add_argument(
        "--interval-limit",
        type=int,
        default=20,
        help="Max number of intervals printed with --print-intervals.",
    )

    return parser.parse_args()


def main() -> None:
    args = parse_args()

    cert = build_finite_window_certificate(
        y0=args.y0,
        x_tail=args.x_tail,
        dps=args.dps,
        mode=args.mode,
        include_prime_records=args.include_prime_records,
    )

    print_console_summary(cert, show_worst_interval=True)

    if args.print_intervals:
        print_console_intervals(cert, limit=args.interval_limit)

    closed = cert["global_bound"]["proved_m_finite_le_2"]

    if args.json_out_anyway:
        write_json(args.json_out_anyway, cert)
        print(f"[ok] JSON written unconditionally to: {args.json_out_anyway}")

    if args.json_out:
        if closed:
            write_json(args.json_out, cert)
            print(f"[ok] finite window closed, JSON written to: {args.json_out}")
        else:
            print("[info] finite window not closed; JSON not written because --json-out requires success")

    if not closed:
        sys.exit(2)


if __name__ == "__main__":
    main()