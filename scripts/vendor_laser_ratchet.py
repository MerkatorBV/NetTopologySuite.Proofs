#!/usr/bin/env python3
# =============================================================================
# scripts/vendor_laser_ratchet.py
# -----------------------------------------------------------------------------
# Validate a jts-emitted laser-ratchet JSON and, when it differs, copy it into
# docs/laser-ratchet.json.  The copy is the observatory's version history
# (`git log -- docs/laser-ratchet.json`).
#
# This is a vendor step, not a theorem.  Timings are not proofs.  Year-2
# zoo types are library work, not JTS PR 7 — copy implemented:false as
# jts sends them; never invent their timings.  Never start a 64-a sweep.
# Refuse to write when the upstream file is missing or not Pages-compatible.
#
# Usage:
#   python3 scripts/vendor_laser_ratchet.py validate PATH
#   python3 scripts/vendor_laser_ratchet.py apply UPSTREAM_PATH
#       [--dest docs/laser-ratchet.json] [--github-output PATH]
#
# apply exits 0 on success (changed or identical).  Prints changed= / tip=
# (and writes those keys to --github-output when given).  validate exits 0
# if the file is a Pages-compatible object, 1 otherwise.
#
# License: BSD-3-Clause (see LICENSE)
# =============================================================================

from __future__ import annotations

import argparse
import json
import os
import sys


ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEFAULT_DEST = os.path.join(ROOT, "docs", "laser-ratchet.json")

# Minimum shape scripts/gen_dashboard.py.laser_ratchet_html needs. Extra
# keys (chord_path, new harnesses, filled former-ungauged rows) are fine.
REQUIRED_TOP = ("contract", "provenance", "types")


def _err(msg: str) -> None:
    print(f"error: {msg}", file=sys.stderr)


def load_json(path: str) -> object:
    with open(path, encoding="utf-8") as f:
        raw = f.read()
    if not raw.strip():
        raise ValueError(f"{path} is empty")
    return json.loads(raw)


def validate(data: object, *, origin: str) -> list[str]:
    """Return a list of problems; empty means Pages-compatible."""
    problems: list[str] = []
    if not isinstance(data, dict):
        return [f"{origin}: expected a JSON object, got {type(data).__name__}"]

    for key in REQUIRED_TOP:
        if key not in data:
            problems.append(f"{origin}: missing required key {key!r}")

    contract = data.get("contract")
    if not isinstance(contract, dict):
        problems.append(f"{origin}: contract must be an object")
    else:
        if not isinstance(contract.get("expr"), str) or not contract["expr"].strip():
            problems.append(f"{origin}: contract.expr must be a non-empty string")
        slack = contract.get("slack")
        if not isinstance(slack, (int, float)) or isinstance(slack, bool):
            problems.append(f"{origin}: contract.slack must be a number")

    prov = data.get("provenance")
    if not isinstance(prov, dict):
        problems.append(f"{origin}: provenance must be an object")
    else:
        tip = prov.get("tip")
        if not isinstance(tip, str) or not tip.strip():
            problems.append(f"{origin}: provenance.tip must be a non-empty string")

    types = data.get("types")
    if "types" in data and not isinstance(types, list):
        problems.append(f"{origin}: types must be a list")
    elif isinstance(types, list):
        for i, t in enumerate(types):
            if not isinstance(t, dict) or not t.get("name"):
                problems.append(f"{origin}: types[{i}] must be an object with name")

    for key in ("primitive_gates", "operation_gates", "ungauged_gates"):
        if key in data and not isinstance(data[key], list):
            problems.append(f"{origin}: {key} must be a list when present")

    return problems


def provenance_tip(data: dict) -> str:
    tip = (data.get("provenance") or {}).get("tip")
    if isinstance(tip, str) and tip.strip():
        return tip.strip()
    return "unknown"


def write_outputs(path: str | None, mapping: dict[str, str]) -> None:
    for k, v in mapping.items():
        print(f"{k}={v}")
    if not path:
        return
    with open(path, "a", encoding="utf-8") as f:
        for k, v in mapping.items():
            f.write(f"{k}={v}\n")


def cmd_validate(path: str) -> int:
    try:
        data = load_json(path)
    except (OSError, ValueError) as exc:
        _err(f"invalid JSON at {path}: {exc}")
        return 1
    problems = validate(data, origin=path)
    if problems:
        for p in problems:
            _err(p)
        return 1
    print(f"ok: {path} is Pages-compatible (tip {provenance_tip(data)})")
    return 0


def cmd_apply(upstream: str, dest: str, github_output: str | None) -> int:
    try:
        data = load_json(upstream)
    except (OSError, ValueError) as exc:
        _err(f"jts emitter payload is not valid JSON ({upstream}): {exc}")
        return 1
    problems = validate(data, origin=upstream)
    if problems:
        for p in problems:
            _err(p)
        _err("refusing to vendor a payload that is not Pages-compatible")
        return 1

    tip = provenance_tip(data)
    local = None
    if os.path.exists(dest):
        try:
            local = load_json(dest)
        except (OSError, ValueError) as exc:
            _err(f"local {dest} is not valid JSON: {exc}")
            return 1

    if local == data:
        print(f"no-op: {dest} already matches upstream (tip {tip})")
        write_outputs(github_output, {"changed": "false", "tip": tip})
        return 0

    os.makedirs(os.path.dirname(dest) or ".", exist_ok=True)
    with open(upstream, encoding="utf-8") as src:
        payload = src.read()
    if not payload.endswith("\n"):
        payload += "\n"
    with open(dest, "w", encoding="utf-8", newline="\n") as out:
        out.write(payload)
    print(f"vendored {upstream} -> {dest} (tip {tip})")
    write_outputs(github_output, {"changed": "true", "tip": tip})
    return 0


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest="cmd", required=True)

    v = sub.add_parser("validate", help="check a laser-ratchet JSON is Pages-compatible")
    v.add_argument("path")

    a = sub.add_parser("apply", help="copy upstream JSON into docs/ if it differs")
    a.add_argument("upstream")
    a.add_argument("--dest", default=DEFAULT_DEST)
    a.add_argument("--github-output", default=os.environ.get("GITHUB_OUTPUT"))

    args = p.parse_args(argv)
    if args.cmd == "validate":
        return cmd_validate(args.path)
    return cmd_apply(args.upstream, args.dest, args.github_output)


if __name__ == "__main__":
    sys.exit(main())
