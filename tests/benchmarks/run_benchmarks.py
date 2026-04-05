#!/usr/bin/env python3
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
"""Benchmark runner for slang using RTLMeter designs.

Each benchmark is identified by a DESIGN:CONFIGURATION pair from RTLMeter's
descriptor.yaml files. The TEST portion of RTLMeter cases is not applicable
here since slang is a compiler, not a simulator.

Usage examples:
  # List all available cases
  python run_benchmarks.py --rtlmeter-dir /path/to/rtlmeter list

  # Run all cases
  python run_benchmarks.py --rtlmeter-dir /path/to/rtlmeter \\
      run --slang /path/to/slang

  # Run specific cases
  python run_benchmarks.py --rtlmeter-dir /path/to/rtlmeter \\
      run --slang /path/to/slang Example:default VeeR-EH1:default

  # Output Bencher Metric Format JSON for CI integration
  python run_benchmarks.py --rtlmeter-dir /path/to/rtlmeter \\
      run --slang /path/to/slang --bencher
"""

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

try:
    import yaml
except ImportError:
    print(
        "Error: PyYAML is required. Install with: pip install pyyaml", file=sys.stderr
    )
    sys.exit(1)


def load_extra_args(path: Path) -> dict[str, dict]:
    """Load a YAML sidecar file that maps design names or DESIGN:CONFIG keys to
    per-case options (args, skip, ...). Returns an empty dict if the file does
    not exist."""
    if not path.exists():
        return {}
    with path.open() as f:
        data = yaml.safe_load(f) or {}
    result: dict[str, dict] = {}
    for key, value in data.items():
        if isinstance(value, dict):
            result[str(key)] = value
    return result


def extra_args_for(design: str, config: str, extra: dict[str, dict]) -> list[str]:
    """Return the extra slang args that apply to this case.

    Per-design entries (keyed by design name alone) are returned first, then
    per-case entries (keyed by 'DESIGN:CONFIG') are appended.
    """
    args: list[str] = []
    for key in (design, f"{design}:{config}"):
        raw = extra.get(key, {}).get("args", [])
        if isinstance(raw, list):
            args += [str(a) for a in raw]
    return args


def is_skipped(design: str, config: str, extra: dict[str, dict]) -> bool:
    """Return True if this case is marked ``skip: true`` in the extra-args map.

    A design-level ``skip`` skips all configurations of that design; a
    case-level ``skip`` (keyed by 'DESIGN:CONFIG') skips only that case.
    """
    for key in (design, f"{design}:{config}"):
        if extra.get(key, {}).get("skip", False):
            return True
    return False


def resolve_extra_args(args: list[str], design_dir: Path) -> list[str]:
    """Resolve path arguments in an extra-args list relative to design_dir.

    Any argument that does not start with '-' is treated as a file path and
    resolved to an absolute path relative to the design directory. Arguments
    starting with '-' (flags and flag=value pairs) are passed through unchanged.
    """
    resolved: list[str] = []
    for arg in args:
        if not arg.startswith("-"):
            resolved.append(str((design_dir / arg).resolve()))
        else:
            resolved.append(arg)
    return resolved


def find_rtlmeter_dir(script_dir: Path) -> Path:
    """Find the rtlmeter directory adjacent to the benchmark script."""
    candidate = script_dir / "rtlmeter"
    if candidate.is_dir():
        return candidate
    raise RuntimeError(
        "Could not find rtlmeter directory. "
        "Pass --rtlmeter-dir explicitly or build with -DSLANG_INCLUDE_BENCHMARKS=ON "
        "to have CMake fetch it automatically."
    )


def load_descriptor(design_dir: Path) -> dict[str, Any]:
    """Load and return the descriptor.yaml for a design."""
    path = design_dir / "descriptor.yaml"
    with path.open() as f:
        return yaml.safe_load(f)


def merge_compile(base: dict[str, Any], override: dict[str, Any]) -> dict[str, Any]:
    """Merge a configuration's compile section into the base compile section.

    Lists are concatenated; dicts are merged with the override taking precedence
    for duplicate keys; all other values are replaced by the override.
    """
    result = dict(base)
    for key, value in override.items():
        if key in result and isinstance(result[key], list) and isinstance(value, list):
            result[key] = result[key] + value
        elif (
            key in result and isinstance(result[key], dict) and isinstance(value, dict)
        ):
            result[key] = {**result[key], **value}
        else:
            result[key] = value
    return result


def list_cases(rtlmeter_dir: Path) -> list[tuple[str, str]]:
    """Return all (design, configuration) pairs available in RTLMeter."""
    cases: list[tuple[str, str]] = []
    designs_dir = rtlmeter_dir / "designs"
    if not designs_dir.is_dir():
        raise RuntimeError(f"No 'designs' directory found in {rtlmeter_dir}")

    for design_dir in sorted(designs_dir.iterdir()):
        if not design_dir.is_dir():
            continue
        descriptor_path = design_dir / "descriptor.yaml"
        if not descriptor_path.exists():
            continue

        descriptor = load_descriptor(design_dir)
        configurations = list((descriptor.get("configurations") or {}).keys())
        if not configurations:
            configurations = ["default"]

        for config in configurations:
            cases.append((design_dir.name, config))

    return cases


def build_slang_command(
    slang_bin: Path,
    design_dir: Path,
    compile_section: dict[str, Any],
    extra_args: list[str] | None = None,
) -> list[str]:
    """Build the slang command line for a given compile descriptor section."""
    cmd: list[str] = [str(slang_bin)]

    # Suppress the normal "Build succeeded" summary so that stdout contains
    # only the --time-stats JSON, which we need to parse cleanly.
    cmd.append("--quiet")

    # Request the timing/memory summary on stdout so we can parse it.
    cmd += ["--time-stats", "-"]

    # Don't warn about missing timescales
    cmd.append("--timescale=1ns/1ns")

    # RTLMeter setup assumes we have these added to every design
    cmd.append(f"-I{design_dir.parent.parent / 'rtl'}")
    cmd.append(design_dir.parent.parent / "rtl" / "__rtlmeter_utils.sv")

    # Per-design/per-case extra arguments supplied outside the descriptor.
    if extra_args:
        cmd.extend(extra_args)

    # Verilog source files (positional arguments).
    for f in compile_section.get("verilogSourceFiles") or []:
        cmd.append(str(design_dir / f))

    # Verilog include files: add the containing directories as -I paths so
    # that `include directives resolve correctly. Deduplicate while preserving
    # order.
    seen_dirs: set[Path] = set()
    for f in compile_section.get("verilogIncludeFiles") or []:
        inc_dir = (design_dir / f).parent
        if inc_dir not in seen_dirs:
            seen_dirs.add(inc_dir)
            cmd += ["-I", str(inc_dir)]

    # Preprocessor defines.
    for k, v in (compile_section.get("verilogDefines") or {}).items():
        if v is None or v == "":
            cmd.append(f"-D{k}")
        else:
            cmd.append(f"-D{k}={v}")

    # Top-level module.
    top = compile_section.get("topModule")
    if top:
        cmd += ["--top", top]

    # Main clock: expose as a preprocessor define so RTL can reference it.
    main_clock = compile_section.get("mainClock")
    if main_clock:
        cmd.append(f"-D__RTLMETER_MAIN_CLOCK={main_clock}")

    # Pass through -G parameter overrides from verilatorArgs. These are
    # top-level parameter overrides that slang supports with the same syntax.
    for arg in compile_section.get("verilatorArgs") or []:
        if isinstance(arg, str) and arg.startswith("-G"):
            cmd.append(arg)

    return cmd


def run_case(
    slang_bin: Path,
    design_dir: Path,
    compile_section: dict[str, Any],
    extra_args: list[str] | None = None,
    verbose: bool = False,
) -> dict[str, Any]:
    """Run slang on a design and return the collected metrics."""
    cmd = build_slang_command(slang_bin, design_dir, compile_section, extra_args)

    if verbose:
        print("  " + " ".join(cmd), file=sys.stderr)

    result = subprocess.run(
        cmd,
        capture_output=True,
        text=True,
    )

    # --time-stats - writes JSON to stdout; parse it.
    metrics: dict[str, Any] = {}
    if result.stdout.strip():
        try:
            metrics = json.loads(result.stdout)
        except json.JSONDecodeError:
            pass

    metrics["exit_code"] = result.returncode
    metrics["stderr"] = result.stderr
    return metrics


def format_table(results: list[tuple[str, str, dict[str, Any]]]) -> str:
    """Format results as a human-readable table."""
    w = [32, 12, 16, 15, 14]
    header = (
        f"{'Design:Config':<{w[0]}} {'Parse (ms)':>{w[1]}} "
        f"{'Elaborate (ms)':>{w[2]}} {'Analysis (ms)':>{w[3]}} "
        f"{'Peak Mem (MB)':>{w[4]}}"
    )
    sep = "-" * (sum(w) + len(w) - 1)
    lines = [header, sep]

    for design, config, metrics in results:
        label = f"{design}:{config}"
        if metrics.get("exit_code", 0) != 0:
            lines.append(f"{label:<{w[0]}} ERROR")
            continue

        parse_ms = metrics.get("parse_time_us", 0) / 1000.0
        elab_ms = metrics.get("elaborate_time_us", 0) / 1000.0
        anal_ms = metrics.get("analysis_time_us", 0) / 1000.0
        mem_mb = metrics.get("peak_memory_bytes", 0) / (1024.0 * 1024.0)

        lines.append(
            f"{label:<{w[0]}} {parse_ms:>{w[1]}.1f} "
            f"{elab_ms:>{w[2]}.1f} {anal_ms:>{w[3]}.1f} "
            f"{mem_mb:>{w[4]}.1f}"
        )

    return "\n".join(lines)


def format_bmf(results: list[tuple[str, str, dict[str, Any]]]) -> dict[str, Any]:
    """Format results as Bencher Metric Format (BMF) JSON."""
    bmf: dict[str, Any] = {}

    for design, config, metrics in results:
        if metrics.get("exit_code", 0) != 0:
            continue

        bmf[f"{design}:{config}"] = {
            "parse_time_us": {"value": metrics.get("parse_time_us", 0)},
            "elaborate_time_us": {"value": metrics.get("elaborate_time_us", 0)},
            "analysis_time_us": {"value": metrics.get("analysis_time_us", 0)},
            "peak_memory_mb": {
                "value": metrics.get("peak_memory_bytes", 0) / (1024.0 * 1024.0)
            },
        }

    return bmf


def cmd_list(args: argparse.Namespace, rtlmeter_dir: Path) -> int:
    cases = list_cases(rtlmeter_dir)
    for design, config in cases:
        print(f"{design}:{config}")
    return 0


def cmd_run(args: argparse.Namespace, rtlmeter_dir: Path) -> int:
    slang_bin = Path(args.slang)
    if not slang_bin.exists():
        print(f"Error: slang binary not found: {slang_bin}", file=sys.stderr)
        return 1

    # Load per-design extra slang arguments.
    script_dir = Path(__file__).parent.resolve()
    if args.slang_args_file:
        extra_args_path = Path(args.slang_args_file)
    else:
        extra_args_path = script_dir / "slang_args.yaml"
    extra_args_map = load_extra_args(extra_args_path)

    all_cases = list_cases(rtlmeter_dir)

    # Filter by the requested cases if any were specified.
    if args.cases:
        requested = set(args.cases)
        selected: list[tuple[str, str]] = []
        for design, config in all_cases:
            if f"{design}:{config}" in requested or design in requested:
                selected.append((design, config))
        if not selected:
            print(
                f"Error: no matching cases found for: {' '.join(args.cases)}",
                file=sys.stderr,
            )
            return 1
    else:
        selected = all_cases

    designs_dir = rtlmeter_dir / "designs"
    results: list[tuple[str, str, dict[str, Any]]] = []

    for design, config in selected:
        design_dir = designs_dir / design
        descriptor = load_descriptor(design_dir)

        base_compile: dict[str, Any] = descriptor.get("compile") or {}
        configurations: dict[str, Any] = descriptor.get("configurations") or {}

        if config not in configurations:
            compile_section = base_compile
        else:
            config_compile = (configurations[config] or {}).get("compile") or {}
            compile_section = merge_compile(base_compile, config_compile)

        label = f"{design}:{config}"
        if is_skipped(design, config, extra_args_map):
            print(f"Skipping {label} (marked skip in extra args file)", file=sys.stderr)
            continue
        print(f"Running {label}...", file=sys.stderr)
        case_extra = extra_args_for(design, config, extra_args_map)
        case_extra = resolve_extra_args(case_extra, design_dir)
        metrics = run_case(
            slang_bin, design_dir, compile_section, case_extra, verbose=args.verbose
        )

        if metrics["exit_code"] != 0:
            print(f"  FAILED (exit code {metrics['exit_code']})", file=sys.stderr)
            for line in metrics.get("stderr", "").splitlines():
                print(f"  {line}", file=sys.stderr)

        results.append((design, config, metrics))

    if args.bencher:
        output = json.dumps(format_bmf(results), indent=2)
    else:
        output = format_table(results)

    if args.output:
        Path(args.output).write_text(output + "\n")
    else:
        print(output)

    # Return non-zero if any case failed.
    return 0 if all(m.get("exit_code", 0) == 0 for _, _, m in results) else 1


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Run slang benchmarks using RTLMeter designs.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument(
        "--rtlmeter-dir",
        metavar="DIR",
        help="Path to the rtlmeter directory (auto-detected if omitted)",
    )

    subparsers = parser.add_subparsers(dest="command", required=True)

    # list subcommand
    list_parser = subparsers.add_parser(
        "list", help="List available DESIGN:CONFIGURATION pairs"
    )
    list_parser.set_defaults(func=cmd_list)

    # run subcommand
    run_parser = subparsers.add_parser("run", help="Run benchmarks")
    run_parser.add_argument(
        "cases",
        nargs="*",
        metavar="DESIGN:CONFIG",
        help="Cases to run (default: all). Can be 'DESIGN:CONFIG' or just 'DESIGN'.",
    )
    run_parser.add_argument(
        "--slang",
        required=True,
        metavar="PATH",
        help="Path to the slang driver binary",
    )
    run_parser.add_argument(
        "--bencher",
        action="store_true",
        help="Output results in Bencher Metric Format (BMF) JSON for CI integration",
    )
    run_parser.add_argument(
        "--output",
        metavar="FILE",
        help="Write output to FILE instead of stdout",
    )
    run_parser.add_argument(
        "-v",
        "--verbose",
        action="store_true",
        help="Print the full slang command line before each run",
    )
    run_parser.add_argument(
        "--slang-args-file",
        metavar="FILE",
        help="YAML file with extra per-design slang arguments "
        "(default: slang_args.yaml next to this script)",
    )
    run_parser.set_defaults(func=cmd_run)

    args = parser.parse_args()

    # Resolve the rtlmeter directory.
    script_dir = Path(__file__).parent.resolve()
    if args.rtlmeter_dir:
        rtlmeter_dir = Path(args.rtlmeter_dir).resolve()
    else:
        rtlmeter_dir = find_rtlmeter_dir(script_dir)

    if not rtlmeter_dir.is_dir():
        print(f"Error: rtlmeter directory not found: {rtlmeter_dir}", file=sys.stderr)
        return 1

    try:
        return args.func(args, rtlmeter_dir)
    except KeyboardInterrupt:
        print("\nInterrupted.", file=sys.stderr)
        return 130


if __name__ == "__main__":
    sys.exit(main())
