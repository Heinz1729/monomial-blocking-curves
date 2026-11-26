"""Build the pinned Lean project and reproduce its cross-platform verification record."""
import argparse
from graphlib import TopologicalSorter
import hashlib
import json
from pathlib import Path
import re
import subprocess


ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
AXIOMS = re.compile(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")
PROJECT = Path(__file__).resolve().parents[1] / "lean"


def lean(project, *args, source=None):
    result = subprocess.run(["lake", *args], cwd=project, input=source, encoding="utf-8",
                            errors="replace", stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode:
        raise SystemExit(result.stdout)
    return result.stdout


def audit_all(project, modules):
    # Lean's own #print axioms collector, sharing its visited set across declarations.
    modules_literal = ", ".join(json.dumps(name) for name in modules)
    program = """
import BlockingCurves
import Lean.Elab.Print
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let modules : List String := [MODULES]
  for name in modules do
    unless env.header.moduleNames.contains (.str .anonymous name) do
      throwError "Module missing from the build entry point: {name}"
  let mut roots := #[]
  for (name, info) in env.constants.toList do
    if let some i := env.getModuleIdxFor? name then
      if modules.contains (env.header.moduleNames[i.toNat]!).toString then
        -- The compiler emits unsafe, source-less auxiliary stubs for executable code.
        -- The dependency closure of every retained root is still traversed unfiltered.
        if info.isUnsafe then
          if (← findDeclarationRangesCore? name).isNone then continue
        roots := roots.push name
  let (_, state) := (((roots.forM CollectAxioms.collect).run env).run {})
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for ax in state.axioms do
    unless permitted.contains ax do
      throwError "Unexpected axiom: {ax}"
  logInfo m!"Project audit passed ({roots.size} declarations)"
"""
    output = lean(project, "env", "lean", "--stdin", source=program.replace("MODULES", modules_literal))
    match = re.search(r"Project audit passed \((\d+) declarations\)", output)
    if not match or int(match[1]) == 0:
        raise SystemExit("Missing project-wide dependency audit result.\n" + output)
    # Generated declaration names and counts can vary with platform or elaborator settings.
    print(match[0])


def record(project):
    lean(project, "build")
    entry = project / "BlockingCurves.lean"
    expected = re.findall(r"^#print axioms ([\w.]+)$", entry.read_text(encoding="utf-8"), re.M)
    if len(expected) != len(set(expected)):
        raise SystemExit("Duplicate named theorem in the audit entry point.")
    output = lean(project, "env", "lean", entry.name)
    results = dict(AXIOMS.findall(output))
    if not expected or set(expected) != set(results):
        raise SystemExit("Missing or unexpected theorem audit output.\n" + output)
    sources = sorted(project.glob("*.lean"), key=lambda path: path.name)
    audit_all(project, [p.stem for p in sources if p.name != "lakefile.lean"])
    lines = ["Lean project verification", (project / "lean-toolchain").read_text().strip(),
             "lake build: passed", "lake env lean BlockingCurves.lean: passed",
             "All safe declarations and source-located unsafe declarations in all project modules: passed",
             "Allowed axioms: Classical.choice, Quot.sound, propext", "", "Selected results"]
    for name in expected:
        axioms = sorted(a.strip() for a in results[name].split(",") if a.strip())
        if set(axioms) - ALLOWED:
            raise SystemExit(f"Unexpected axioms for {name}: {axioms}")
        lines.append(f"{name}  [{', '.join(axioms)}]")
    lines.extend(["", "SHA-256 (UTF-8 source bytes with LF line endings)"])
    for path in sources + [project / "lake-manifest.json", project / "lean-toolchain"]:
        digest = hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()
        lines.append(f"{digest}  {path.name}")
    return "\n".join(lines) + "\n"


def build_modules_serially(project):
    """Keep only one local module's kernel reductions in memory on small runners."""
    paths = {p.stem: p for p in project.glob("*.lean") if p.name != "lakefile.lean"}
    dependencies = {}
    for name, path in sorted(paths.items()):
        imports = re.findall(r"^import\s+(\w+)(?:\s*$)", path.read_text(encoding="utf-8"), re.M)
        dependencies[name] = set(imports) & paths.keys()
    for name in TopologicalSorter(dependencies).static_order():
        print(f"Building {name}", flush=True)
        subprocess.run(["lake", "build", "+" + name], cwd=project, check=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=PROJECT)
    parser.add_argument("--write", action="store_true", help="refresh the verified record")
    parser.add_argument("--serial", action="store_true", help="prebuild local modules one at a time")
    args = parser.parse_args()
    if args.serial:
        build_modules_serially(args.project.resolve())
    verified = record(args.project.resolve())
    target = args.project / "verification.txt"
    if args.write:
        target.write_bytes(verified.encode("utf-8"))
    elif target.read_text(encoding="utf-8") != verified:
        raise SystemExit("Stale verification.txt. Review the changes and rerun with --write.")
    print("Verified all source hashes and theorem dependencies.")
