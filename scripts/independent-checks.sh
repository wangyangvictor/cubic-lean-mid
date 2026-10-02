#!/bin/sh
# Optional, slower verification. First complete scripts/check.sh.
# Requires Python 3, Git, Lake/Lean 4.26.0,
# and separately built, pinned checker repositories in CHECKER_TOOLS:
#   comparator fd5d5bcf14177b187f66d4502071268d877887c3 (Lean 4.35.0-rc3)
#   lean4export 66f1fb4bc256072069767fce52d39480e4524869
#   nanoda_lib 3a2407216ee84a75f9e1aead6803d0578be06ae7
# LEAN_EXPORTER_426 is the same pinned exporter built with Lean 4.26.0.
# LEAN_435 is the Lean 4.35.0-rc3 executable. Comparator's parser libraries
# must be built with that version. Supplied checker binaries are trusted
# build artifacts: their hashes and source pins are recorded in the receipt.
# Repository URLs and exact setup commands are also recorded in
# checks/checker-receipt.json. Build two copies of lean4export: one with
# Lean 4.26.0 for exporting proofs, and CHECKER_TOOLS/lean4export with
# Lean 4.35.0-rc3 for Comparator's parser. Source guards below check
# tracked Lean/Rust files (including staged edits) and reject non-ignored untracked
# Lean/Rust files. They do not prove binary/source correspondence.
# Example: CHECKER_TOOLS=/path/to/tools LEAN_EXPORTER_426=/path/to/exporter \
#          LEAN_435=/path/to/lean scripts/independent-checks.sh
# The deliberate admitted challenge is generated only in the audit output
# directory. It is never a production module. The script retains its logs
# and potentially large exports; no binaries/exports are shipped in this ZIP.
set -eu
cubic_check_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
export CUBIC_CHECK_ROOT="$cubic_check_root"
exec python3 - <<'PY'
from pathlib import Path
import collections, datetime, hashlib, json, os, re, subprocess

root = Path(os.environ['CUBIC_CHECK_ROOT']).resolve()
project = root / 'formalization/CubicTenVariables'
tools = Path(os.environ['CHECKER_TOOLS']).resolve()
exporter = Path(os.environ['LEAN_EXPORTER_426']).resolve()
lean435 = Path(os.environ['LEAN_435']).resolve()
nanoda = tools / 'nanoda_lib/target/release/nanoda_bin'
pins = {
    'comparator': 'fd5d5bcf14177b187f66d4502071268d877887c3',
    'lean4export': '66f1fb4bc256072069767fce52d39480e4524869',
    'nanoda_lib': '3a2407216ee84a75f9e1aead6803d0578be06ae7'}
out = Path(os.environ.get('CHECK_OUTPUT_DIR', str(root / 'checks' /
    ('independent-run-' + datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'))))).resolve()
if out == root / 'formalization' or root / 'formalization' in out.parents:
    raise RuntimeError('Audit output must be outside the production formalization directory')
out.mkdir(parents=True, exist_ok=False)

def sha(p):
    h = hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda: f.read(1048576), b''): h.update(b)
    return h.hexdigest()

def capture(command, cwd=project):
    return subprocess.check_output(command, cwd=cwd, text=True).strip()

def run(name, command, cwd=project, env=None, stdout=None, reject=None):
    print(name, flush=True)
    with (out / (name + '.log')).open('w') as log:
        if stdout:
            with stdout.open('wb') as stream:
                r = subprocess.run(command, cwd=cwd, env=env, stdout=stream, stderr=log)
        else:
            r = subprocess.run(command, cwd=cwd, env=env, stdout=log, stderr=subprocess.STDOUT)
    (out / (name + '.result.json')).write_text(json.dumps(
        dict(command=command, exit_code=r.returncode), indent=2) + '\n')
    if reject is None:
        if r.returncode != 0: raise RuntimeError(name + ' failed; see ' + str(out))
    elif r.returncode == 0 or reject not in (out / (name + '.log')).read_text():
        raise RuntimeError(name + ' did not reject for the required reason; see ' + str(out))

for repo, rev in pins.items():
    if capture(['git', '-C', str(tools / repo), 'rev-parse', 'HEAD']) != rev:
        raise RuntimeError('Wrong source revision for ' + repo)
    subprocess.run(['git', '-C', str(tools / repo), 'diff', 'HEAD', '--no-ext-diff', '--no-textconv',
        '--exit-code', '--', '*.lean', '*.rs'], check=True)
    untracked = capture(['git', '-C', str(tools / repo), 'ls-files', '--others', '--exclude-standard', '-z']).split('\0')
    if any(Path(p).suffix in ['.lean', '.rs'] for p in untracked if p):
        raise RuntimeError('Untracked Lean/Rust source in checker repository ' + repo)
for p in [exporter, lean435, nanoda]:
    if not p.is_file(): raise RuntimeError('Missing checker executable: ' + str(p))
if not re.search(r'\bversion 4\.26\.0(?=,|\s|\))', capture(['lake', 'env', 'lean', '--version'])):
    raise RuntimeError('The mathematical project must use Lean 4.26.0')
if not re.search(r'\bversion 4\.35\.0-rc3(?=,|\s|\))', capture([str(lean435), '--version'])):
    raise RuntimeError('Comparator requires Lean 4.35.0-rc3')
def source_inventory():
    return {str(p.relative_to(root)): sha(p) for p in sorted((root / 'formalization').rglob('*.lean'))
            if '.lake' not in p.parts and '.elan' not in p.parts}
sources = source_inventory()
script_path = root / 'scripts/independent-checks.sh'
script_sha256 = sha(script_path)
run('rehash_target_build', ['lake', '--rehash', '--no-build', 'build',
    'CubicTenVariables.Theorem11ReducedZetaInternalCurves'])

imports = '''import CubicTenVariables.Literature.ProjectiveMicrolocalCertificate
import CubicTenVariables.Literature.SmoothCubicWeil
import CubicTenVariables.Literature.ProperHyperplaneWeightDichotomy
import CubicTenVariables.Literature.AffinePlaneCurveWeil
import CubicTenVariables.Literature.CubicSurfaceZetaFactors
'''
statement = '''set_option autoImplicit false
noncomputable section
namespace CubicFormsMidIndependentAudit
open MvPolynomial CubicTenVariables
theorem main
    (microlocal : Literature.ProjectiveMicrolocalCertificate)
    (weil : Literature.SmoothCubicWeil)
    (dichotomy : Literature.ProperHyperplaneWeightDichotomy)
    (curveWeil : Literature.AffinePlaneCurveWeil)
    (zeta : Literature.CubicSurfaceZetaFactorBounds) :
    ∀ (n : ℕ), 10 ≤ n → ∀ F : MvPolynomial (Fin n) ℚ,
      F.IsHomogeneous 3 → ∃ x : Fin n → ℚ, x ≠ 0 ∧ eval x F = 0 :=
'''
(out / 'Challenge.lean').write_text(imports + statement + '  by sorry\nend CubicFormsMidIndependentAudit\n')
(out / 'Solution.lean').write_text('import CubicTenVariables.Theorem11ReducedZetaInternalCurves\n' + statement +
    '  CubicTenVariables.Theorem11ReducedZetaInternalCurves.main microlocal weil dichotomy curveWeil zeta\nend CubicFormsMidIndependentAudit\n')
(out / 'Mismatch.lean').write_text('import Mathlib.Logic.Basic\nnamespace CubicFormsMidIndependentAudit\ntheorem main : True := True.intro\nend CubicFormsMidIndependentAudit\n')
(out / 'CanonicalInit.lean').write_text('import Init\n')
primitives = ['Quot', 'Quot.mk', 'Quot.lift', 'Quot.ind', 'propext', 'Classical.choice', 'Quot.sound',
    'Nat.add', 'Nat.sub', 'Nat.mul', 'Nat.pow', 'Nat.gcd', 'Nat.div', 'Nat.mod', 'Nat.beq', 'Nat.ble',
    'Nat.land', 'Nat.lor', 'Nat.xor', 'Nat.shiftLeft', 'Nat.shiftRight', 'String.ofList', 'Char.ofNat',
    'List', 'eagerReduce', 'Nat', 'String', 'String.mk', 'Char', 'optParam', 'autoParam', 'semiOutParam', 'outParam']
env426 = os.environ.copy()
env426['LEAN_PATH'] = str(out) + os.pathsep + capture(['lake', 'env', 'printenv', 'LEAN_PATH'])
env426['PATH'] = capture(['lake', 'env', 'printenv', 'PATH'])
for module in ['Challenge', 'Solution', 'Mismatch', 'CanonicalInit']:
    run('compile_' + module, ['lake', 'env', 'lean', '-DautoImplicit=false', '-DrelaxedAutoImplicit=false',
        '-R', str(out), '-o', str(out / (module + '.olean')), str(out / (module + '.lean'))])
    targets = primitives + ([] if module == 'CanonicalInit' else ['CubicFormsMidIndependentAudit.main'])
    run('export_' + module, [str(exporter), module, '--', *targets], env=env426,
        stdout=out / (module + '.ndjson'))

cfg = dict(challenge_module='Challenge', solution_module='Solution',
    theorem_names=['CubicFormsMidIndependentAudit.main'], definition_names=[],
    permitted_axioms=['propext', 'Classical.choice', 'Quot.sound'])
(out / 'comparator.json').write_text(json.dumps(cfg, indent=2) + '\n')
driver = '''import Main
def runAudit (solutionPath : String) : IO Unit := do
  let cfg : Comparator.Config ← IO.ofExcept (Lean.fromJson? (← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile CONFIG))))
  let golden ← Export.parseStream (← Comparator.stringStream (← IO.FS.readFile GOLDEN))
  let challengeText ← IO.FS.readFile CHALLENGE
  let challenge ← Export.parseStream (← Comparator.stringStream challengeText)
  IO.ofExcept <| Comparator.compareAt golden challenge #[`propext, `Classical.choice, `Quot.sound] #[] PRIMITIVES
  Comparator.M.run (Comparator.verifyMatch challengeText (← IO.FS.readFile solutionPath)) cfg
  IO.println "Canonical-core comparison and Comparator verification passed."
#eval runAudit SOLUTION
'''
for token, value in {'CONFIG': json.dumps(str(out / 'comparator.json')),
    'GOLDEN': json.dumps(str(out / 'CanonicalInit.ndjson')),
    'CHALLENGE': json.dumps(str(out / 'Challenge.ndjson')),
    'PRIMITIVES': '#[' + ', '.join('`' + n for n in primitives) + ']'}.items(): driver = driver.replace(token, value)
env435 = os.environ.copy()
env435['PATH'] = str(lean435.parent) + os.pathsep + env435.get('PATH', '')
env435['LEAN_PATH'] = os.pathsep.join(str(tools / p) for p in
    ['comparator/.lake/build/lib/lean', 'lean4export/.lake/build/lib/lean'])
for name, solution, rejection in [('comparator_main', 'Solution', None),
    ('comparator_sorry_control', 'Challenge', "Illegal axiom detected: 'sorryAx'"),
    ('comparator_mismatch_control', 'Mismatch', 'Challenge and solution theorem statement do not match:')]:
    p = out / (name + '.lean')
    p.write_text(driver.replace('SOLUTION', json.dumps(str(out / (solution + '.ndjson')))))
    run(name, [str(lean435), str(p)], cwd=out, env=env435, reject=rejection)
if 'Canonical-core comparison and Comparator verification passed.' not in (out / 'comparator_main.log').read_text():
    raise RuntimeError('Missing Comparator success certificate')

for name, module, rejection in [('nanoda_main', 'Solution', None),
    ('nanoda_sorry_control', 'Challenge', 'unpermitted axiom "sorryAx"')]:
    pretty = out / (name + '.pretty.txt'); pretty.touch()
    p = out / (name + '.json')
    p.write_text(json.dumps(dict(export_file_path=str(out / (module + '.ndjson')),
        permitted_axioms=cfg['permitted_axioms'], unpermitted_axiom_hard_error=True,
        unsafe_permit_all_axioms=False, nat_extension=True, string_extension=True,
        num_threads=1, print_success_message=True, pp_declars=[], pp_output_path=str(pretty), pp_to_stdout=False), indent=2) + '\n')
    run(name, [str(nanoda), str(p)], cwd=out, reject=rejection)

names = {0: ''}; axioms = []; counts = collections.Counter(); targets = {}; metadata = None
with (out / 'Solution.ndjson').open('rb') as f:
    for raw in f:
        if raw.startswith(b'{"ie"') or raw.startswith(b'{"il"'): continue
        o = json.loads(raw)
        if 'in' in o:
            v = o.get('str', o.get('num')); pre = names[v['pre']]
            names[o['in']] = pre + ('.' if pre else '') + str(v.get('str', v.get('i', v.get('num'))))
        elif 'meta' in o: metadata = o['meta']
        elif 'ie' not in o and 'il' not in o:
            for kind, v in o.items():
                counts[kind] += 1
                if kind == 'axiom': axioms.append(names[v['name']])
                if isinstance(v, dict) and names.get(v.get('name')) in [
                    'CubicTenVariables.Theorem11ReducedZetaInternalCurves.main', 'CubicFormsMidIndependentAudit.main']:
                    targets[names[v['name']]] = kind
if set(axioms) != set(cfg['permitted_axioms']): raise RuntimeError('Unexpected exported axiom set')
if len(targets) != 2 or set(targets.values()) != {'thm'}: raise RuntimeError('Missing actual target theorem')
if metadata['lean']['version'] != '4.26.0' or metadata['exporter']['version'] != '3.1.0':
    raise RuntimeError('Wrong proof compiler/exporter version')
if source_inventory() != sources:
    raise RuntimeError('Mathematical source inventory changed during checking')
if sha(script_path) != script_sha256:
    raise RuntimeError('Independent-checker script changed during checking')
match = re.search(r'Checked (\d+) declarations with no errors', (out / 'nanoda_main.log').read_text())
if not match: raise RuntimeError('Missing Nanoda success certificate')
receipt = dict(status='PASSED', target='CubicTenVariables.Theorem11ReducedZetaInternalCurves.main',
    explicit_literature_parameters=5, literal_conclusion='Every homogeneous rational cubic in n >= 10 variables has a nonzero rational zero.',
    nanoda_checked_declarations=int(match.group(1)), permitted_axioms=sorted(axioms),
    source_pins=pins, proof_export_sha256=sha(out / 'Solution.ndjson'),
    source_sha256=sources, verification_script_sha256=script_sha256, checker_binary_sha256={p.name: sha(p) for p in [exporter, lean435, nanoda]},
    canonical_init_comparison=True, admission_controls_rejected=True, statement_mismatch_control_rejected=True,
    target_build_check='Lake --rehash --no-build validates the existing prerequisite build; this script does not silently launch a new unbounded build.',
    limits=['The five explicit propositions are assumed; their truth and literature fidelity are not verified by kernels.',
        'Supplied checker binaries are trusted build artifacts; repository source pins and binary hashes are recorded.',
        'No hardened adversarial operating-system sandbox, and no guarantee that either kernel has zero bugs.'])
(out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
print('PASSED; retained evidence at ' + str(out))
PY
