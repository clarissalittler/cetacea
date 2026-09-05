#!/usr/bin/env python3
"""Generate/check browser fixtures against fresh native CLI grading results."""
import argparse
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'web/tests/assignment-parity.json'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    # Downloadable browser tasks must carry exactly the checked native policy.
    for archive, manifest in [
        ('docs/book/hol-code/ch22.ctea-task', 'docs/book/hol-code/ch22-solutions.ctea-assignment'),
        ('docs/hol/pilot/pigeonhole_client.ctea-task', 'docs/hol/pilot/pigeonhole_client.ctea-assignment'),
        ('docs/book/hol-code/ch17.ctea-task', 'docs/book/hol-code/ch17-solutions.ctea-assignment'),
        ('docs/book/hol-code/ch21.ctea-task', 'docs/book/hol-code/ch21-solutions.ctea-assignment'),
        ('docs/book/hol-code/ch20.ctea-task', 'docs/book/hol-code/ch20-solutions.ctea-assignment'),
        ('docs/book/hol-code/ch19.ctea-task', 'docs/book/hol-code/ch19-solutions.ctea-assignment'),
        ('docs/book/hol-code/ch18.ctea-task', 'docs/book/hol-code/ch18-solutions.ctea-assignment'),
    ]:
        expected_task = dict(format='cetacea-assignment', version=1, path=manifest,
                             source=(ROOT / manifest).read_text(), files=[])
        assert json.loads((ROOT / archive).read_text()) == expected_task, f'{archive}: task differs from native policy'
    subprocess.run(['cargo', 'build', '-p', 'cetacea_cli'], cwd=ROOT, check=True)
    fixtures = []

    def record(name, root, source, path, manifest, expected, native_root, native_manifest, files=None):
        try:
            run = subprocess.run([str(ROOT / 'target/debug/cetacea_cli'), '--json', '--assignment', str(native_manifest), str(native_root)], cwd=ROOT, capture_output=True, text=True, timeout=30)
        except subprocess.TimeoutExpired as error:
            raise RuntimeError(f'{name}: native grading exceeded the 30-second fixture limit') from error
        if run.returncode not in (0, 1):
            raise RuntimeError(f'{name}: checker failed: {run.stderr}')
        result = json.loads(run.stdout)
        assert result['ok'] == expected, (name, result)
        assert (run.returncode == 0) == expected, (name, run.returncode)
        relative_parent = str(Path(root).parent)
        virtual_prefix = '' if relative_parent == '.' else relative_parent + '/'
        def declaration(value):
            native_prefix = str(native_root.parent) + '/'
            return virtual_prefix + value[len(native_prefix):] if value.startswith(native_prefix) else value
        violations = sorted({(declaration(v['declaration']), v['kind']) for v in result['hol_policy_violations']})
        certified = result['hol_shadow']['matches'] and not any(d['severity'] == 'error' for d in result['diagnostics'])
        fixtures.append(dict(name=name, project=dict(root=root, files=[dict(path=root, source=source)]), assignment=dict(path=path, source=manifest, files=files or []), expected=dict(accepted=expected, certified=certified, violations=violations)))

    cases = [('docs/hol/pilot/pigeonhole_client.ctea', 'docs/hol/pilot/pigeonhole_client.ctea-assignment', True)]
    for chapter in range(13, 23):
        source = f'docs/book/hol-code/ch{chapter}-solutions.ctea'
        cases.append((source, source + '-assignment', True))
        if chapter in (14, 15):
            cases.append((source, source.replace('.ctea', '-fol.ctea-assignment'), False))
    cases.append(('docs/book/hol-code/ch17-exercises.ctea', 'docs/book/hol-code/ch17-solutions.ctea-assignment', False))
    cases.append(('docs/book/hol-code/ch18-exercises.ctea', 'docs/book/hol-code/ch18-solutions.ctea-assignment', False))
    cases.append(('docs/book/hol-code/ch19-exercises.ctea', 'docs/book/hol-code/ch19-solutions.ctea-assignment', False))
    cases.append(('docs/book/hol-code/ch20-exercises.ctea', 'docs/book/hol-code/ch20-solutions.ctea-assignment', False))
    cases.append(('docs/book/hol-code/ch21-exercises.ctea', 'docs/book/hol-code/ch21-solutions.ctea-assignment', False))
    cases.append(('docs/book/hol-code/ch22-exercises.ctea', 'docs/book/hol-code/ch22-solutions.ctea-assignment', False))
    for root, path, expected in cases:
        name = path if expected else f'{path} rejects {root}'
        record(name, root, (ROOT / root).read_text(), path, (ROOT / path).read_text(), expected, ROOT / root, ROOT / path)

    base = "version = 1\nprofile = 'prop'\n"
    proof = 'theorem answer : True := by\n  trivial\n'
    variants = [
        ('simple', proof, base + "required_theorem.answer = 'True'\n", True),
        ('wrong-signature', proof, base + "required_theorem.answer = 'False'\n", False),
        ('missing-theorem', proof, base + "required_theorem.missing = 'True'\n", False),
        ('incomplete', 'theorem answer : True := by\n  sorry\n', base, False),
        ('new-axiom', 'axiom answer : True\n', base, False),
        ('classical-denied', 'mode classical\ntheorem answer (P : Prop) : P \\/ not P := by\n  by_cases h : P\n  left\n  exact h\n  right\n  exact h\n', base, False),
        ('missing-import', proof, base + "required_imports = ['std/hol/list@1']\n", False),
        ('forbidden-import', 'import std/hol/list@1 as L\n' + proof, base + 'allowed_imports = []\n', False),
    ]
    arithmetic_policy = "version = 1\nprofile = 'hol'\n"
    modular_square = (ROOT / 'docs/hol/examples/modular_square.ctea').read_text()
    modular_policy = "version = 1\nprofile = 'fol+induction'\nallowed_imports = ['builtin:std/modular.ctea', 'builtin:std/nat.ctea', 'builtin:std/eq.ctea']\n"
    variants.append(('concrete-modular-square', modular_square, modular_policy, True))
    variants.append(('concrete-modular-square-wrong', modular_square.replace('M.ModEq(12, mul(27, 27), mul(3, 3))', 'M.ModEq(12, mul(27, 27), 8)'), modular_policy, False))
    variants.extend([
        ('concrete-square', 'theorem square : mul(27, 27) = 729 := by\n  refl\n', arithmetic_policy, True),
        ('concrete-square-wrong', 'theorem square : mul(27, 27) = 728 := by\n  refl\n', arithmetic_policy, False),
    ])
    variants.extend([
        ('failed-proof', 'theorem answer : False := by\n  trivial\n', base, False),
        ('local-axiom-cannot-be-whitelisted', 'axiom answer : True\n', base + "allowed_axioms = ['answer']\n", False),
    ])
    selected = (ROOT / 'docs/hol/examples/selected_contributions.ctea').read_text()
    selected_imports = ['builtin:std/hol/counting.ctea', 'builtin:std/hol/finite_weighted_sums.ctea', 'builtin:std/hol/sums.ctea', 'builtin:std/hol/weighted_sums.ctea', 'builtin:std/nat.ctea', 'std/hol/cardinality@1', 'std/hol/list@1']
    selected_policy = "version = 1\nprofile = 'hol'\nallowed_imports = " + json.dumps(selected_imports) + "\n"
    variants.append(('selected-weighted-evidence', selected, selected_policy, True))
    wrong_selected = selected + "\ntheorem wrong : S.sum(C.map(contribution, C.cons(outside, C.nil))) = mul(C.length(C.cons(outside, C.nil)), 2) := by\n  apply W.sum_map_constant_on {A := Item; f := contribution; xs := C.cons(outside, C.nil); k := 2}\n  intro x\n  intro member\n  refl\n"
    variants.append(('selected-weighted-evidence-missing', wrong_selected, selected_policy, False))
    reordered = (ROOT / 'docs/hol/examples/reordered_totals.ctea').read_text()
    reordered_imports = [name for name in selected_imports if name != 'builtin:std/hol/finite_weighted_sums.ctea'] + ['builtin:std/hol/weighted_enumerations.ctea']
    reordered_policy = "version = 1\nprofile = 'hol'\nallowed_imports = " + json.dumps(reordered_imports) + "\n"
    variants.append(('reordered-weighted-enumeration', reordered, reordered_policy, True))
    duplicate = reordered + "\ntheorem wrong : S.sum(C.map(weight, C.cons(low, forward))) = S.sum(C.map(weight, forward)) := by\n  apply E.sum_same_members {A := Vertex; f := weight; xs := C.cons(low, forward)} forward\n  finite\n"
    variants.append(('reordered-weighted-enumeration-duplicate', duplicate, reordered_policy, False))
    endpoints = (ROOT / 'docs/hol/examples/endpoint_contributions.ctea').read_text()
    endpoint_imports = reordered_imports + ['builtin:std/hol/endpoint_sums.ctea']
    endpoint_policy = "version = 1\nprofile = 'hol'\nallowed_imports = " + json.dumps(endpoint_imports) + "\n"
    variants.append(('generic-endpoint-incidences', endpoints, endpoint_policy, True))
    loop_case = endpoints.split('theorem loop_edge_total', 1)[1].split('-- Excluding', 1)[0]
    bad_loop = endpoints + '\ntheorem wrong' + loop_case.replace('loop_incidence', 'home_end')
    variants.append(('generic-endpoint-incidences-bad-loop', bad_loop, endpoint_policy, False))
    matrix = (ROOT / 'docs/hol/examples/double_counting.ctea').read_text()
    matrix_imports = ['std/hol/matrix@1', 'std/hol/list@1', 'std/hol/cardinality@1', 'builtin:std/hol/double_counting.ctea', 'builtin:std/hol/weighted_sums.ctea', 'builtin:std/hol/sums.ctea', 'builtin:std/nat.ctea']
    matrix_policy = "version = 1\nprofile = 'hol'\nallowed_imports = " + json.dumps(matrix_imports) + "\n"
    variants.append(('generic-double-counting', matrix, matrix_policy, True))
    wrong_matrix = matrix + "\ntheorem wrong : M.columns_total(signups, days, subjects) = 20 := by\n  rewrite <- totals_agree\n  exact by_day\n"
    variants.append(('generic-double-counting-wrong-total', wrong_matrix, matrix_policy, False))
    handshake = (ROOT / 'docs/hol/examples/handshake.ctea').read_text()
    handshake_imports = sorted(set(matrix_imports + endpoint_imports + ['builtin:std/hol/handshake.ctea']))
    handshake_policy = "version = 1\nprofile = 'hol'\nallowed_imports = " + json.dumps(handshake_imports) + "\n"
    variants.append(('generic-handshake', handshake, handshake_policy, True))
    variants.append(('generic-handshake-loop-counted-once', handshake.replace('| home => 4', '| home => 3'), handshake_policy, False))
    recurrences = (ROOT / 'docs/hol/examples/recurrences.ctea').read_text()
    probability = (ROOT / 'docs/hol/examples/probability_counts.ctea').read_text()
    probability_policy = "version = 1\nprofile = 'hol'\nallowed_imports = ['builtin:std/hol/probability_counts.ctea', 'builtin:std/hol/weighted_sums.ctea', 'builtin:std/hol/sums.ctea', 'builtin:std/nat.ctea', 'std/hol/cardinality@1', 'std/hol/list@1']\n"
    variants.append(('finite-probability-counts', probability, probability_policy, True))
    variants.append(('finite-probability-lost-ticket', probability.replace('S.sum(C.map(first_head, tickets)) = 3', 'S.sum(C.map(first_head, tickets)) = 2'), probability_policy, False))
    recurrence_policy = "version = 1\nprofile = 'hol'\nallowed_imports = ['builtin:std/hol/recurrences.ctea', 'builtin:std/nat.ctea']\n"
    variants.append(('recurrences-and-named-functions', recurrences, recurrence_policy, True))
    variants.append(('recurrences-wrong-update', recurrences.replace('| succ k rec => add(3, rec)', '| succ k rec => add(4, rec)'), recurrence_policy, False))
    for name, source, manifest, _ in list(variants):
        permission = {'incomplete': 'allow_incomplete', 'new-axiom': 'allow_new_axioms', 'classical-denied': 'allow_classical'}.get(name)
        if permission:
            variants.append((name + '-permitted', source, manifest + permission + ' = true\n', True))
            for unrelated in ['allow_extensionality', 'allow_choice']:
                variants.append((name + '-' + unrelated, source, manifest + unrelated + ' = true\n', False))
    with tempfile.TemporaryDirectory(prefix='cetacea-browser-parity-') as temporary:
        directory = Path(temporary)
        for name, source, manifest, expected in variants:
            source_file = directory / 'main.ctea'
            task_file = directory / 'task.ctea-assignment'
            source_file.write_text(source)
            task_file.write_text(manifest)
            record(name, 'main.ctea', source, 'task.ctea-assignment', manifest, expected, source_file, task_file)
        grant_source = 'import helper.ctea as H\ntheorem answer : True := by\n  exact H.helper\n'
        grant_manifest = base + "required_imports = ['helper.ctea']\nallowed_theorems = ['helper.ctea::helper']\nrequired_theorem.answer = 'True'\n"
        for name, helper, expected in [
            ('pinned-grant', 'theorem helper : True := by\n  trivial\n', True),
            ('axiom-tainted-grant', 'axiom helper : True\n', False),
            ('incomplete-grant', 'theorem helper : True := by\n  sorry\n', False),
        ]:
            source_file.write_text(grant_source)
            task_file.write_text(grant_manifest)
            (directory / 'helper.ctea').write_text(helper)
            record(name, 'main.ctea', grant_source, 'task.ctea-assignment', grant_manifest, expected,
                   source_file, task_file, [dict(path='helper.ctea', source=helper)])
        helper = 'import other.ctea as O\ntheorem helper : True := by\n  exact O.other\n'
        other = 'theorem other : True := by\n  trivial\n'
        (directory / 'helper.ctea').write_text(helper)
        (directory / 'other.ctea').write_text(other)
        source_file.write_text(grant_source)
        for name, allowed, expected in [('transitive-import-denied', False, False), ('transitive-import-permitted', True, True)]:
            manifest = grant_manifest + ("allowed_imports = ['helper.ctea', 'other.ctea']\n" if allowed else '')
            task_file.write_text(manifest)
            record(name, 'main.ctea', grant_source, 'task.ctea-assignment', manifest, expected, source_file, task_file,
                   [dict(path='helper.ctea', source=helper), dict(path='other.ctea', source=other)])
    rendered = json.dumps(fixtures, indent=2, ensure_ascii=False) + '\n'
    if args.check:
        if not OUTPUT.exists() or OUTPUT.read_text() != rendered:
            raise SystemExit('Browser assignment fixtures are stale; run scripts/browser_assignment_parity.py')
    else:
        OUTPUT.write_text(rendered)
    print(f'{len(fixtures)} native assignment parity cases verified')


if __name__ == '__main__':
    main()
