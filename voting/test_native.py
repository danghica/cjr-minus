"""Run checked-emitted Cangjie using the parent project's compiler setup."""
import importlib.util
import itertools
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("native_printer", ROOT.parent / "tests/native_printer.py")
native = importlib.util.module_from_spec(spec)
spec.loader.exec_module(native)


def reference(n, ballots):
    active = set(range(n))
    while active:
        choices = [next((c for c in row if c in active), None) for row in ballots]
        choices = [c for c in choices if c is not None]
        if not choices:
            return -1
        counts = {c: choices.count(c) for c in active}
        for c, count in counts.items():
            if 2 * count > len(choices):
                return c
        active.remove(min(active, key=lambda c: (counts[c], -c)))
    return -1


rankings = [list(p) for size in range(4) for p in itertools.permutations(range(3), size)]
profiles = [(0, []), (1, [[0], []]), (3, []), (3, [[], []])]
profiles += [(3, [a, b]) for a in rankings for b in rankings]
profiles += [(3, [[0], [0], [0], [1], [1], [2, 1], [2, 1]])]
profiles += [(5, [[4, 3, 2], [0, 1], [1, 2], [2, 3], [3, 2]])]
body = ["var ok = true"]
top_cases = 0
for index, (n, ballots) in enumerate(profiles):
    width = max(map(len, ballots), default=0)
    cells = [c for row in ballots for c in row + [-1] * (width - len(row))]
    p = f"p{index}"
    body.append(f"let {p} = unsafe {{ CPointer<Int64>(calloc(UIntNative({max(1,len(cells))}), UIntNative(8))) }}")
    body += [f"unsafe {{ ({p} + {i}).write({c}) }}" for i, c in enumerate(cells)]
    body.append(f"ok = (rankedChoice({n}, {len(ballots)}, {width}, {p}) == {reference(n, ballots)}) && ok")
    if index < 24 or index >= len(profiles)-2:
        for limit in sorted({0, min(1,n), n}):
            remaining = [row[:] for row in ballots]
            expected = []
            for _ in range(limit):
                winner = reference(n, remaining)
                if winner < 0:
                    break
                expected.append(winner)
                remaining = [[c for c in row if c != winner] for row in remaining]
            cursor = f'choices{index}_{limit}'
            body.append(f'var {cursor} = rankedChoices({n}, {len(ballots)}, {width}, {p}, {limit})')
            for winner in expected:
                body.append(f'ok = ({cursor}.nonempty && {cursor}.value == {winner}) && ok')
                body.append(f'{cursor} = {cursor}.next')
            body.append(f'ok = !{cursor}.nonempty && ok')
            top_cases += 1
    body += [f"ok = (unsafe {{ ({p} + {i}).read() }} == {c}) && ok" for i, c in enumerate(cells)]
    body.append(f"unsafe {{ free(CPointer<Unit>({p})) }}")
body.append("if (ok) { 0 } else { 1 }")
source = (ROOT / "ranked_choice.cj").read_text().split("main():", 1)[0]
source += "main(): Int64 {\n" + "\n".join(body) + "\n}\n"
with tempfile.TemporaryDirectory(prefix="ranked-choice-") as tmp:
    work = Path(tmp)
    compiler, env = native.toolchain(work)
    path = work / "test.cj"
    path.write_text(source)
    subprocess.run([str(compiler), str(path), "-o", str(work / "test")], env=env, check=True)
    subprocess.run([str(work / "test")], env=env, check=True)
    # These assertions are emitted from CJR expressions as well. Change only
    # main's declared result type so a failed assertion is an exit status of 1.
    guarded = (ROOT / "pareto_checks.cj").read_text()
    assert guarded.count("main(): Unit") == 1
    path.write_text(guarded.replace("main(): Unit", "main(): Int64"))
    subprocess.run([str(compiler), str(path), "-o", str(work / "guarded")], env=env, check=True)
    subprocess.run([str(work / "guarded")], env=env, check=True)
    monotonicity = (ROOT / "monotonicity_checks.cj").read_text()
    assert monotonicity.count("main(): Unit") == 1
    path.write_text(monotonicity.replace("main(): Unit", "main(): Int64"))
    subprocess.run([str(compiler), str(path), "-o", str(work / "monotonicity")], env=env, check=True)
    subprocess.run([str(work / "monotonicity")], env=env, check=True)
print(f"Passed {len(profiles)} native elections and ballot preservation checks.")
print(f"Passed {top_cases} native multi-choice limits, ordering, exhaustion and input-preservation checks.")
print("Passed a native guarded election and five injected guard results.")
print("Verified both native monotonicity counterexample results.")
