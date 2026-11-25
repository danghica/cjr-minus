#!/usr/bin/env python3
"""Compile and execute Lean-emitted Cangjie using result-checking native mains.
Run `lake exe test-printer` and `lake exe test-linked-list`, and `lake exe test-iterator`, and `lake exe test-mergesort` first. Requires Cangjie 1.0.5 (CJC overrides discovery).
"""
import argparse
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def toolchain(work):
    candidates = [os.environ.get("CJC"), shutil.which("cjc"),
                  str(Path.home() / "cangjiebuild/software/cangjie/bin/cjc")]
    compiler = next((Path(c) for c in candidates if c and Path(c).is_file()), None)
    if compiler is None:
        raise RuntimeError("Cangjie compiler not found; set CJC to the Cangjie 1.0.5 compiler")
    home = Path(os.environ.get("CANGJIE_HOME", str(compiler.parent.parent)))
    env = dict(os.environ, CANGJIE_HOME=str(home))
    if platform.system() == "Darwin":
        env["DYLD_LIBRARY_PATH"] = str(home / "runtime/lib/darwin_aarch64_cjnative")
        if not env.get("SDKROOT"):
            sdk = Path(subprocess.check_output(["xcrun", "--show-sdk-path"], text=True).strip())
            # Cangjie 1.0.5's linker predates newer macOS TAPI target spellings.
            # Adapt only a temporary copy, as the upstream runtime harness does.
            compat = work / "sdk"
            for stub in (sdk / "usr/lib").rglob("*.tbd"):
                if stub.is_symlink():
                    continue
                target = compat / stub.relative_to(sdk)
                target.parent.mkdir(parents=True, exist_ok=True)
                text = re.sub(r"arm64e\.x1-[\w]+\s*,?\s*", "", stub.read_text())
                text = re.sub(r",\s*\]", " ]", text).replace("arm64e-", "arm64-")
                target.write_text(text)
            link = compat / "usr/lib/libSystem.tbd"
            if not link.exists():
                link.symlink_to("libSystem.B.tbd")
            env["SDKROOT"] = str(compat)
    version = subprocess.check_output([str(compiler), "--version"], env=env, text=True).strip()
    if "1.0.5" not in version:
        raise RuntimeError(f"Cangjie 1.0.5 required, found {version}")
    print(version, flush=True)
    return compiler, env


ALLOC = "unsafe { CPointer<Int64>(calloc(UIntNative(1), UIntNative(8))) }"
FREE = "unsafe { free(CPointer<Unit>(p)); free(CPointer<Unit>(q)) }"
HARNESSES = {
    "arith": "if (sumOne() == 1 && multiply(-7, 6) == -42 && divide(-7, 3) == -2) { 0 } else { 1 }",
    "struct_upd": "if (bump() == 1 && bumpKeep() == 0) { 0 } else { 1 }",
    "cell": "cell()\n0",
    "class_upd": "if (classBump() == 0) { 0 } else { 1 }",
    "vtable": "if (run() == 1) { 0 } else { 1 }",
    "factorial": "if (fact(5) == 120) { 0 } else { 1 }",
    "strict_and": "if (strictAnd() == 1) { 0 } else { 1 }",
    "counter": "if (runCounter() == 5) { 0 } else { 1 }",
    "raw": "if (runRaw() == 42) { 0 } else { 1 }",
    "method": "let c = Counter(0)\nc.inc()\nif (c.value == 1) { 0 } else { 1 }",
    "self_reference": "let n = Node(false, 0, None)\nlet before = n.next.value\nn.next = Node(true, 7, None)\nif (before == 0 && n.next.value == 7) { 0 } else { 1 }",
    "sum_block": f"let p = {ALLOC}\nunsafe {{ p.write(4) }}\nlet answer = sumAt(p)\nunsafe {{ free(CPointer<Unit>(p)) }}\nif (answer == 4) {{ 0 }} else {{ 1 }}",
    "swap": f"let p = {ALLOC}\nlet q = {ALLOC}\nunsafe {{ p.write(1); q.write(2) }}\nswap(p, q)\nlet ok = unsafe {{ p.read() == 2 && q.read() == 1 }}\n{FREE}\nif (ok) {{ 0 }} else {{ 1 }}",
    "frame_call": f"let p = {ALLOC}\nlet q = {ALLOC}\nunsafe {{ q.write(3) }}\nlet answer = frameCall(p, q)\nlet updated = unsafe {{ p.read() }}\n{FREE}\nif (answer == 3 && updated == 9) {{ 0 }} else {{ 1 }}",
    "linked_list": """
let a = cons(1, cons(2, cons(3, empty())))
let b = cons(-4, cons(5, empty()))
let ab = append(a, b)
let r = reverse(ab)
var ok = length(a) == 3 && length(ab) == 5 && length(r) == 5
ok = ok && head(a) == 1 && head(tail(a)) == 2
ok = ok && head(r) == 5 && head(tail(r)) == -4
ok = ok && isEmpty(empty()) && !isEmpty(a)
let c = cons(9, empty())
var left = append(append(a, b), c)
var right = append(a, append(b, c))
while (!isEmpty(left) && !isEmpty(right)) {
    ok = ok && head(left) == head(right)
    left = tail(left)
    right = tail(right)
}
ok = ok && isEmpty(left) && isEmpty(right)
var twice = reverse(reverse(a))
var original = a
while (!isEmpty(original) && !isEmpty(twice)) {
    ok = ok && head(original) == head(twice)
    original = tail(original)
    twice = tail(twice)
}
ok = ok && isEmpty(original) && isEmpty(twice)
var revAppend = reverse(append(a, b))
var appendRev = append(reverse(b), reverse(a))
while (!isEmpty(revAppend) && !isEmpty(appendRev)) {
    ok = ok && head(revAppend) == head(appendRev)
    revAppend = tail(revAppend)
    appendRev = tail(appendRev)
}
ok = ok && isEmpty(revAppend) && isEmpty(appendRev)
// Input persistence: append and reverse must not change either source list.
ok = ok && head(a) == 1 && length(a) == 3 && head(b) == -4 && length(b) == 2
if (ok) { 0 } else { 1 }
""",

    "list_iterator": """
let xs = cons(11, cons(-2, cons(11, empty())))
let it = iterator(xs)
var option = it.next()
var count: Int64 = 0
var total: Int64 = 0
var ok = true
while (option.isSome()) {
    let node = option.getOrThrow()
    if (count == 0) { ok = ok && node.value == 11 }
    if (count == 1) { ok = ok && node.value == -2 }
    if (count == 2) { ok = ok && node.value == 11 }
    count = count + 1
    total = total + node.value
    option = it.next()
}
ok = ok && count == 3 && total == 20
ok = ok && !it.next().isSome() && !it.next().isSome()
ok = ok && !it.cursor.nonempty && length(it.list) == 3 && head(it.list) == 11
ok = ok && length(xs) == 3 && head(tail(xs)) == -2
let none = iterator(empty())
ok = ok && !none.next().isSome() && !none.next().isSome()
let left = iterator(xs)
let right = iterator(xs)
ok = ok && left.next().getOrThrow().value == 11
ok = ok && left.next().getOrThrow().value == -2
ok = ok && right.next().getOrThrow().value == 11
ok = ok && right.cursor.value == -2 && left.cursor.value == 11
if (ok) { 0 } else { 1 }
""",

    "mergesort": """
let input = cons(5, cons(-1, cons(3, cons(3, cons(0, cons(2, empty()))))))
let output = mergeSort(input)
var actual = output
var expected = cons(-1, cons(0, cons(2, cons(3, cons(3, cons(5, empty()))))))
var ok = length(input) == 6 && length(output) == 6
while (!isEmpty(actual) && !isEmpty(expected)) {
    ok = ok && head(actual) == head(expected)
    actual = tail(actual)
    expected = tail(expected)
}
ok = ok && isEmpty(actual) && isEmpty(expected)
ok = ok && head(input) == 5 && head(tail(input)) == -1
let halves = splitList(input)
ok = ok && length(halves.left) == 3 && length(halves.right) == 3
ok = ok && head(halves.left) == 5 && head(tail(halves.left)) == 3
ok = ok && head(halves.right) == -1 && head(tail(halves.right)) == 3
ok = ok && isEmpty(mergeSort(empty()))
let one = mergeSort(cons(-7, empty()))
ok = ok && head(one) == -7 && length(one) == 1
var descending = empty()
var i: Int64 = 0
while (i < 32) {
    descending = cons(i, descending)
    i = i + 1
}
var ascending = mergeSort(descending)
i = 0
while (!isEmpty(ascending)) {
    ok = ok && head(ascending) == i
    i = i + 1
    ascending = tail(ascending)
}
ok = ok && i == 32 && head(descending) == 31 && length(descending) == 32
var equal = empty()
i = 0
while (i < 16) { equal = cons(7, equal); i = i + 1 }
var sortedEqual = mergeSort(equal)
ok = ok && length(sortedEqual) == 16
while (!isEmpty(sortedEqual)) {
    ok = ok && head(sortedEqual) == 7
    sortedEqual = tail(sortedEqual)
}
let merged = mergeLists(cons(0, cons(2, cons(2, empty()))), cons(-1, cons(2, cons(3, empty()))))
actual = merged
expected = cons(-1, cons(0, cons(2, cons(2, cons(2, cons(3, empty()))))))
while (!isEmpty(actual) && !isEmpty(expected)) {
    ok = ok && head(actual) == head(expected)
    actual = tail(actual)
    expected = tail(expected)
}
ok = ok && isEmpty(actual) && isEmpty(expected)
if (ok) { 0 } else { 1 }
""",

}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-dir", type=Path, default=ROOT / ".lake/printer-output")
    parser.add_argument("--only", choices=list(HARNESSES), help="Validate a single emitted program")
    args = parser.parse_args()
    harnesses = HARNESSES if args.only is None else {args.only: HARNESSES[args.only]}
    with tempfile.TemporaryDirectory(prefix="cjr-lean-native-") as temporary:
        work = Path(temporary)
        compiler, env = toolchain(work)
        for name, body in harnesses.items():
            source = (args.source_dir / f"{name}.cj").read_text()
            if "/* unsupported:" in source:
                raise RuntimeError(f"Unsupported source: {name}")
            # First compile and run the emitted file unchanged.
            original = work / f"{name}_original"
            subprocess.run([str(compiler), str(args.source_dir.resolve() / f"{name}.cj"), "-o", str(original)],
                           cwd=work, env=env, check=True, capture_output=True, text=True)
            subprocess.run([str(original)], cwd=work, env=env, check=True, timeout=30)
            # Then replace only main to assert observable results of generated functions.
            prefix, sep, _ = source.rpartition("\nmain(): Unit {")
            if not sep:
                raise RuntimeError(f"Missing main: {name}")
            path = work / f"{name}_assert.cj"
            path.write_text(prefix + "\nmain(): Int64 {\n" + body + "\n}\n")
            binary = work / f"{name}_assert"
            subprocess.run([str(compiler), str(path), "-o", str(binary)], cwd=work, env=env,
                           check=True, capture_output=True, text=True)
            subprocess.run([str(binary)], cwd=work, env=env, check=True, timeout=30)
            print(f"PASS {name}: original and result assertions", flush=True)
    print(f"All {len(harnesses)} emitted programs compiled and executed successfully.")


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as error:
        print(error.stdout or "")
        print(error.stderr or "")
        raise
