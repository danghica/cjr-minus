# Upstream Cangjie golden files

These eight files are copied unchanged from `example/misc/extracted/` in
https://github.com/danghica/cjr-core at commit
`c663bd896f92d4646901786642af823c6a278bed`. Their SHA-256 fingerprints and the
printer source fingerprint are recorded in `upstream.json`. `TestPrinter.lean`
compares generated source after removing only the first-line generator banner.
They are test references, not the generated Lean output. Use `emit` for checked
source, including the strict-conjunction correction.
