# extractor

`trust-extract` reads a compiled Lean project and writes a **dataset** (S2, `ltb-dataset/2`, in
[specs](https://github.com/LeanTrustBuilders/specs)): its declarations with their keys (S1), their
dependencies under four notions, and facets such as docstrings, source locations, statements and
annotations. It also checks a dataset with Lean's kernel (`check`) and analyzes well-definedness
(`welldefined`).

It is the only tool of the [LeanTrustBuilders](https://github.com/LeanTrustBuilders) suite that reads
`.olean` files; everything downstream reads the dataset and needs no Lean. It is built on
[MeaningGraph](https://github.com/LeanTrustBuilders/meaning-graph) (dependencies and hashes),
[TrustAnnotations](https://github.com/LeanTrustBuilders/annotations) and
[WellDefined](https://github.com/LeanTrustBuilders/well-defined).

## Use

Inside the project, once it is built:

```bash
lake env /path/to/trust-extract extract --root MyProject --repo owner/name --out dataset
```

A `.olean` file can only be read by the Lean that wrote it, so the extractor is released per
toolchain: `v<version>-lean-<toolchain>`, e.g. `v0.10.0-lean-v4.35.0-rc2`. Take the newest release
whose tag ends with your project's toolchain. `trust-extract --help` lists every option.

**In GitHub Actions**, once the library is built:

```yaml
- uses: LeanTrustBuilders/extractor/extract@main
  with:
    root: MyProject
    repo: owner/name
    directory: path/to/the/checkout      # default: .
    args: --parts 4                      # more arguments for `trust-extract extract`
    check: meaning                       # optional: the kernel check (`meaning term` for a small library)
    welldefined: true                    # optional: the well-definedness facet
    publish: dataset-${{ steps.commit.outputs.sha12 }}   # optional: publish as a release
```

It installs the newest release for the library's toolchain, extracts, adds the `attributes` facet,
runs the optional steps, and publishes the dataset as a release of the
repository running the workflow, where evidence-store and referee-site look for it.
`LeanTrustBuilders/extractor/setup@main` only installs the release (outputs `bin`, `scripts`, `tag`,
and `toolchains`: those that have one).

**Extract from a clean build.** The extractor cannot tell whether `.olean` files are consistent with
each other, and a build directory that went through several commits can hold a module compiled
against an older version of an import. For a dataset others will use, start from an empty
`.lake/build`: fetch the project's cache, then build what it lacks.

**Modules that do not build.** `--skip-module M` (repeatable) or `--skip-modules-file FILE` leaves
them out, with every module importing them. The dataset lists them under `library.unavailable`, so a
review of one of their declarations reads as *unavailable* rather than deleted. After a build, the
failures are `lake build --no-build 2>&1 | sed -n '/logged failures/,$s/^- //p'`.

**Large projects are extracted in parts.** Each imported module maps files into memory, and a large
project on top of Mathlib needs more mappings than Linux allows one process by default
(`vm.max_map_count`). `extract` imports the project in parts, each in a child process, and merges
them: `--parts N` starts with N parts, a part that fails to import is split in two, and `--jobs N`
runs N at once. The dataset does not depend on the split, with one exception: Lean generates some
auxiliary lemmas (`congr_simp`, equation lemmas) separately in several modules, and a part keeps the
copy of the first module it imports. The content hash of a proof resting on such a lemma, its `term`
edges, and the module recorded for the lemma can then differ between splits; `producer.parts`
records the split. With the same split, two extractions are byte-identical.

**Past the project.** By default an upstream constant is a node with no edges of its own.
`--upstream-closure <statement|meaning|term>` follows dependencies into the libraries underneath:
every upstream declaration reached becomes a node, with its edges in `upstream-<notion>` files.
Along `term`, a definition's value is followed whole, and a proof contributes its statement only.

**Packages.** Every node's `package` is the Lake name of the package declaring it, read from the
workspace's `lake-manifest.json`, so a declaration has the same label in every dataset: Mathlib's
are `mathlib` in Mathlib's own dataset as downstream of it. The project is labelled by the root
package's name (`--package` overrides it; without a manifest, the root prefix), a dependency by its
name in the manifest, found by its directory with symbolic links resolved, and the toolchain's own
library is `lean4`.

## The dataset

```
meta.json                    what produced it, from what; its edge files and facets; the packages
decls.jsonl                  one node per line: id, name, module, package, scope, kind, isProp, hashes;
                             the nodes are the project's declarations and what their edges point to
modules.jsonl                one project module per line: name, path, imports, module docstrings
edges/<notion>.bin           little-endian int32 pairs (source id, target id)
facets/<facet>.jsonl         at most one line per declaration, keyed by "decl"
```

**The rule** `ltb-meaning/1` (MeaningGraph's `MeaningGraph.Hash`) decides the declarations, and two
walks under it give each hash with its graph: the walk that erases proofs gives the `statement` and
`meaning` edges and the meaning and local hashes, and the walk that keeps proofs gives the `term`
edges and the content hash. So each hash follows its graph. Helpers are looked through, and a
constructor or recursor stands for its inductive type.

| notion | edges from a declaration to |
|---|---|
| `statement` | what its type mentions, proofs erased |
| `meaning` | what it means: its statement for a proof, its statement and value for a definition, its type and constructors for an inductive type; proofs erased everywhere |
| `term` | everything the kernel checked of it: its type and value, proofs included (`--no-term` skips it) |
| `source` | what its source needs that the elaborated term does not mention: coercions, and what a notation expands to |

| hash | changes when |
|---|---|
| `meaning` | anything in its `meaning` closure changes, down to Lean core; not on renames |
| `local` | the declaration itself is rewritten, not when something it uses changes |
| `content` | anything in its `term` closure changes, proofs included |

**Facets:** `docstring`, `source` (path, range, keyword), `axioms` (and whether `sorryAx` is among
them), `statement` (binders with their roles, conclusion, body, fields or constructors, as Lean
prints them, with the constant each identifier stands for), `signature` (every node's, for hovers),
and one `annotation.<attr>` per attribute recorded in the TrustAnnotations extension, including
attributes defined after this release. `--no-statements`, `--no-refs`, `--no-signatures` and
`--no-upstream-docs` leave out what a consumer does not show.

## The attributes facet

The compiled library does not keep the attributes a declaration was written with. A script shipped
with each release reads them from the sources at the dataset's commit (the `extract` action runs it):

```bash
python3 scripts/attributes.py --dataset dataset --source path/to/the/checkout
```

It writes the facet `attributes` (`attributes/1`): the attributes written before each declaration's
keyword, as `{name, args}` (`@[stacks 09GA]`, `@[wikidata Q616608]`, `@[deprecated]`, …). Those
added later by an `attribute [...]` command are not seen.

## Checking a dataset

```bash
lake env trust-extract check --root MyProject --dataset dataset --jobs 8
```

For every project declaration D, Lean's kernel checks D in an environment holding the libraries
underneath, the project's constants that are not nodes, and, of the project's nodes, only those in
D's closure as the dataset's edges draw it. What the kernel needs and the closure lacks is
**missing**. It also lists what D mentions, through helpers, that its closure lacks (`unlisted`).
The result is the facet `check.kernel.<notion>`: `ok`, `missing`, `error` or `skipped` per
declaration. It proves sufficiency, not minimality, and does not see notation or coercions.

- `--notion meaning` (the default) erases proofs first and adds theorems as axioms: the closures that
  coverage and staleness rest on.
- `--notion term` keeps values whole and checks every proof again, one declaration at a time. It is
  for small libraries: on a large one its memory grows with the proofs checked until the machine
  runs out.

It runs on the dataset's toolchain, in the project as built at the dataset's commit. `--drop-edge A
B` leaves an edge out, to test the check; `--shard k/n` spreads it over processes; `--strict` exits
with 1 on any failure.

## Well-definedness

```bash
lake env trust-extract welldefined --dataset dataset --jobs 8
```

Runs [WellDefined](https://github.com/LeanTrustBuilders/well-defined)'s analyzer and writes the facet
`welldefined`. Each application of a definition with a declared domain (`@[domain]`) in a statement
analyzed carries an obligation, that its arguments are in the domain given what is in scope; it
comes out `discharged`, `irrelevant`, `refuted`, `open` or `unapplied`.

- **Statements:** the claims and specification theorems by default, those named with `--decl` or
  `--decls-file`, and every theorem of the modules under `--theorems-in`.
- **Bodies:** every definition with a declared domain is analyzed under it (`--no-definitions` to
  skip).
- **Domains:** those of the modules imported; `--module` imports a catalogue alongside the library.
  Rows are keyed by declaration name and need not be about nodes.
- **Dischargers:** `omega`, `infer_instance`, `positivity`, `fun_prop`, `norm_num`, `simp_all`, then
  those given with `--discharger`, each with `--heartbeats` (default 10000) per obligation.
  `meta.json` records them and the domains, since the results depend on them.

## Build

```bash
lake build
./.lake/build/bin/trust-extract version
```

`lake update` rewrites `lean-toolchain` to the newest toolchain among the dependencies: restore the
pin afterwards and rebuild from clean (`rm -rf .lake/build`).

`main` follows the newest toolchain, with its dependencies on their `main`; a branch
`lean-v<toolchain>` carries the extractor on an older one. A tag `v<version>-lean-v<toolchain>`
publishes a release.

## Tests

```bash
lake build && test/run.sh [KEEP_DIR]
```

`test/run.sh` extracts the fixture project `test/fixture` twice and checks the datasets are
identical, overlays version B (`test/fixture-b`: a definition changed, a statement rewritten, a proof
changed, a binder and a theorem renamed), extracts again, and checks how each hash moves, the edges
of each notion and the facets. It also checks extraction in parts, skipped modules, the upstream
closure, the kernel check (which must catch a dropped edge), the well-definedness facet, and the
the attributes facet. With `KEEP_DIR`, it keeps the datasets: they are the test vectors of
specs, evidence-core and referee-site.
