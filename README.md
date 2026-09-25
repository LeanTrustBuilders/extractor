# extractor

`trust-extract` reads a compiled Lean project and writes a **dataset** (spec `ltb-dataset/0`, see
[LeanTrustBuilders/specs](https://github.com/LeanTrustBuilders/specs)): its declarations, the three
hashes of each declaration's key, its dependencies under three notions, and facets such as
docstrings, source locations and annotations.

It is the only piece of the [LeanTrustBuilders](https://github.com/LeanTrustBuilders) suite that
reads `.olean` files, so it is the one released per Lean toolchain. Everything downstream
([evidence-core](https://github.com/LeanTrustBuilders/evidence-core), views, stores) reads the
dataset and needs no Lean.

Built on [MeaningGraph](https://github.com/RemyDegenne/meaning-graph) (dependencies),
[semantic_hash](https://github.com/mathlib-initiative/semantic_hash) (hashes),
[ChallengeGen](https://github.com/RemyDegenne/challenge-gen) and
[TrustAnnotations](https://github.com/LeanTrustBuilders/annotations). The dataset layout follows
the index format of [trust](https://github.com/chrisflav/trust).

## Use

Inside the project, once it is built:

```bash
lake env /path/to/trust-extract extract --root MyProject --repo owner/name --out dataset
```

The project and the extractor must use the same Lean toolchain: a `.olean` file can only be read by
the Lean that wrote it. Releases are tagged by extractor version and toolchain:
`v0.2.0-lean-v4.34.0-rc2` is trust-extract 0.2.0 for `leanprover/lean4:v4.34.0-rc2` (the first release
was tagged `v4.34.0-rc2`). Take the newest release whose tag ends with `-lean-<your toolchain>`.

**Extract from a clean build.** The extractor reads the `.olean` files as they are and cannot tell
whether they are consistent with each other. A build directory that has gone through several
commits can hold a module compiled against an older version of one of its imports, and Lake may
count it as up to date. For a dataset that others will use, start from an empty `.lake/build`, as
CI does: fetch the project's cache, then build what it lacks.

**Modules that do not build.** `--skip-module M` (repeatable) or `--skip-modules-file FILE` leaves
modules out, typically those that fail to build at the commit, and with them every module importing
them, since Lake's report of failures names only the modules it tried. The dataset lists them all
in `meta.json`, under `library.unavailable`, so that a review of one of their declarations reads as
*unavailable* rather than as deleted. After a build, the failures are

```bash
lake build --no-build 2>&1 | sed -n '/logged failures/,$s/^- //p'
```

**Large projects are extracted in parts.** Every imported module maps several files into memory,
and a project the size of Tau Ceti on top of Mathlib (about 15,000 modules) needs more mappings than
Linux's default limit (`vm.max_map_count`, 65,530) allows in one process. So `extract` imports the
project in parts, each in a child process (`extract-part`), and merges them. A part that fails to
import is split in two and retried; `--parts N` starts with N parts. A declaration's dependencies
and hashes depend only on what its module imports, and nodes are ordered canonically, so the
dataset is identical however the work was split: `test/run.sh` checks this. Raising the limit
(`sudo sysctl -w vm.max_map_count=262144`) lets a large project be extracted in fewer parts.

`trust-extract diagnose-import <private|exported> <Prefix>` reports how many mappings an import
takes.

Other options: `--jobs N` runs up to N parts at once; `--no-term` skips the `term` notion, which walks
every proof term; `--check-deps` checks every declaration's dependencies against MeaningGraph's own
`Context.declDeps` (the extractor computes them with its own driver, which gives the same lists but
skips proofs unless `term` is asked for, deduplicates with hash sets, and runs in parallel). The
tables those computations rest on are MeaningGraph's too (`Context`), except the one mapping each
notation to what it expands to: MeaningGraph walks every definition's value as a tree, which is
exponential on values that share subterms (a part of Tau Ceti never finished), so the extractor
builds that table itself, visiting each subterm once; `--check-deps` compares it with
MeaningGraph's.

On Tau Ceti (7,010 modules on top of Mathlib; 77,758 declarations), extraction takes about six
minutes on a 32-core machine with `--parts 4 --jobs 2`, at most 8 GB of memory per part, and writes
147 MB.

## The dataset

```
meta.json                    what produced the dataset, from what; the edge files and facets it holds
decls.jsonl                  one node per line: id, name, module, package, scope, kind, isProp, hashes
edges/statement.bin          little-endian int32 pairs (source id, target id)
edges/meaning.bin
edges/term.bin
facets/docstring.jsonl       one file per facet, one line per declaration, keyed by "decl"
facets/source.jsonl
facets/axioms.jsonl
facets/annotation.<attr>.jsonl
```

**Nodes** are the project's own declarations (written by a person, not generated by the compiler)
and the upstream constants their statements and data mention. Upstream nodes have no outgoing edges.

**Notions of dependency:**

| notion | edges from a declaration to |
|---|---|
| `statement` | the constants its type mentions |
| `meaning` | what it means: its statement for a proof; its statement and the data of its value, proofs skipped, for a definition. Coverage is computed over this closure |
| `term` | its type and whole value, proofs included, restricted to targets that are nodes |

**The three hashes** of the declaration key:

| hash | what it covers |
|---|---|
| `meaning` | semantic_hash's proof-irrelevant hash. Deep: changes when anything the declaration's statement or data rests on changes meaning |
| `content` | semantic_hash's proof-relevant hash. Deep, and also changes when a proof changes |
| `local` (`ltb-local-v1`) | the declaration's own statement and data, with each referenced constant contributing its *name*. Changes when the declaration itself is rewritten, not when something it uses changes |

All three are invariant under renaming binders and universe parameters, and the meaning hash is
invariant under renaming the declaration itself, which is how reviews follow renames.

**Facets:** `docstring`, `source` (path, range, and the keyword the declaration is written with, such
as `theorem` or `lemma`), `axioms` (and whether `sorryAx` is among them), and one
`annotation.<attr>` facet per attribute recorded in the TrustAnnotations extension, including
attributes defined after this extractor was released.

## Build

```bash
lake build
./.lake/build/bin/trust-extract version
```

`lake update` rewrites `lean-toolchain` to the newest toolchain among the dependencies. Restore the
pin afterwards and rebuild from clean (`rm -rf .lake/build`), or the binary is built for the wrong
Lean.

**Moving to a new toolchain.** `main` follows the newest toolchain the libraries use; a release tag
keeps each older one buildable. To move: tag the annotations package for the new toolchain (the
extractor requires it by toolchain tag), set `lean-toolchain` and the `TrustAnnotations` revision,
`lake update TrustAnnotations`, run the tests, and tag `v<version>-lean-v<toolchain>`. The fixture
is built with whatever toolchain and annotations revision the extractor is pinned to.

## Tests

```bash
lake build && test/run.sh
```

`test/run.sh` builds the fixture project `test/fixture` (version A), extracts it twice and checks the
two datasets are identical, overlays `test/fixture-b` (version B), extracts again, and runs
`test/check.py` on both. Version B changes a definition, rewrites a statement, changes only a proof,
renames a binder, and renames a theorem; the check pins how each hash moves in each case, the kinds,
the edges of each notion, and the facets. `test/run.sh DIR` keeps the two datasets, which is how
evidence-core's test vectors are produced.
