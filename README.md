# extractor

`trust-extract` reads a compiled Lean project and writes a **dataset** (spec `ltb-dataset/1`, see
[LeanTrustBuilders/specs](https://github.com/LeanTrustBuilders/specs)): its declarations, the three
hashes of each declaration's key, its dependencies under four notions, and facets such as
docstrings, source locations and annotations. It also checks a dataset with Lean's kernel
(`trust-extract check`).

It is the only piece of the [LeanTrustBuilders](https://github.com/LeanTrustBuilders) suite that
reads `.olean` files, so it is the one released per Lean toolchain. Everything downstream
([evidence-core](https://github.com/LeanTrustBuilders/evidence-core), views, stores) reads the
dataset and needs no Lean.

Built on [MeaningGraph](https://github.com/LeanTrustBuilders/meaning-graph) (dependencies, and the
meaning and local hashes), [semantic_hash](https://github.com/mathlib-initiative/semantic_hash) (the
content hash) and
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
dataset does not depend on how the work was split, with one exception. Lean generates some
auxiliary lemmas on demand (`congr_simp`, equation lemmas), and several modules can each hold their
own copy, with different proofs. An environment keeps the copy of the first module in its import
order, which depends on the modules a part imports. So the **content** hash of a declaration whose
proof rests on such a lemma, its **term** edges, and the module recorded for such a lemma can
differ between two splits: on Tau Ceti at 8befae0, 4 parts against 8 gave 287 different content
hashes out of 97,944, 8 different term edges out of 5.9 million, and 4 different modules. The
meaning and local hashes, the statement and meaning edges, and the facets did not differ. With the
same split, two extractions are byte-identical, on different machines too (Tau Ceti at 8befae0 on
a laptop and on a GitHub runner). `meta.json` records the number of parts (`producer.parts`);
`test/run.sh` checks that the fixture's dataset does not depend on the split. Raising the limit
(`sudo sysctl -w vm.max_map_count=262144`) lets a large project be extracted in fewer parts.

`trust-extract diagnose-import <private|exported> <Prefix>` reports how many mappings an import
takes.

Other options: `--jobs N` runs up to N parts at once; `--no-term` skips the `term` notion, which walks
every proof term. The dependencies are MeaningGraph's (`Context.depsOf`, in parallel): `statement` is
its `typeDeps`, `meaning` its `typeDeps` for a proof and `dataDeps` otherwise, and `term` its `deps`,
which is only computed when asked for.

**Past the project.** By default the graph stops at the project: an upstream constant is a node
with no edges of its own. `--upstream-closure <notion>` follows dependencies into the libraries
underneath, with MeaningGraph's boundary lifted (`Boundary.none`, `Context.closure`): every upstream
declaration reached along `statement`, `meaning` or `term` becomes a node, with its own edges in
`upstream-statement`, `upstream-meaning` and `upstream-term` (the last from declarations that are not
proofs: an upstream proof term is never walked), and the statement facet covers the ones that are
not proofs. Along `term`, a definition's value is followed whole, the lemmas its proofs call
included, and a proof contributes its statement only: the closure
[trust](https://github.com/chrisflav/trust) draws. The project's own notions and hashes do not
change. On LeanMachineLearning (1,452 declarations on Mathlib) the `term` closure adds 10,288
upstream declarations, and the whole extraction takes 19 seconds and writes 24 MB.

On Tau Ceti at 8befae0 (7,432 modules on top of Mathlib; 81,999 declarations), extraction takes
about 80 seconds on a 32-core machine with `--parts 4 --jobs 2`, at most 8 GB of memory per
part, and writes 156 MB. Each part reports how long each of its steps takes.

## The dataset

```
meta.json                    what produced the dataset, from what; the edge files and facets it holds;
                             the packages imported, with their module counts and which import which
decls.jsonl                  one node per line: id, name, module, package, scope, kind, isProp, hashes
modules.jsonl                one project module per line: name, source path, imports, module docstrings
edges/statement.bin          little-endian int32 pairs (source id, target id)
edges/meaning.bin
edges/term.bin
edges/source.bin
edges/upstream-<notion>.bin  with --upstream-closure: the same notions, from upstream nodes
facets/docstring.jsonl       one file per facet, one line per declaration, keyed by "decl"
facets/source.jsonl
facets/axioms.jsonl
facets/statement.jsonl
facets/annotation.<attr>.jsonl
```

**The rule** (`ltb-meaning/1`, MeaningGraph's `MeaningGraph.Hash`) decides the declarations, the
`statement` and `meaning` edges, and the meaning and local hashes, in one walk, so that the graph and
the hashes agree: a declaration's meaning hash changes exactly when something in its `meaning`
closure changes. Proofs are erased everywhere; helpers are looked through; a constructor or recursor
stands for its inductive type. See [meaning-hash.md](https://github.com/LeanTrustBuilders/design/blob/main/AI_initial_docs/meaning-hash.md).

**Nodes** are the project's own declarations (written by a person, private ones included) and the
upstream declarations their statements and meanings rest on; with `--upstream-closure`, also every
upstream declaration the closure reaches. Upstream nodes have outgoing edges only in the
`upstream-<notion>` files.

**Notions of dependency:**

| notion | edges from a declaration to |
|---|---|
| `statement` | the declarations its type mentions, proofs erased |
| `meaning` | what it means: its statement for a proof; its statement and value for a definition; its type and constructors for an inductive type; proofs erased everywhere. Coverage is computed over this closure, and the meaning hash covers it |
| `term` | its type and whole value, proofs included, restricted to targets that are nodes |
| `source` | what its source needs that the elaborated term does not mention: coercion instances, and for a notation what it expands to |

**The three hashes** of the declaration key:

| hash | what it covers |
|---|---|
| `meaning` (`ltb-meaning/1`) | a Merkle hash of the declaration's content under the rule, each reference replaced by the referenced constant's meaning hash. Deep: changes when anything in its `meaning` closure changes, down to Lean core |
| `local` (`ltb-local/2`) | the same content, with references to other declarations by name. Changes when the declaration itself is rewritten, not when something it uses changes |
| `content` | semantic_hash's proof-relevant hash. Deep, and also changes when a proof changes; trust's certificates are keyed by it |

All three are invariant under renaming binders and universe parameters, and the meaning hash is
invariant under renaming the declaration itself, and the declarations it uses, which is how reviews
follow renames. Each node also carries, as `legacy`, the meaning and local hashes of
`ltb-dataset/0` (semantic_hash's proof-irrelevant hash, `ltb-local-v1`), so that records keyed by
them can still be compared.

**Facets:** `docstring`, `source` (path, range, and the keyword the declaration is written with, such
as `theorem` or `lemma`), `axioms` (and whether `sorryAx` is among them), `statement`, and one
`annotation.<attr>` facet per attribute recorded in the TrustAnnotations extension, including
attributes defined after this extractor was released (`claim`, `example_of`, `specifies`,
`characterization`, …; one row per declaration, with the payload of each application).

`statement` takes each statement apart, as a reader needs it: its binders, each with its name, its
type and its role (a **type**, a **variable**, a **hypothesis**, or an **instance**), the conclusion
under them, and, for a definition, its body; for a structure, its fields; for another inductive
type, its constructors. Everything is pretty-printed by Lean from inside the declaration's
namespace, with a bounded number of steps for a body (`⋯` marks what was cut). It is computed in
parallel chunks; `--no-statements` skips it.

**Hovers.** Each text of the `statement` facet comes with `refs`: for every identifier, operator or
notation that stands for a constant, its span and the constant's name, read off Lean's own record
of which subterm each piece of printed text came from (the one the editor's hovers use). Each binder
also names the head constant of its type. The `signature` facet gives every node's signature as Lean
prints it, with its `refs` too, and the `docstring` facet covers upstream nodes too. Together they are what a site needs
to say, on hover, what `ℕ`, `Kernel` or `∀ᵐ` is. They cost about two thirds more dataset on
LeanMachineLearning (3.9 MB to 6.4 MB); `--no-refs`, `--no-signatures` and `--no-upstream-docs`
leave each part out for a consumer that does not show hovers.

## Checking a dataset

```bash
lake env trust-extract check --root LeanMachineLearning --dataset dataset --jobs 8
```

Check 2 of the suite's self-checks (dependency-testing.md §9 in LeanTrustBuilders/design): for every
project declaration D of a dataset, Lean's kernel checks D in an environment that holds the
libraries underneath, the project's constants that are not nodes (compiler helpers), and, of the
project's nodes, only those in D's closure as the dataset's edges draw it. What the kernel needs
and the closure lacks is **missing**; the check adds it and runs again, to name everything missing.

- `--notion meaning` (the default) erases proofs first, with a pass of its own: an argument whose
  expected type is a proposition becomes `sorryAx` of that type, and theorems are added and checked
  as axioms (their statements). `--notion term` keeps values whole and checks every proof.
- The project's constants are renamed in everything the check adds, so a reference to one it did not
  add cannot find the imported original.
- It also lists what D **mentions**, through helpers, that its closure lacks (`unlisted`): stricter
  than the kernel, which only looks at what it needs.
- It writes the facet `check.kernel.<notion>` (schema `check.kernel/1`) into the dataset: per
  declaration, `kernel` is `ok`, `missing` (with the constants), `error` or `skipped`.
- It proves sufficiency, not minimality, and does not see notation or coercions.

It must run on the dataset's toolchain, in the project as built at the dataset's commit.
`--drop-edge A B` leaves an edge out, to test the check; `--strict` exits with 1 on any failure.
`--shard k/n` checks every n-th declaration, to spread a check over processes: along `term`, on a
library the size of Tau Ceti, checking proofs in many threads of one process used far more memory
than the same work in several processes of one thread each. On
LeanMachineLearning (1,452 declarations) both notions check everything in about 3 seconds with
`--jobs 8`. Dropping edges one at a time, the kernel caught all 39 removals that left a declaration's
`meaning` closure without the target, except 2 proofs written inside a statement, which `meaning`
counts but the kernel does not need once proofs are erased; and all 17 such removals along `term`.
Under the rule `ltb-meaning/1` (0.7.0), every closure of LeanMachineLearning checks, along both
notions, and no declaration mentions anything its closure lacks.

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
evidence-core's test vectors are produced. It also runs the kernel check on version B, along both
notions, and checks that it catches a dropped edge.
