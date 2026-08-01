# Missing layers

What a Lean 4 / Mathlib formalization of the CSP dichotomy needs that Mathlib does not
have. Probed against Mathlib at `905b9581` (2026-07-28), toolchain `v4.32.2`, by reading
the source rather than by recall.

Legend: **HAVE** usable directly · **PARTIAL** core exists, glue missing · **MISSING**
nothing there.

---

## 0. The one that decides the shape of the project

**There is no complexity theory in Mathlib.** No `P`, no `NP`, no NP-completeness, no
polynomial-time many-one reduction, no SAT. The single relevant definition,
`Turing.TM2ComputableInPolyTime` (`Mathlib/Computability/TuringMachine/Computable.lean:179`),
applies to total functions `α → β` rather than to decision problems, and is not even
known to compose — `TM2ComputableInPolyTime.comp` is an open `proof_wanted` at
`Computable.lean:284`.

So a formalization cannot state "CSP(Γ) is in P, or NP-complete" without first building a
complexity layer. That layer is a large project *unrelated to the dichotomy*, and it would
dominate the effort while contributing none of the mathematics.

This is why the blueprint states layered targets (`ch0-target.tex`): the algebraic core
(T0), algorithm correctness as a proposition (T1), the algebraic content of hardness (H0)
— none of which mention a machine — and the complexity wrappers (T2, H1) isolated and left
unbuilt. Everything below is about T0/T1/H0.

---

## 1. Universal algebra

| Item | Status | Where / what is needed |
|---|---|---|
| Languages, structures, terms, `Term.realize` | HAVE | `Mathlib/ModelTheory/{Basic,Syntax,Semantics}.lean`. `Term.func` takes `Fin l → Term α`, so arbitrary branching arity needs no encoding. |
| Substructures, `closure`, complete lattice, Galois insertion, `closure_induction`, `map`/`comap` | HAVE | `Mathlib/ModelTheory/Substructures.lean` (985 lines). This is exactly the `Sg` API. |
| `mem_closure_iff_exists_term` | HAVE | Generation by terms over a *fixed* generator list, with the variable type being the generating set. Better than any hand-rolled clone; the predecessor project deleted a whole blueprint section because of it. |
| `Term.subst`, `Term.relabel` and their realize laws | HAVE | Simultaneous substitution, which the predecessor blueprint originally lacked. |
| Products of structures | **MISSING** | `ModelTheory/Ultraproducts` goes straight to the quotient via `Prestructure` and never exposes `∀ i, M i`. **Built here**: `CSP/Product.lean` (dependent and binary products, coordinatewise realization, reindexing and evaluation homomorphisms), inherited from the predecessor project. ~140 lines. |
| Congruences of a general structure | **MISSING** | `Con` exists only for monoids/rings; `Setoid` has its complete lattice but no compatibility. `ModelTheory/Quotients.lean` has `Prestructure` — the right *data*, but as a class indexed by the setoid, so congruences cannot be quantified over, intersected, or ordered. **Built here**: `CSP/Congruence.lean` — bundled `Congruence L M`, order, `⊥`/`⊤`, arbitrary `sInf`, quotient structure, quotient homomorphism. ~190 lines, `sorry`-free. |
| Congruence lattice as a complete lattice | PARTIAL | `sInf` and the order are built; the full `CompleteLattice` instance (needs `sSup` via generation) is not, and is not yet needed. Small. |
| Correspondence theorem, second/third isomorphism theorems for structures | **MISSING** | Needed for `cor:prop-quotient` and `cor:prop-from-factor`. Medium (~300 lines). |
| Stability of a relation under a congruence | **MISSING** | **Built here**: `CSP.StableAt`, `CSP.Stable`, `CSP.Stable2`. |
| Irreducible congruences, `σ*` | **MISSING** | Not a standard notion; note it is *not* meet-irreducibility (`Mathlib/Order/Irreducible.lean` does not apply). **Built here**: `CSP/Irreducible.lean`, including existence and uniqueness of `σ*` — the step the source states as "the minimal δ". `sorry`-free. |
| Absorption, binary absorption, central subuniverses, Taylor terms | **MISSING from Mathlib**, **HAVE from the predecessor** | `ZhukLean.{Absorbs, BinAbsorbs, Witnesses, IsTaylorOn, CentrallyAbsorbs}`, reused here as a genuine `lake` dependency. |
| Clones, polymorphisms, `Pol`/`Inv`, WNU, Taylor, Maltsev, majority | **MISSING** | Nothing anywhere in Mathlib. `Mathlib/Combinatorics/Optimization/ValuedCSP.lean` is *valued* CSP with fractional polymorphisms only — no decision CSP, no ordinary polymorphism, no `Pol`/`Inv`. Not a useful base. |
| Polynomially complete algebras | **MISSING** | `L[[A]]` / `Substructure.withConstants` gives polynomial operations nearly free, so the definition is cheap; the Istinger–Kaiser characterization is not. **Avoidable**: treat "PC congruence" as "irreducible and not linear" throughout — the only statement needing genuine polynomial completeness (`lem:pc-on-top`) is used solely to connect with the 2020 paper. |

## 2. Finite combinatorics

**HAVE, everything, with no glue.** `Finset`/`Fintype`; `Fintype.decidableForallFintype`;
`Finset.strongInduction` and `strongDownwardInduction` (`Mathlib/Data/Finset/Card.lean`);
`Finite.wellFounded_of_trans_of_irrefl`; `Setoid.completeLattice`.

One trivial gap: no `Finite (Setoid α)` instance for finite `α` (~5 lines via
`Setoid α ↪ (α → α → Prop)`).

Also needed and not present as a named lemma, though it is three lines: *a monotone
predicate on subsets of a finite set that holds at the top holds at some minimal subset*.
The main proof performs this minimality step at least four times, each with a different
property (`haz:minimality`). Worth stating once.

## 3. Graphs and connectivity

**HAVE.** `Relation.ReflTransGen` (`Mathlib/Logic/Relation.lean:332`) with
`head_induction_on`; `Relation.reflTransGen_symmGen` (`:878`) is precisely the
"linked = reflexive-transitive closure of a symmetric relation" lemma; `SimpleGraph`
with `Reachable`, `Connected`, `ConnectedComponent`, and decidable reachability for finite
types (`Combinatorics/SimpleGraph/Connectivity/Finite.lean:56`).

Recommendation followed here: define linkedness as `Relation.ReflTransGen` directly
(`CSP.Linked`), and keep a ~15-line bridge to `SimpleGraph.fromRel` for the one place that
needs connected components (splitting a non-linked instance into linked pieces). That
bridge lemma is not in Mathlib.

## 4. Abelian groups, `ZMod`, and the codimension-one step

| Item | Status |
|---|---|
| `ZMod p`, its field structure for prime `p`, products | HAVE |
| Subgroups of finite abelian groups, structure theorem | HAVE |
| Vector spaces over `ZMod p`, dimension, codimension | HAVE for a single prime |
| **Dimension of a subgroup of `∏ ZMod qᵢ` with *mixed* primes** | **MISSING** |
| **"codimension 1 ⟺ solution set of one linear equation"** | **MISSING** |

This is the substrate of `thm:codim-one` Step 2 and of the algorithm's `(p3)`. The mixed
primes are not incidental: the group splits as a product over primes of
$\mathbb F_q$-vector spaces, and "dimension" is a tuple. Zhuk's own footnote — "the fact
that different variables take values from different fields is not a problem as $J$ may
contain only variables on the same field" — is this issue surfacing. Medium
(~400–600 lines), and self-contained enough to be done independently and early.

## 5. Instances, coverings, and the representation decision

Nothing in Mathlib. **Built here**: `CSP/Instance.lean` — constraints with tuple scopes,
instances as lists, assignments, solutions, reductions (allowed empty), 1-consistency,
linkedness, cycle-consistency, subdirect solution sets, weakening as a relation,
cruciality. `sorry`-free.

The one design decision still open, and the most consequential:

> **Expanded coverings.** The source says "rename the variables so that the only common
> variable of `Υ_x` and `𝓙` is `x`" and forms conjunctions of instances whose variable
> sets must first be made disjoint. With a concrete variable type this needs a fresh-name
> supply plus eight preservation lemmas (renaming preserves 1-consistency,
> cycle-consistency, cruciality, covering-hood, …) that the paper never states. With the
> variable type as a *parameter* and instances joined over a coproduct, renaming
> disappears into the coproduct and those lemmas become transport along an equivalence.

`CSP/Instance.lean` takes the variable type as a parameter for exactly this reason;
`IsExpandedCovering` is deliberately left undefined rather than stubbed, because a
`def … : Prop := sorry` is a junk constant that later proofs can silently lean on.

---

## 6. Size

The one hard calibration point: the predecessor project formalized ~3.5 printed pages of
Zhuk's centre theory in ~1670 lines of Lean from a ~24-page blueprint. That is roughly
**480 Lean lines per printed page** of source.

| Block | Pages | Notes |
|---|---|---|
| Zhuk 2404 §2–§3 (the spine) | ~35 | the dichotomy proper |
| Zhuk 2404 §5 (proofs of the §2 properties) | ~13 | |
| Zhuk 2404 §4 (XY-symmetric) | ~11 | **independent of the dichotomy — cut it** |
| Imported black boxes (16 of them) | ~25 | 3 already discharged by the predecessor |
| The algorithm and its correctness wiring | ~10 | from the 2020 paper; 2404 gives only pseudocode |
| NP-hardness side (H0) | ~20 | pp-interpretation, Galois, Bulatov–Jeavons–Krokhin |
| Cook–Levin → NAE-3-SAT | ~12 | **or 0**, if H1 is left unbuilt as recommended |

Excluding §4 and the complexity wrappers: **~100–130 printed pages ≈ 35 000–60 000 lines
of Lean**. No part of it is currently formalized anywhere in any proof assistant beyond
the centre theorem reused here.

Line count, however, is not the binding constraint. This pipeline has demonstrated
~33 000 verified `sorry`-free Lean lines in ~10 active hours on the Jordan–Schönflies
formalization, by fanning independent modules out into git worktrees and landing them in
waves — 52 merges, dozens of `wt/*` branches — with the rate holding on the hard blueprint
content, not just the foundation. At that throughput the CSP algebra is days of wall clock,
not years.

What binds instead is the **critical path**: the depth of the serial chain, and the number
of places where the source is wrong and new mathematics is required. Here that is §3's chain
— `lem:bridge-from-instance` → `thm:stable-intersection` → `thm:main-inductive`, each a
single large proof that cannot be split across agents — plus the four blocking defects
(the §5 citation cycle, the `n = 2` gap, the missing hypothesis in connectedness, and the
two gaps in the main induction) that need arguments not present in the literature. Those are
not throughput-limited, and they are what to schedule around.

## 7. Suggested order

1. **`lem:ba-center-implies`** (`[ZhukStrong, Cor. 6.1.2, 6.9.2]`). Small, self-contained,
   in the same neighbourhood as the reused predecessor code, and used everywhere.
2. **The mixed-prime linear algebra** of §4. Independent of everything else.
3. **`lem:bridge-comp`** (`[ZhukJACM, Lem. 6.3]`). Pure relational algebra, 12 source
   lines. Discharges one of the two `sorry`s in `CSP/Bridge.lean`.
4. **The coproduct design for coverings**, then `IsExpandedCovering` and
   `prop:covering-basics`.
5. **`thm:stable-intersection`**. The one genuinely hard statement in the interface, and
   the sole source of bridges.
6. **`lem:bridge-from-instance`**. Eight hypotheses, ~10 pages. Budget generously.
7. **`thm:main-inductive`**. Last.
