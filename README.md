# CSP dichotomy in Lean 4

Foundations for a formalization of the CSP Dichotomy Theorem, following the blueprint at
[`../csp-dichotomy`](../csp-dichotomy), which rewrites Zhuk's simplified proof
([arXiv:2404.01080](https://arxiv.org/abs/2404.01080)).

Lean 4.32.2, Mathlib v4.32.2. `lake build`.

## Status

**Foundations complete and `sorry`-free; the summit is stated, not proved.**

| Module | Contents | Lines | Status |
|---|---|---|---|
| `CSP/Product` | products of structures, coordinatewise realization, reindexing | 143 | complete |
| `CSP/Congruence` | `Congruence L M`, order, `⊥`/`⊤`/`sInf`, quotient structure, `projHom`; stability | 189 | complete |
| `CSP/Irreducible` | irreducible congruences; existence and uniqueness of `σ*` | 136 | complete |
| `CSP/Bridge` | bridges, collapse `δ̃`, composition, linear and PC congruences | 143 | 2 imports open |
| `CSP/Types` | the six types, multi-types, `⋘` | 181 | complete |
| `CSP/Instance` | instances, reductions, consistency, linkedness, weakening, cruciality | 211 | complete |
| `CSP/Main` | the target theorems | 186 | stated |
| **total** | | **1189** | |

Eight `sorry`s in total, all deliberate: two are results Zhuk imports from his 2020 paper
(bridge composition and its collapse identity), six are the target theorems plus the
measure lemma. Nothing below `CSP/Main` depends on any of them.

## What is reused

[`../zhuk-lean`](../zhuk-lean) — a complete `sorry`-free formalization of Zhuk's centre
theorem — is consumed as a `lake` dependency, not copied. It supplies absorption in the
tuple form, Taylor terms, central absorption, the Barto–Kazda relational description of
absorption, and the centre theorem itself. That last one is
`LEMCenterImpliesTernaryAbsorption`, which Zhuk's simplified proof cites *without proof*,
so three of its sixteen black-box imports are already discharged.

## What Mathlib supplies, and what it does not

See [`GAPS.md`](GAPS.md) for the full probe. The short version:

- **Universal algebra**: `Mathlib.ModelTheory` gives languages, terms, substructures with
  the full `Sg` API, and term substitution. It does **not** give products of structures,
  congruences of a general structure, clones, polymorphisms, WNU or Taylor terms, or
  anything CSP-related. `Mathlib/Combinatorics/Optimization/ValuedCSP.lean` is *valued*
  CSP with fractional polymorphisms only, and is not a usable base.
- **Complexity theory**: nothing. No P, no NP, no NP-completeness, no polynomial-time
  reduction, no SAT. The one relevant definition, `Turing.TM2ComputableInPolyTime`,
  applies to total functions rather than decision problems and is not known to compose —
  its composition lemma is an open `proof_wanted` in Mathlib. **This is why the blueprint
  states layered targets**; see its §1.
- **Finite combinatorics, graphs, `ZMod`**: essentially everything, with two gaps — a
  `Finite (Setoid α)` instance (~5 lines), and the mixed-prime linear algebra behind the
  codimension-one theorem (medium).

## Design decisions

- **Build on `Mathlib.ModelTheory`, keep the language generic.** A bespoke
  "finite algebra with one WNU operation" type would bundle the standing hypotheses as
  fields, but it would discard `Substructures.lean` — 985 lines of exactly the `Sg` API
  needed — and the predecessor's 1600 lines. Congruences and quotients turn out to be
  *cheaper* in `ModelTheory`, not dearer.
- **`⋘` is `Relation.ReflTransGen`** of the union of the four base types. Its induction
  principle is the one the proofs use. `L` and `PC` are absent from the union because `D`
  subsumes them.
- **Dotted relations are disjunctions**: `DotLll C B := C = ∅ ∨ Lll C B`, so the case
  split is forced at every use site rather than resolved by the reader's judgement.
- **The bridge criterion defines linearity.** Zhuk defines a linear congruence by a
  per-block isomorphism to `ℤ_p^m` and derives the bridge criterion; we reverse it. The
  criterion is first-order over finite data and is what every consumer uses.
- **`σ*` is data attached to irreducibility.** `Irreducible.exists_isCover` produces it;
  there is no standalone function, because there is no cover without irreducibility.
  A by-product the source never states: taken literally, irreducibility *implies*
  `σ ≠ A²`, since the empty family of strictly larger stable subuniverses intersects to
  the universe.
- **Instances are lists, scopes are tuples, the variable type is a parameter.** Proofs
  delete constraints and allow repeated variables in a scope; and expanded coverings need
  instances joined over a coproduct of variable types rather than by renaming with a
  fresh-name supply.
- **Nothing is stubbed with `sorry` at the level of a definition.** `IsConnectedInstance`
  and `IsExpandedCovering` are *absent* rather than defined as `sorry`, because a
  `def : Prop := sorry` is a junk constant that downstream proofs can silently lean on.
  Absence forces the design decision; a stub hides it.

## Order of attack

1. `lem:ba-center-implies` — small, self-contained, used everywhere, adjacent to what is
   already formalized.
2. The mixed-prime linear algebra of the codimension-one step. Independent; can go in
   parallel.
3. Bridge composition — twelve source lines of relational algebra; closes both open items
   in `CSP/Bridge`.
4. The coproduct design for coverings.
5. `thm:stable-intersection` — the one hard statement in the interface, and the sole
   source of bridges.
6. `lem:bridge-from-instance` — eight hypotheses, ten pages.
7. `thm:main-inductive` — last.

## Scope

The predecessor formalized ~3.5 printed pages in ~1670 Lean lines: roughly 480 lines per
page. Excluding the complexity layer and Zhuk's §4 (XY-symmetric operations, an
independent result), the remaining source is ~100–130 pages, so **35 000–60 000 lines**.
This is a multi-person-year project and should be described as one.

## License

Apache 2.0, the convention for Lean code.
