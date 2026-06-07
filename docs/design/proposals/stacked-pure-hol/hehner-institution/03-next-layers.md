# Next Layers

These notes start with Pure and HOL because that is the trusted center the
proposal is trying to stabilize. But the same crosswalk extends outward.

## The immediate continuation

Once the Pure/HOL pair is clear, the later layers can be described the same
way:

| Later area | Hehner / `aPToP` reading | Institution-theory reading |
|---|---|---|
| OpenTheory packages | Packaging and dependency structure for already-logical content. | Theory/package transport for HOL-family institutions. |
| Oracles and observations | Additional scoped fact collections, never ambient truth. | Conservative theory extensions in designated fragments. |
| Store / namespace / mount | Bunches of rows and facts later frozen into content-addressed packages. | Structured theory data and transport machinery around the logic, not the logic itself. |
| Formats and keyed validity | Packaged refinements over carriers, with explicit identity discipline. | Extra institution-like validity layers and bridges, not raw kernel types. |
| Morphisms / base-shift / commutative diagrams | Explicitly packaged translations, not silent coercions. | First-class institution morphisms/comorphisms. |

## The recurring pattern

The repo-wide pattern stays the same:

1. collect facts extensionally
2. package them explicitly when identity matters
3. keep the hosting logic separate from the package format
4. keep translations separate from both

That is the common discipline behind:

- Hehner's collection vs packaging split
- the repo's `THREE-CORNERS` and `NO-GLOBAL-LIE` invariants
- institution theory's logic/theory/proof/translation split

## Suggested follow-up docs

If this crosswalk becomes useful, the next natural documents are:

1. **OpenTheory through the same lens**:
   package transport over HOL, not "another logic".
2. **Oracle/store layer through the same lens**:
   observations, Merkle witnesses, and mount facts as scoped theory
   extensions plus package discipline.
3. **Morphism layer through the same lens**:
   explicit directionality, preservation claims, and commuting diagrams.

That would yield a full "Covalence in Hehner + institution language" series
without pretending the whole repo is already formalized that way.
