So the main purpose of this repository has been to build up an experimental sketch of the `covalence` theorem prover 
-- the problem is I find it's hard for people (and therefore probably agents) to get a handle on it, since there's lots of overlapping designs. At the same time -- I still want to push on all the various angles of the vision in one repository, since I don't think it's yet ready to distill out a starting product doing just one specific thing (once the core prover is done, that can be a start, but that needs content-addressing implemented).

I think an interesting idea would be to eventually transition this repository to `covalence-sketch` 
-- since right now this is essentially a vibe-coded sketch of what covalence would look like
-- and then make a new `covalence` repo where the commits and branching structure are carefully planned and copied over.

Then new sketches can be branches on top of the `covalence` repo's solid core.

We're probably not ready for that yet -- what I'm thinking we want is to *fix* the high-level API for:

- The core kernel API
- WASM compilation and interpretation
- WASM acceleration of the core kernel
- Content addressing
- The server/client (via HTTP + WebSockets)

Then, once we've got all that ready, we can start copying it over "already in final form" 
with the comments and docs cleaned up and the architecture solid,
with each piece of the code carefully reviewed as we copy it,
to get a much higher-quality and better indexed codebase.

That said -- we probably want to make sure we're "actually done" first so that we've got a solid base to build off
-- then we can continue development by making more "spike/sketch" branches 
and then carefully copying over to feature branches once we've got something with the right shape (TDD style), 
which we then PR and merge into main -- we might eventually even have a develop/main split with the invariant being
that what's in develop must be green and clean, while what's in main must actually be _sound_ with high confidence.

Instead of a separate repository, we might also just make a separate branch
-- so for example reset `main` to the empty commit with current `main` becoming an `initial-sketch` branch
-- this might actually be an easier approach for various reasons 
(we don't have any links or dependencies now, and the only real checkout is here, so we only get to do such aggressive ops now!)

So to be "actually done", we probably want some important extension features:

- SQLite ser/de, and SQL interop in general
- E-graph support, which was of course our original selling point -- and should make the WASM/WIT use story a lot easier
- Importing proofs and files as WASM
- K framework support -- cross referencing SpecTec WASM with K WASM is a very cool stretch goal
- Lisp support, and in particular
- ACL2 support
- System interop in general -- e.g. having a predicate for "this bash command ran here" at the base level, etc.
- A nice Python API for _each_ layer -- to help agents and to force us to make sure dynamic support is first-class
  - The base layer -- this is probably where we can put the system interop lore
  - The middle layer -- algebraic theories in Python is also independently cool and useful, imo, especially w/ E-graphs
  - The top layer -- internal logics in Python; including the previous layers as injections, essentially

The reason we want these extension features is essentially we want a solid set of:

- APIs to target
- Applications built on top of those APIs which should run unchanged

We should probably split each extension into its API component and its application component (many of these will have just one or the other)

Some other things to think about:

- We probably want better names for base/eval/top logics -- especially since there's more than one top layer; indeed, we can view:
  - Metamath -- instantiated @ ZFC, GT, HOL, IZFC, etc., as one family of top logics
  - ACL2 as another -- or perhaps an instantiation of Lisp
  - K as a third
  - SpecTec as a fourth
  - SMT-LIB is an interesting case, since theories are not really fully defined... I need to research this more!
  - Then there's PA and SOA -- which we natively deal with as a subset of Metamath
  - We also want support for Dedukti, STLC, and System F as important "carriers"
    - I need to check -- is HOL-omega powerful enough to prove the consistency of System F? What about just plain HOL?
    - Eventually we want the "Categories for Types" machinery, specifically!
    - On the other hand, Dedukti is interesting both for Edinburgh/LF in general and Coq + Lean export specifically
  - Then there's GT3
  - WASM itself could be viewed as a top logic -- indeed this was in a way the original design, with WASM acting as a "strange loop" between the top and the bottom

- What exactly is the current state of our Lisp/ACL2 support?
  - How can we carve out clean traits for:
    - Producing S-expressions
    - Parsing out S-expressions from their HOL representations
    - Working with Lisp terms/ACL2 terms, doing reductions, etc
    - Would be especially useful if the same trait could work with:
      - A test Lisp interpreter for unit/integration tests and fuzzing 
        -- especially the "parsing out" part can help us show we're proving what we think we're proving
      - Different HOL representations of S-expressions 
        -- potentially with casts between them as another trait
        -- so note the "parsing out" bit needs a deparse tactic to go with the parse tactic