+++
id = "N0049"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "human:tekne"
at = "2026-07-20T00:00:00+01:00"
source = "human-authored"
agent = "none"
harness = "editor"
+++

- Typing rules, Claude ==> OCaml
- Mistake: trust typing rules requires auditing code
  - Note:
    - My idea is multiple backends for high-level specifications of typing rules which themselves have rigorous semantics
    - Currently:
      - K framework: high-level framework for giving rewrite rules + syntax
      - SpecTec: high-level framework for giving rewrite rules + syntax
      - Lisp: "raw computational soup" -- but also there's a lot of code
        - Scheme
        - ACL2
        - SectorLisp
    - Want to target:
      - Ott
    - Nice thing:
      - Only needs to be a subset: rather than doing the _entire_ thing, we can write a frontend which only does one particular _type_ of language, and lowers it to a natural set of definitions + APIs
      - Multiple overlapping frontends give _consilience_
      - In general:
        - Usually: one compiler handles _all_ programs
        - Now: many mini-compilers handle overlapping subsets of programs, like an atlas on a manifold
          - This can also mean that certain subsets are handled ultra-efficiently, in a way which is theoretically impossible for the entire language...
          - Consider how a sphere can't be flattened into one map, but _can_ be flattened into two
        - If we actually have a full specification language for the spec language itself
          - Example: K is specified in K (old version only though)
        - Then we can use a frontend to lower the spec for the spec language itself in, and use that as yet another pillar of consilience
  - Neel: exactly the opposite thing.
    - The thing I've ended up doing is -- the view I've come to -- is that these AI tools are actually _really good_ at routine kinds of proofs
      - Jad: I'm viewing this theorem prover as a harness for proof
      - Neel: compiler correctness proofs are routine proofs
      - Jad: exactly what I want -- I want a _harness_ for inductions, etc -- so I write my compiler/language-spec in an ultra-high-level language, and then have the AI discharge the proof
    - Neel: point is what I do is in my type system experiments with Claude I'm doing the wrong thing to turn type systems into algorithms -- I should be using it to write a verified compiler
    - Jad: this is exactly what I'm doing -- except I want to generate WASM, not ML code
      - We can _also_ generate ML code as a _spec_ for the WASM -- especially if e.g. we also import something like OCaml_light -- which is exactly why I want an Ott frontend -- rather than support all of Ott, I want to support _exactly_ the subset used for OCaml_light as efficiently as possible and literally just discard the rest, it doesn't even need to be generally sound, just sound for OCaml_light -- again, the cool thing about an atlas is that each map only needs to be sound (in math: well-defined) for a _patch_ of the manifold -- classic complex analysis extension trick
- Exactly what I've been pushing at -- I think we work towards using AI as the "ultimate compiler"
  - Imagine writing code in high-level "math Haskell" -- so Haskell but with semantics in e.g. ZFC or GT3 or some other powerful set theory -- with _subsets_ also having semantics in weaker logic like HOL or even PA or SOA for e.g. a countable fragment
  - Then you have an AI lower that to low-level code -- doesn't have to be an AI, can also be a collection of _mutually-sound_ "atlases"
  - Furthermore, any code you generate with spec can be used as a decision procedure to help you generate and verify more code
  - And -- since this is all a simple, composable, and standard binary format: WASM -- with a few standard thin-waists: Lisp S-expressions for computation, raw bytes for data, to start -- it's very compatible with content-addressing: load the module with hash blah and the bytes with hash bleh. In particular, _other_ formats can be represented as the hash of their decoder

  The S-expressions are important as a primitive because they are inherently $n$-ary -- hence representing the content links, whereas a WASM module on its own is unary (minus imports which are ill-defined)

- Here's the reason why I want to do CN:
  - There's a LOT of existing C code out there
  - Just proving it has no UB has _extreme_ value and could attract huge amounts of funding
  - If we have something like CN, we can also do verified auto translation --
  - But more interestingly to me -- we can use verified C code as a _specification_ for things

- Neel:
  - CN is not what you want for this purpose
  - Couple of reasons:
    - First: CN is fairly inexpressive -- so your workflow is pretty much always "I am going to prove this C program implements this first-order functional program"
    - Anything interesting is proved about the first-order functional program
 - For pKVM, we have a functional model of what each hypercall is supposed to do in terms of how it modifies the page table mappings, and the CN spec is basically "each hypercall implements this function" -- any kind of isolation property is proved about the functional spec

- Jad:
  - I agree, not the long-term thing
  - I think this is good as an existing baseline -- especially since we can target a subset, again, atlas

- Neel:
  - The other issue is that CN is not what I would design if I wanted to design something for AI assistant verification

- Jad:
  - I agree again -- so what I found though is that when building the initial implementation it's _far_ easier to take something bad and tack on the features you need to make it AI-native vs. starting from a blank slate -- especially since what you can do is have a non-computable desugaring from the AI feature to the regular one

- Neel:
  - The other thing is the... this is something where I'm coming around to the point of view that C verification is a bad idea

- Jad:
  - I agree, but there's a lot of existing C code -- and I don't want to actually _verify_ it
  - Instead -- if we can _just_ prove properties like:
    - No UB
    - Determinism under this precondition
    - Implementation of _some_ first order function
  - We can then use it as a _spec_

- Neel:
  - You can prove things like this, but not very true

- Jad:
  - Exactly -- but every time it's not true is a valuable bug fix for the UB case

- Neel:
  - Not exactly -- the reason is that -- I used to be much more optimistic but now I'm much more pessimistic about C verification
  - The guarantees you're getting are not as much as you'd like
  - There's a bunch of issues:
    - C doesn't have a semantics -- as in the C standards given to implementers + programmer communities all disagree on what C should do; see Linux kernel lore like RCU
    - The C standards committee does not have a coherent view -- what views they have don't agree with the compiler implementers

- Jad:
  - This is exactly why I think this project is relevant: C is an atlas

- Neel:
  - C is multiple atlases that disagree on their overlap

- Jad:
  - Exactly -- so it would be very interesting to have a "weak C standard" as a collection of atlases that:
    - Every sane compiler agrees with
    - The real standard is a refinement of

- Neel:
  - Lots of C programs have inline assembly -- the memory model of x86 and ARM and POWER is very different from the C memory model
  - Also -- concurrency models are different
  - There's really no coherent way to relate the C worldview to the assembly worldview -- no way at the level of a C program with inline ASM

- Jad:
  - This is exactly my point -- C verification has been intractable because people have been looking for a simple atlas
  - Not even a set of consistent atlases is enough -- that's the _nice_ case
  - What I propose is a _lattice_ of atlases

- Neel:
  - If you want a real guarantee just verify the binary

- Jad:
  - Exactly!
  - I want to use the C as a scaffold for _abstracting_ the binary
  - The issue is that the -O0 program and the -O3 program will be different, probably
  - May even be _semantically different_
  - The C standard wants to relate all the programs -- semi-impossible with current hodgepodge
  - My idea:
    - Use various atlases on C to define subsets of valid program semantics at lower abstract level
    - Prove x86 assembly for various compilations _is_ in the atlas and/or prove C compilation from tiny atlas to x86
      - For example: verifying a nanopass from a subset of a C atlas to a nicer SSA
    - You can also use C to _extract_ a specifciation -- for example, consider the reference implementations of cryptographic algorithms, often written in C -- or consider decoders like zlib or zstd or similar

- Neel:
  - This is not what I'd do these days
  - If you look at F* -- they have a "Pulse" sublanguage for low-level code
  - If you have a decent enough spec you can just spend a few hundred bucks on tokens to get a verified low-level impl

- Jad:
  - I agree, no new code should be written in C as it is
  - This is about ingesting existing code and basically saying via consilience "this code probably meets this spec because under sane atlases here it does this, and also we validated the binary to actually do this"
  - So this is on a program-by-program level:
    - I apply atlas A to program P to say "you _could_ interpret P to mean semantics S"
    - I then prove that a common binary of program P actually impelements S
    - Hence, by consilience, assuming S is something that an AI/human considers "sane"
      -- e.g. zstd actually implements a decompressor
      -- it's probably what was meant by that program
  - This is what real C programmers are forced to do in their head -- I think you could automate it so a large codebase could be verified for ~100k in tokens would be the goal -- which is very reasonable for e.g. pKVM and friends
  - Once you have your semantics -- you can start getting rid of your C code, except as a historical artifact -- by translating _to the semantics_
  - And if you make the semantics deterministic:
    - It gives you a meaning for your code
    - You don't need to throw away the C afterwards either -- though you don't want to use it anymore -- since now it's a perfectly valid statement to say that you have a C_variant program where variant is the weird atlas (which might even change file by file due to e.g. a #pragma telling you which atlas page to use for that file)
    - Here, C's weird ideas about translation units help you: you could have a different atlas for different translation units, with headers in a very permissive position in the lattice
    - You can always add UB -- consider "ultra UB C" where everything is UB except super simple 100% race and cast free programs
    - I hypothesize that most C program code can be de-optimized into equivalent ultra UB C + mutexes
    - E.g. trading code is _all_ single threaded, for the most part -- concurrency is bounded to a few well-specced data structures

- Neel:
  - Even in sequential C you have to worry about races -- unsequenced expressions

- Jad:
  - Great: make them _all_ UB in "minimal C" -- it forces you to:
    - Sequence all your expressions
    - Make all your casts explicit -- except maybe a very small subset
    - Even: _annotate_ pointer casts or ownership or whatever with a comment or such
  - Without AI impossible
  - With AI million dollars
  - Neel: or even less
  - Million dollars for a big codebase that is useful -- see SQLite
  - Would be very interesting to interpret SQLite as:
    - Write a preprocessor, based on clang, which converts SQLite source to ultra UB C source where casts are all explicit, etc.
    - Prove things about preprocessed thing
    - Now: your atlas contains the spec of your preprocessor; all you need to do is:
      - Be sane
      - Support _what's used in SQLite_ -- not all of C
    - Once you have SQLite validated -- that's _extremely useful_ -- and you can compare it with binaries

- Neel:
  - I think it's a good idea

- Jad:
  - The other thing is:
    - Tobias is translating MLIR into Lean
    - He's gotten Lean to _parse_ the MLIR for SQLite in the LLVM dialect
    - But notice to get this to work you need to execute native Lean, big TCB
  - My system I think is a much nicer target for this sort of work:
    - Write the parser in WASM and validate it once -- full WASM speed, may even beat Lean since you can write it imperative first
    - Then you can have MLIR semantics
    - In fact -- an atlas over MLIR is an excellent narrow waist, and we have an _excellent_ semantics for SSA and a proof that lots of different algebraic representations of it are equivalent
    - Atlas discipline means we don't need to support everything -- we just need to throw an honest error _or_ return an honest approximation when we hit something we don't support -- and we can implement multiple different subset programs with multiple different agents, _it doesn't need to be a monolith_
  - If code is super cheap to write -- consider Level 2 UNIX philosophy -- do _less than one thing_ and do it well
  - Interesting: study higher-order combinators on <= programs:
    - Common: pipes, _structured_ pipes on typed data (very interesting since can be lowered to different things for different performance characteristics: shared memory queues, JSON RPC...)
    - Also interesting: REST, Web, kernel syscalls, UNIXisms, etc -- again, an "atlas of UNIX" rather than formalize UNIX because there's no one impl of UNIX nor-even a single bug-free impl of "some UNIX"
    - _Descriptive_ vs. _prescriptive_ semantics of PL
      - PL was not taken so seriously before because it was prescriptive
      - Descriptive PL is only possible with ridiculous amounts of _unskilled_ labor -- hence AI
      - Now prescriptive PL becomes useful again rather than a toy since it lets you algebraically related descriptive PL of billions of LoC of existing source
      - If you've got a decentralized prover which scales and can have a Git repo as a first-class API -- you can prove things about parts of real code and reuse those facts
    - Weird operators that were impossible before:
      - Join of two programs
      - Meet of two programs
      - Generalizing: tensor products and wedge products and other such interesting categorical/profunctor operations on programs living in a spec lattice

- Jad: ultra concretely, here's what I have that I think makes a subset of CN/MLIR/etc a good idea:
  - SMT support: we can import proofs from CVC5 including Farkas certificats
  - SAT support: we can import _large_ proofs from Cadical -- including bitvector-style proofs on large bitvectors as well as problems involving very large #s of variables -- I'm still building a full bitblaster however because our bitvector API is very ugly and I'm punting the nicer bitvector API to after the TCB rewrite since our TCB is not very bitvector friendly -- the primitives are nats and bytes because they were simple, and it turns out bitvectors are an important primitive and should _not_ be done with a crappy wrapper, lesson learned
  - Lisp support: in progress, but useful as a computational substrate -- also as a substrate working on implementing and proving equivalent to various notions of computability:
    - Binary lambda calculus (mostly done)
      - Working on: symbolic untyped lambda calculus; then STLC + System F
      - Right now focused on Lisp -- want untyped lambda separate from Lisp codebase since different API with some isomorphism
    - SKI combinators (done)
    - Turing machines
    - Minsky machines
    - Automata hierarchy:
      - DFA, NFA, pushdown, ...
    - Compilers + relations between them, simulation, etc -- as high-level APIs used by everyone
    - So the idea is e.g. if I want to do "induction over computable functions"
      - Use compiler to get binary lambda calculus
      - Work with that

- The vision I have is:
  - Very small TCB _expressive enough to support arbitrary acceleration_ -- rather than an "oracle set" you have an "accelerator set" -- _almost_ the same thing but more restricted:
    - Base case: no accelerators at all -- log(n) performance on int/nat operations since a big number is represented as e.g. double(succ(double(succ(zero)))) -- I actually implememented decision procedures and tactics for e.g. addition, etc. on this representation
      - Why have this base case without even accelerating integers?
      - Because: the soundness of integer acceleration needs the semantics of integers to be real integers
      - So if I reason about the semantics of integers as a test (e.g. sanity checking that addition is commutative)... but this reasoning depends on the integer accelerator... we get a loop where a wrong integer accelerator can verify itself
      - Hence the discipline of accelerator free reasoning with a tiny 3k LoC TCB implementing _just_ HOL-omega over first-order-logic (so basically a weird Isabelle/HOL-omega)
      - All our:
        - Metamath import
        - ACL/2 import
        - Lisp import
        - SMT and SAT import
      - Compiles in the TCB free fragment -- acceleration is _optional_ even for integers, but gives an order of magnitude + speedup
    - Eval case: "the usual suspects" -- the only one you really need here is "bytes" for content addressing, which otherwise is actually completely separate from the rest of eval -- so each of these can actually be slotted in independently. It's good because it means each accelerator can be independently audited and is modular.
      - Bytes: hold a byte vector, operations: cat, index, cons, snoc, len, ...
      - String: to/from UTF8/UTF16 -- this is where we want a spec beforehand written in pure HOL for obvious reasons since this is complex but we also do it a LOT -- also need a char type -- likewise cat, index, cons, snoc, len, iter as a list(char) -- convert to bytes for the byte op equivalent. UTF16 support necessary for interacting with the JS world nicely -- this all runs in a browser! -- eventually might remove for Bytes + WASM (WASM*)
      - Nat: obvious -- implements Peano + sub + mod + div -- WASM*
      - Int: obvious -- implements usual suspects; backend for accelerated SMT -- WASM*
      - Fixed-width bitvectors: also obvious, currently implemented using Nat which leads to great bitblasting pain for "simplicity" -- this should be first class even with WASM since WASM takes it as input/output and also it's how computers actually work...
      - Lists: useful because it turns out a Vec<T> is a common thing and has good cache locality -- funnily enough, *not* WASM* because this is polymorphic -- also I support an immutable list thing with finger trees; lots of TCB but Clojure shows this is a nicey and also it just imports a crate so "not real TCB it's a dependency bro"
      - Sets: same as above -- only half-implemented and used for context, but if we use it for contenxt so it's in the TCB might as well expose it for terms too
      - Ditto for Maps
      - Maybe: Decimal -- so we all of JSON -- I'm against accelerated Rational though since there's lots of possible implementations, but Decimal is important
      - f32 and f64; with a FP spec -- see why we need something TCB free, otherwise an error in the FP spec makes things inconsistent before we even started -- I just make arith ops canonicalize but can do something relational later probably nicer!
  - Core features -- compose with eval, don't actually need any eval _except_ bytes (mandatory).
    - Content addressing -- this is not yet implemented, but I have a plan for how to do it
      - Right now we have content-addressed content, but you need to fully resolve it before proving things about it
      - However -- we can not only prove things about unresolved content -- but in fact be _honest_
      - Define a _relation_ seen: (hash, key, blob) for a keyed hash (like BLAKE3 with regular BLAKE3 having key = "default").
        - This is a finite relation: "only a finite number of hashes have been computed in this world"
        - Then we represent content addressing as two axioms with a relaitvely simple model (take seen empty or any collision free set):
          - Seen is finite
          - There are no hash collisions in seen 
          - Seen obeys the BLAKE3 spec
          - Level 2: hashes are acyclic: i.e. under the substring relation, a hash doesn't appear in some ancestor of that hash -- optional stronger assumption -- this upgrades your Merkle data structures; often Level 1 is strong enough
        - Can have multiple seen sets for different cryptographic functions:
          - SHA256, SHA512, etc -- keyed or unkeyed
          - Can even have explicit seen sets:
            - E.g. a Git repository can be a seen set for SHA1
            - Instead of adding it as an assumption, can _verify_ it by going over the blobs and showing no SHA1 collision -- even in-prover -- and then hash the _whole_ repo using an actual crypto hash
            - In fact -- the correct way to verify it is to build a Map<SHA1, SHA256> proved sound w.r.t. to the seen relation -- and relations and maps are our core primitive
        - Can generalize to PKI:
          - relation signatures seen: (pubkey, signature, blob) 
          - relation knows: (id, privkey, pubkey) and signed: (id, blob)
          - Such that:
            - knows and seen are finite
            - if there exists a signature, then someone who knows the privkey signed the blob
          - Can express trust as an _assumption_, rather than an axiom, like any other
            - I trust someone who knows the privkey for pubkey to be honest about blob
    - Database serialization:
      - Goes with content addressing
      - The idea: support a _subset_ of SQLite consisting of relations tagged with their mathematical meaning
      - This is how you export a theorem and sign it
        - So a database contains theorems
        - A database contains signatures of theorems
        - A database itself can be signed
        - A database can contain other databases either via hash or in rare cases by embedded blob
        - A database can contain _ignored tables_ for arbitrary user metadata with no mathematical meaning
        - A database can also contain proofs
        - So e.g. for a theorem T:
          - Look up signatures JOINed with my trust set, validate
          - If no signature, look up proof and execute
          - Proof is a WASM script -- WASM metadata and/or table metadata tell me what LCF APIs to link it up with
          - This is the TCB rewrite I have planned -- low LoC because all the complex lookup, synchronization, etc is delegated to SQLite
          - All I need is the language for writing down table meanings + assumption sets -- based on HOL omega, equivalent to what we already have
          - Makes it really easy to serialize and sign the state of your kernel:
            - Dump in memory DB to a file
            - Sign it
          - Makes it really easy to join kernel state from concurrent kernels:
            - VACUUM, JOIN, DUMP

- Neel:
  - Martin Kleppmann -- database guy @ the lab 
    -- and Owen Lynch is a PhD student at Oxford
    -- the geolog guy, now called Colm
    Got a bunch of money from ARIA to build a database of mathematical facts
  - Jad: I know about geolog, Becky talked to Owen Lynch about my ideas, and geolog import seems like a great thing in the thing
  - It's just that it doesn't quite exist yet
  - Jad: they're on the right track with the DB thing -- the reason I didn't mention it is because for covalence the DB is an implementation detail and in fact not even currently implemented
    - Basically I found out that since our bottom layer is first order
    - Our architecture is:
      - First-order, positive logic -- foundation layer or maybe _substrate_
      - Higher-order polymorphic logic (HOL omega) -- foundations or _metalogic_
      - Lots of stuff: ZFC, ACL2, ... -- _object logic_
    - The bottom layer:
      - Can be persisted in a DB if we make relations a primitive -- and relations are a much nicer API than what we have now
      - Lots of error-prone code can be therefore replaced with simple JOINs, etc -- for n-ary AND, OR, etc.
      - DB is nice because it also has the fixed eval primitives we want and no more:
        - Bytes
        - Strings
        - Fixed width integers
        Too bad the latter two are very buggy -- but bytes only is a good start and I _almost_ trust SQLite if I trust anyone
      - DB is also nice because it gives us an untrusted foreign protocol
        - For example -- we could have a Postgres or MySQL (or rather, Dolt, which implements MySQL)
          -- or eventually a covalence since a DB is a cool thing to formalize (long story)
          -- instance serving theorems live which an API endpoint could query for frontend-only non-verifying consumers

  - If relations are the base: here's a useful relation:
    - `executes: (executor, input, output)`
    - That's it. Then:
      - different WASM subsets are assumed as an axiom _implemented_ by different executors:
        - wasmi
        - wasmtime
        - V8
        - ...
      - You can audit the trust set because even now you can dump it to an S-expression
        - Later: dump to JSON, S-expression was for Reason (TM)
      - Hard part: `input/output` isn't _really_ WASM -- we also want state
        - Idea: `executes: (executor, program, input, start_uuid, output, end_uuid)`
        - Then can use start_uuid: 0 for initialization
        - So for example, if I initialize a new WASM instance in wasmtime, I'd write:
          - `(wasmtime, my_module, "start", 0, (), "some UUID")`
          - Afterwards, next function call becomes: `(wasmtime, my_module, "some UUID", "some function", "some output", "some other UUID")`
          - Now stateless execution pairs, etc, or complex things like multiple sequenced operations or whatever is just an SQL query away with the appropriate indices
      - Cool part: _this generalizes_:
        - Executor can be: a docker container, with startup being creating the container
        - x86, RISC-V, in QEMU, on hardware, run a C compiler, AWS nitro with remote attestation, _whatever_
        - You specify it in _regular_ HOL, not some weird DSL -- just like your Merkle structures are _also_ specified in regular HOL -- the only atoms are relational algebra -- a tiny subset of SQL!
        - You execute it however you want and write your DB, which you sign as valid executions
        - Someone can prove things using your execution DB and _either_:
          - Persist the executions -- so you only trust the execution of the remote
          - Persist some subset of the executions -- e.g. skipping steps (so saying for example that there are steps between UUID A and UUID B but both of them derive from a valid start initialization and are the same module -- or alternatively that they are different modules) -- so now all you're trusting is the SQL impl on the remote + the execution
          - Persist only the proved theorems, dumping the execution altogether

-  What I propose in a few sentences:
  - Get the SMT and Lisp stuff _shiny_
  - Actually do the SQLite + content + WASM stuff -- then the prover is _complete_, vs now
  - Start on SSA and an internal compiler toolchain
  - Build the future, yo!


- Seeing more "I'll get Fable to mechanize stuff"
  - Good enough to exploit incoherences for pain
