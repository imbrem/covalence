+++
id = "N0056"
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

A good API here is one where we can model kernel state as an SQLite database.

# Rust Surface Idea

So _everything_, even MThm, should be relational in flavor.
For example, we could define a `Set` trait with

- An element type -- elements are `Expr<Self::Elem>`
- A _witness_ type -- what's actually _stored_

Then an MThm of a set stores the witness and tells you what `Elem` are in the set.

A relation is a set which can have columns projected out of it, whether numeric or named
(probably numeric and then with names optionally assigned to the numbers).

We want a connection with SQLite datatypes -- so a set which can be serialized can have its elements as rows...

# SQLite ideas

So SQLite columns have different types here. Let's say a table can correspond 
(in some master metadata table) some Rust set type as above.

Then each column may be (a column can do multiple duty)

- Keys defined in that table, which can be primary but don't have to be

  The idea is that each value of this key corresponds to some opaque value, 
  chosen by something like epsilon(type, "name") at the _substrate_ (not HOL!)
  layer (so even e.g. a chosen term).

  Let's call these DEF(ty) for some (substrate) type ty; or just DEF

- Keys defined in _some other table_ T as above; uses a foreign key constraint

  Let's call these USE(T, ty) for some (substrate) type ty; or just USE

- Keys defined in some global unrealized relation (which a table may be a subset of)
  -- think the "seen set" for BLAKE3 or SHA256 or the SHA1 keys in a Git repo
  -- think about this.

  Can also include e.g. a global counter for fresh names? Etc?

  Let's call these NAME(ty) for some (substrate) type ty

- Data

- Metadata -- anything not referenced in the relation (which can reference column names)

Then say we want to store terms of the form app(a, b) of type O in table T, where a : I -> O and b : I.

Well -- if we restrict a and b to come from some other tables TL and TR, we could store them as rows
of

- RELATION: tm = app(lhs, rhs)

- COLUMNS:

  - tm (integer ROWID) -- DEF(O)

  - lhs (integer) -- USE(TL, I -> O)

  - rhs (integer) -- USE(TR, O)

Note that the relational structure here requires everything to be of the same type!

We could also have a special table kind for storing terms in a compressed fashion
-- but that's actually not _particularly_ important since _internal_ terms like HOL all have
type HOL

That said 
-- it might make sense to have special support for storing a sum of relations with 
some discriminant -- interpreting the schemas at different types -- or even some basic
polymorphism even at the substrate level for storage purposes. Discuss.

Giving every column exactly one type 
(its SQLite type pushed through one of a small set of fixed functions as an annotation)
and then using that in a relation seems the right way to go -- it's just the ID columns
we need to think about and which tempt us to support things like polymorphism;
then there's also (much more relevant) the idea of e.g. supporting dependent table sources
as well as sums; for example:

- A table of binary constructors (ID) (BINOP) (LHS) (RHS) -- _quads_, or 3-address instructions, basically!

- A table of unary constructors

- Etc...

Of course a unary constructor is just a binary constructor ignoring the RHS and so on -- but could make sense e.g. for separate tables for app, bytes, and so on...

That said, given a table of HOL terms Tm, a table of HOL types Ty
we could then store e.g. the HOL typing relation as

- RELATION: hasty(tm, ty)

- COLUMNS:

  - ROWID (ignored, implicit)

  - tm (integer) -- USE(Tm, tm)

  - ty (integer) -- USE(Ty, ty)

But if we had a _fixed_ type fixTy, we could just go with

- RELATION: hasty(tm, ty)

- COLUMNS:

  - ROWID (ignored, implicit) -- or could go without ROWID; both should work

  - tm (integer) -- USE(Tm, tm)

-- or in fact could go without ROWID; both should work

Likewise, lots of tables for the same relations.

So all we need is a way to store the relations themselves
-- which presumably we can do in another table; if we have the polymorphism for it, at least!

Likewise -- HOL terms, representing contexts as just a single term (the AND of their elements, say),
could be stored as

- RELATION: imp(lhs, rhs)

- COLUMNS:

  - ROWID (ignored, implicit) -- or could go without ROWID; both should work

  - lhs (integer) -- USE (Tm, tm)

  - rhs (integer) -- USE (Tm, tm)

On the other hand, if we wanted to have a proper type Ctx of contexts, while we have context formers,
we may want a closed "set former" table, maybe, with rows like

- RELATION: mem(lhs, rhs)

- SPECIAL: COMPLETE(rhs) (i.e. for all rhs in the table, lhs mem rhs iff it's a row -- we'll need to think about completeness here)

- COLUMNS:

  - ROWID (ignored, implicit) -- or could go without ROWID; both should work

  - lhs

  - rhs

A multiset could also be done this way if you wanted to 
-- but would need the rowid since duplicate rows are information here

Now what's cool is this can be merged with the SQLite blob store (which can just become *always* the default local blob store) -- indeed, content addressing is just a table

- RELATION: id = blob \and cas(hash, key, data)

- COLUMNS:

  - id (integer, ROWID)

  - hash (blob)

  - key (optional blob)

  - data (optional blob)

just like now!

Back to ROWIDs -- might make sense to support field@id for row with id id
-- then could also refer to a hash as hash@id, key as key@id, and data as data@id,
so no need for the id = blob constraint.

In the case of the old id = app(lhs, rhs), this is still useful:

id refers to app(lhs, rhs)

lhs@id refers to lhs

rhs@id refers to rhs

Can have variants for optional fields vs mandatory -- corresponding to foreign key constraints?

So all we really need is:

- How do we store relations in SQLite

- How do we _specify_ a grounding between base relations and Rust types 
  -- one which is flexible and partial
  -- as well as specify the TCB too, perhaps, so one DB can hold multiple TCBs as well
  (with usual tables having a fixed TCB:, say -- though some tables may have a column determining their TCB by ID, for example?)

  The TCB can also help determine the grounding -- got to think about this

This is also where we make things more Rust independent -- having everything be relations and first-classing the concept of columns (with a set also being viewed as a "single column relation")
makes things generic (and implementable e.g. in dynamic languages -- having multiple impls of the substrate should really help validation efforts in the future) -- then we're saying "this TCB, written in Rust, perhaps anchored to e.g. the hash of a software manifest + the hash of the whole Cargo.lock it's compiled into + ... ==> these relations are grounded".

Then WASM execution is the big one -- what we probably want is a table for _instances_

The idea is: an abstract type of e.g. a module instance or similar, with columns like

- STEP(runtime: int, op: int, before_state: int, input: int, output: int, after_state: int ROWID)

- START(runtime: int, start_state: int ROWID) (or maybe STEP(runtime, start, "empty", code, NULL, instance0))

Indeed, might even want to represent things like linking, so e.g. for a WASM module and/or component,
something like (maybe as step kinds, maybe as relations, discuss)

- preinit = START_INIT(runtime, "empty", module_bytecode)
- preinit1 = LINK_MEMORY(runtime, preinit, "name", params...)
- preinit2 = LINK_MODULE(runtime, preinit1, "name", some_other_module)
- preinit3 = LINK_FUNCTION(runtime, preinit2, "name", some_function)
- preinit4 = LINK_FUNCTION(runtime, preinit3, "name", some_magic_function)
- ...
- state0 = FINISH_INIT(runtime, preinitN)
- state1 = CALL(runtime, "some function", state0, input, output)
- ...

This can let us support lots of runtime types and information:

- Kinds like WASM, x86, RISC-V, etc.

- Specific versions and subsets: WASM 3.0, WASM LIME, etc...

- Specific trusted subsets: WASM 3.0 but we only trust WASM LIME, etc...

- Specific implementation/trust information: wasmtime, wasmi, x86 on AWS Nitro, a specific chipset, QEMU

And use state as a key for metadata, e.g. a table (state, start_timestamp, end_timestamp, machine_id)...

Then we can work under an assumption, e.g. that the LINK_FUNCTION relation or the FINISH_INIT relation implies some HOL relation

--

what we probably want is _every_ relation to lift to an _uninterpreted_ HOL relation unconditionally;

then we can have a regular HOL conditional that (if uninterpreted HOL => WASM spec) then (bleh) or similar.

In general, we can use the relational structure to separate out "axioms" and "conditions" at the HOL level without complicating our metatheory too much
-- for example storing the table

fixedAxioms \cup ctx |- tm with tables ctx, tm

Likewise -- meta judgements, e.g. about numbers of free variables, locally closed, etc, are perfectly valid substrate relations (note all the = above was meta equality at the substrate layer, not HOL equality!) -- e.g. we can even store something like a table with RELATION: max_bound_variable(tm) = bvi where bvi is an INTEGER column; or use the set representation to store which free variables are contained in a term, or store that a free variable is not contained in a term, or store a free type variable is not contained in a type, store rank information...

--

note we need to be careful of SQLite overflow when dealing with INTEGER columns in general!

Then things like e.g. a metamath DB or things in general should be stored as:

- The HOL relation, parametrized by

- Inputs in the substrate lifted to HOL -- with the primitive lifting for bytes being all that's necessary, and fixed integers + floats + strings (TEXT) being _useful_ (and booleans from 0 to 1, say -- so we need a BOOL usage for a column too it seems -- though can define as notZero on integers!)

So note: the separate substrate is because the computational stuff is separate from the meaning we assign it, which can be independent of computation.

Likewise this splits TCB into two parts:

- The HOL assumption set TCB -- what meaning the computational stuff has

- The execution TCB -- that the computational stuff itself is true

The computational stuff should be defined by globally unique well-known names -- that is, O256 generated the original covalence way, from hashes of specs rooted at a well-known O256 and/or just random numbers! So no confusion where you and I disagree on what "WASM" means -- it's a 256-bit integer you simply can't use by accident. That's what the substrate is for: trusted filling in of tables for well-known names of WASM, HOL-omega, but also other things (say x86, whatever) -- things with English specs, + metadata (e.g. what machine, what key, what time...) as needed via more tables with _more_ well-known names.

So

- Database trust is: the well-known names are what they say they are

Then on top of that, as a regular but segregated set of HOL assumptions, we have

- The _observations_ of the well-known names imply X is derivable (substrate flavor -- or HOL logic _about_ object logic like Metamath)/X is true (HOL logic flavor)

Interesting thought: if every table has a TCB, does it make sense to have the HOL assumptions about observations at the _substrate_ layer like the TCB assumptions, making it into a HOL itself (which seems the right move and an elegant one -- vs the HOL-omega of the middle layer), or within the middle HOL.

Note can do both -- can even be useful to: seems a distinction though: if in TCB T, (observation O ==> H) ==> X then in TCB T + (O ==> derivable H) we may not be able to derive X without a special rule without at least replaying the proof. Which is interesting.