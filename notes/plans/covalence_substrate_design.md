+++
id = "N005H"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "human:tekne"
at = "2026-07-21T00:00:00+01:00"
source = "human-authored"
agent = "none"
harness = "editor"
+++

# covalence substrate design

goal: design a substrate for covalence based on the following ideas:

- use SQLite as a format for:
  - unit of node state
  - proof export
  - proof import
- so: need to have a substrate logic with a close connection to relational algebra over the basic SQLite datatypes (TEXT, INTEGER, REAL, BLOB -- then NULL)
- we want a model of an SQLite database, which lets us determine:
  - how to interpret an SQLite database as a bunch of terms/theorems, and, given such an interpretation:
    - use it as a persistence layer:
      - read off individual terms/theorems
      - store individual terms/theorems
    - use it to ground content-addressing -- a particularly relational form of theorem (note the current CAS cache is an SQLite database!)
    - use it as a _batch_ persistence layer:
      - SELECT tables of terms/theorems, filter out sub-databases in a coherent way
      - import one database into another -- use content addressing here!
      - attach to multiple databases from a single node
      - use above + export to merge databases
    - use it as a storage medium for _untrusted_ terms/theorems:
      - decidably import and typecheck terms
      - validate theorems by replaying stored proofs -- store WASM in tables, both directly and via content addressing; as well as other data
    - mutate it in a soundness preserving way:
      - have ops add and remove terms/theorems while leaving the database true; including in bulk and between DBs (so as a superset of batch persistence)
    - query it to get new theorems:
      - basically the above but with a temp table

- Let's model (the part that we're interested in of) an SQLite database as consisting of:
  - _tables_, each of which has:
    - a _name_
    - a _strictness_
    - a _schema_ containing:
      - a set of _columns_, each of which has
      	- an _affinity_ -- not a strict type given how SQLite is
      - a set of _constraints_:
        - foreign table constraints
        - check constraints, not null
        - uniqueness constraints
      - an optional rowid column
      - a primary key (may be the rowid)
    - a set of _rows_ which for each column carry a value in (TEXT, BLOB, INTEGER, REAL) or are NULL (viewed as _no value_)

- Note we don't model indices here, since that's purely a speed thing -- generated columns we'll think about later

- So more concretely, let's assume we have some way of assigning metadata to some _subset_ of tables in an SQLite database;
  our goal is to think about which metadata we need to give _meaning_ to these tables, in a way compatible with the above.

  Here's some of the meanings tables can have:

  - Recall that a _theorem_ is just: this Expr<bool> is always true in this Context -- for MThm currently called a "Language",
    but basically abstract rules + the TCB implementing them.

    So one meaning could be:

    Here's an Expr<bool> with placeholders for columns Col("name", repr)

    - BASIC: this expression is true where the placeholders are filled with columns drawn from an _arbitrary_ row in the table

    We already see some problems: how do we deal with NULL, etc. 

    repr here says how to map an SQLite type (TEXT, BLOB, INTEGER, REAL) to a covalence substrate type -- here a Rust type

    that includes NULL

    the reprs out there are defined by the context 
    -- or we could represent the SQLite types as fixed Rust types, and then reuse the existing machinery here.

    do we exclude rows for which this translation fails? or do we also assert the translation never fails?

    -- that is, Col("name", repr) must be compatible with some Schema, which we _also_ assign to the table

    or do failed translation rows become epsilon-choices?

    the other very important case of reprs is _names_, which we'll get to later -- these interact with content-addressing in important ways!

    I like schemas but we need to think about it! Maybe it could be per-repr... 
    with schemas, different reprs could require different things of their schemas,
    with an Expr being well-typed _with respect to a schema_ -- column-free meaning schemaless.

    Also some more advanced options which *may* be useful; but probably go under the next bullet -- which make the above a tad more complicated:
    
    - this expression is true for _at least one_ row in the table

    - this expression is true for _no_ rows in the table -- i.e. is always false

    - this expression is false for _at least one_ row in the table

    So the classic quaternary logic, basically.

  - Rather than parametrizing our theorems on columns, we could parametrize theorems by the _table altogether_
    -- viewed as a set/relation RowType -> bool -- which of course means we need a way to go from rows to RowType, handle nulls, etc.

    - Honestly actually -- not *too* difficult... 
      an Expr<T> under the appropriate schema gives us a way to "interpret rows as T". That works.

      And we already need one of these for the theorem thing...

      So the theorem thing really just becomes the special case: All(table interpreted as a set using Expr<bool>)

      With the other cases being: Any(table interpreted as a set using Expr<bool>), Not(All(...)) and Not(Any(...)).

      So all we need is basically binding for schemas... 
      that said if we interpret schemas we have to interpret binding _anyways_
      though this means SQLite types just become regular Rust types that it happens a table can provide.

      Can think about this...

      Of course -- we can also just have a variable Table(schema, Expr<bool>)... or even Table("table_name", schema, Expr<bool>)

      The latter of course then opens the door to _general_ truth, 
      rather than truth bound to a specific table -- which might be the right move; a new perspective.

      Thing is -- specific tables are useful for identifier lore -- then we also need to think about schemas + visibility.

      Hmm -- it may make sense to have truth be generic while schemas + visibility are tied to tables?

      Let's think about it... I suppose much of this has to do with what metadata repr we go with...

    - A table can be viewed as a Map<K, V> as well; where K and V are maps on expressions 
      (so in particular K must be unique for rows) 

  - Names -- so Col("my_col", Int) might mean interpret my column as a covalence substrate Int 
    need to think about behaviour otherwise: epsilon? schema? 
    - schema is nicer and plays well with STRICT tables -- and we want to keep track of the variables in an Expr anyways
    - on the other hand, epsilon composes well: I can give the column _two_ meanings, both as "always true" theorems
      - the real meaning: some expr involving Col("my_col", Int)
      - the schema: Col("my_col", Is<Int>) 
        -- since this is always true, we never hit the epsilon-behaviour as above,
        and are spared the bug prone job of checking our SQL queries against the schema.

      while this is _potentially_ more elegant, and at least more minimal -- 
      one of the positives of the schema approach is basically layered concerns:
      schemas can be checked automatically and decidably and compose with well-understood rules,
      while general theorem composition is deeply undecidable.

      plus, schemas can _imply_ theorems

    Anyways... what if instead we said Col("my_col", Def<Type>)?

    What we'd do is interpret _every_ unique value of my_col in the table at any given time as an _erased_ value of type Type
    -- each value being _potentially_ distinct.

    So note two different rows both with my_col = 3 or my_col = "hello" get the same value -- and hence on insertion,
    if some rows with my_col = 3 already exist, we must either:

    - remove them

    - ensure the value we're erasing is equal to the value for those rows -- but of course, we don't _know_ the value for those rows!
 
    note this is not a problem if my_col is in fact UNIQUE -- e.g. a ROWID, probably the common use of this!

    Which comes to the next part: we can _infer_ the value for those rows from the relation, maybe.

    For example, if we have the meaning:
    ``` 
    Col("tm", Def<B>) = App(Col("lhs", something: Fun<A, B>), Col("rhs", something: A))
    ```
    and we have that: 
    (a) App(someLHS1, someRHS1) = App(someLHS2, someRHS2) (knowledge from elsewhere)
    (b) (5, someLHS1, someRHS1) is a row in the table
    then we can safely insert (5, someLHS2, someRHS2) into the table
    since the two interpretations of 5 (from the original and the new row) must be equal;
    on the other hand, without fact (a), we'd have to first remove (5, someLHS1, someLHS2) from the table

    We'll call this type of column a DEF column.

    The other part of the puzzle is a USE column -- where we interpret a value (say an integer)
    as the erased value corresponding to a given (table, column) pair
    --
    here, we might also want to support virtual tables of sorts;
    e.g. a DEF column backed by an integer counter producing fresh IDs.

    An especially important type of virtual table would be the SEEN set of a hash function
    -- though we might in fact want to keep this totally separate from the table mechanism and
    dealt with only within the substrate. Let's think about this more.

    Going with the schema approach, we might say:

    - Col("name", Repr) is valid if the schema guarantees all value for "name" satisfy the requirements of Repr

    - Col("name", Def<Type>) is valid if the schema guarantees... hmm... 
      I guess it can always be valid, with the values just usually unconstrained?

      We probably do want to keep track of which columns we have use a def for in the schema for an expression, though...

      Also -- if we ue a column as two different types, e.g. Def<Type1> and Def<Type2>, 
      those should be totally independent mappings -- now we need to think about type representations, too,
      along with term representations (and repr representations) in the table. 

      Terms should probably have special tables -- can also use the = relation, but it's both a pro and a con
      that that fixes types unless we muck about with polymorphism.
  
      We need special tables for types and reprs and such anyways -- so might as well have one for terms, too:
      can have both!

    - Col("name", Use<Type>) likewise should be tracked -- and the Use keep track of the source.

- In general -- on the type side of things, we want to change the Expr trait to keep track of the Schema as an associated type

- We may be able to do double-duty here:

  - Define a notion of variables -- can compute things about the free variable set both dynamically (for the Any case, via a derived trait) 
    _and_ statically -- so we want a constant safe over and under-approximation of the variable set exposed by the API;
    I'm thinking of some constexpr tricks here; maybe a trait like E: HasVar<V> for expressions E with:

    - for Var<I> where I is a marker: HasVar<V>, const STATIC_HAS_VAR: bool = typeid<I> == N; const STATIC_NOT_HAS_VAR: bool = typeid<I> != N; 

    - for App<L, R>: HasVar<V>, const STATIC_HAS_VAR: bool = STATIC_HAS_VAR<L> || STATIC_HAS_VAR<R>; ...

    - for Val<V>, all false

    then dynamic methods

  - Then since lots of different types can be variables (including user-defined extensions)
