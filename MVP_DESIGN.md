# MVP Design

This document contains some the features required for `covalence` MVP.

We're going to iterate on this quite a bit, and improve the implementation,
but this is what we should start with.

## Definitions and Environment

We have the following basic definitions:

- A blob is a sequence of bytes of finite length -- potentially empty. 
  Value semantics: two blobs are equal iff they have equal length + equal bytes.

- A WASM module means a WASM 3 module as per the WASM 3 specification
  -- including multiple memories, multiple tables, and WASM GC.

  All modules nested in WASM components are interpreted as WASM 3 modules
  -- 
  we strictly validate that no features not defined in the WASM 3 specification may be used.

We'll assume we have, for an MVP:

- A set of (short) _names_ `name` with partial encoding/decoding to blobs:
  - `decode : blob -> name`
  - `encode : name -> blob`
  - s.t. for all b, `encode(decode(b)) = b` iff `decode(b)` is defined

  Note in particular this means that 
  
    - we _may_ have some names with no encoding --
        dually, _most_ blobs are not valid names! Valid names should be _short_.

    - `encode` and `decode`, where defined, are injective

- An cryptographic _keyed_ hash function `H : K -> blob -> name`, 
    where `K` is a type of keys equipped with a _distinct_:
    - "default key" `DATA : K`
    - key corresponding to each _name_ `K_name : name -> K`
    - key corresponding to each "context" blob `K_blob : blob -> K`

    These must have _no_ overlap

    We write `H(b)` as a shorthand for the default hash `H(DATA, b)`.

    Note BLAKE3 satisfies the above, where
    - `name == u256`, encoding is just as bytes
    - hashing with the default key is just BLAKE3 hashing
    - hashing with `K_name(o)` is BLAKE3 keyed hashing with key `o`
    - hashing with `K_blob(c)` is BLAKE3 key derivation hashing with context `c`

- The ability to load, link, and execute WASM components

Later, we'll integrate a blob store, etc 
-- but for now we need the actual execution framework,
so we want to keep things as minimal as possible to start,
but easily extensible 
-- components and props will be able to import a lot more,
and we'll be adding a _few_ more object types too.

## MVP Prover API

Our goal is to define an _LCF-style theorem prover_ 
based on the Curry-Howard correspondence using WASM.

Let's break down what that means -- in terms of our two primary object types:

- A _component_ is a WASM component as per the component model.

  This is represented as a binary blob encoded 
  using the standard binary encoding of the component model --
  we'll fix a particular version and set of features, and anything else
  we will consider _invalid_.

  Components may import the following:

  - A blob API containing:

    - Resources:

      - `blob` -- an opaque sequence of bytes 
         -- may be _lazily loaded_ (e.g. from a blob store), in which case we only fetch the data we need about it as necessary.

         If we ever can't find any data about a blob (or at any time) the implementation may trap

    - Functions:

      - `cons(vector<u8>) -> blob` -- create a blob from the given data

      - `cat(blob, blob) -> blob` -- concatenate two blobs together

      - `eq(blob, blob) -> bool` -- check whether two blobs are equal

      - `length(blob) -> u64` -- get the length of a blob

      - `slice(blob, u64, u64) -> vector<u8>` -- slice a byte range of a blob -- _might_ not trap even if invalid until we `read` it

      - `read(blob) -> vector<u8>` -- materialize a blob into a `vector<u8>`

  - A blob, by its hash + "blob/"

  - A WASM module, by the hash of its binary format blob + "module/"
    -- this gives us the module to instantiate

  - A component, by the hash of its binary format blob + "component/"
    
    - Either as a component -- just giving us the entire component to instantiate (including wiring imports)

    - Or by importing exports _from_ the component -- in which case instatiating it and linking it is up to the runtime

- A _proposition_ (_prop_) is just a component which may additionally:

    - Import a function `attest()`

    - Import other props by the hash of their binary format blob + "prop/"
      -- note a props may import components, but components may _not_ import props
      (though we may wire a component's imports to a props within a props 
       -- since _inside_ a props a props import is a component like any other)

    - A prop is _true_ if and only if one can:

        - Instantiate the component, calling its `start` function if it has one (i.e. standard WASM component initialization)

        - Call any of its exported functions with any arguments so as to get it to call `attest()`

        In particular, a prop is true if its `start` function calls `attest()`

- A _proof_ of a prop is simply a sequence of calls to the proposition which cause it to call `attest()`. 

  A natural encoding of a proof is hence simply as a component with the prop as an import

- If we think about this for a second, this makes the proof, indirectly, into a prop _itself_ 
  -- the only difference is that it does not call `attest()` directly, but only through its (single) import.

- This leads us to our first two _inference rules_:

    - If `P` is a prop, then it implies the _disjunction_ of its (prop) imports
      -- where `attest()` is viewed as the "true" prop
    
    - In particular, a prop with no prop imports (including `attest()`) is _false_

  We'll build up inference rules, and interfaces using them, later, but we'll focus on the MVP now.
