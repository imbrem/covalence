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

- 
