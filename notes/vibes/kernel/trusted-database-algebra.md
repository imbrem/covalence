+++
id = "N0057"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:gpt-5.6-sol"
at = "2026-07-20T00:00:00+01:00"
source = "trusted-database-algebra-sketch"
agent = "gpt-5.6-sol"
harness = "codex"
+++

# Trusted database algebra

The neutron is intended to execute much of the TCB, not merely persist its
output. Most large-state kernel operations should become simple queries over an
in-memory SQLite database. Only a small, typed fragment of relational behavior
is trusted—not arbitrary SQL and not every SQLite feature.

## Authority boundary

A row does not confer authority merely because it exists. Authority comes from
its database/table trust classification and the checked operation that admitted
or derived it. A trusted query is a nucleus transition: it consumes trusted and
untrusted relations under a fixed trust-propagation rule and writes rows with
explicit provenance.

The selected SQLite behavior is consequently part of the implementation TCB.
The goal is to reduce that behavior to query shapes whose semantics fit on a
page and can also be replayed by a tiny independent relational interpreter.

Do not accept user SQL as a trusted rule. Expose a typed relational-algebra AST
and compile its closed variants to prepared SQL templates. Arbitrary SQL may
propose rows in an untrusted database, never directly change trust.

## Database classes

- **trusted**: accepted nucleus state under a named execution/grounding TCB;
- **untrusted**: candidate rows, imported snapshots, solver output, or remote
  state awaiting comparison, signature acceptance, or reproof;
- **derived**: trusted rows produced from trusted premises by a named primitive
  query/rule;
- **cache**: discardable rows with no authority, reconstructible from trusted
  state;
- **signed candidate**: untrusted until a signer policy accepts its exact
  canonical snapshot, schema, groundings, roots, and trust manifest.

Trust should normally be tracked below whole-database granularity: per attached
database and table, with row provenance where a table contains selectively
promoted rows. Physically separating trusted and untrusted databases is the
safest initial implementation.

## Candidate primitive query fragment

| Primitive | Trust behavior |
|---|---|
| keyed lookup / membership | reads an already trusted row; creates no new authority |
| projection and rename | derives the projected trusted relation; records lost columns |
| typed selection | retains trusted rows satisfying a small trusted predicate |
| union | combines compatible trusted relations and their provenance |
| inner/equi-join | derives tuples from trusted matching premises |
| semijoin | filters a trusted relation by trusted witnesses in another |
| intersection | promotes only candidate rows also present in a trusted relation |
| difference | allowed only with explicit completeness/closed-world evidence |
| group/aggregate | excluded initially; later requires an independently specified operator |
| recursive CTE | excluded initially; represent fixed points by checked iteration |

Basic trusted predicates should begin with typed equality, null/option tests,
and range-checked comparisons over substrate integers. No collation-dependent
text comparison, implicit coercion, floating arithmetic, user functions,
triggers, views with arbitrary SQL, or planner-sensitive semantic shortcuts.

Projection, filtering, and subdatabase extraction preserve positive facts but
usually destroy completeness. A `COMPLETE` claim is copied only when a checked
side condition proves that the operation preserved its quantified domain.

## Core nucleus operations

### Read trusted state

Read only tables whose schema, relation name, grounding TCB, and migration
version match the accepted manifest. A query returns witnesses tied to that
database generation; it does not manufacture free-standing theorem handles.

### Attach multiple databases

Attach trusted and untrusted databases under distinct capabilities. Cross-DB
queries must name the trust of every input. SQLite attachment is an
implementation mechanism; the nucleus operation is a typed multi-relation query
with deterministic namespace and schema resolution.

### Merge trusted states

The positive union of two compatible trusted states should produce a larger
trusted state. Before union:

- reconcile schema and well-known-name manifests;
- require compatible groundings/TCBs or retain them as separate scopes;
- preserve row provenance and signatures;
- reject conflicting `DEF` identities or define their disjoint renaming;
- weaken or separately reconcile completeness claims;
- deduplicate set relations while retaining duplicates in multiset relations.

This is not raw `ATTACH; INSERT ... SELECT *`; it is a checked `merge`
transition implemented by a small family of such queries.

### Compare trusted and untrusted states

Useful promotion shapes include:

- **intersection promotion**: retain candidate rows field-equal to trusted rows;
- **keyed comparison**: match candidate witnesses to trusted definitions and
  retain only consistent rows;
- **premise join**: join candidate conclusions/evidence against every trusted
  premise required by a rule, promoting only successful rows;
- **reproof**: replay candidate derivations through nucleus rules and insert
  only their checked conclusions;
- **signature promotion**: accept the exact signed snapshot under an explicit
  signer policy, without pretending it was locally reproved.

“Remove all unproved rows” is therefore a first-class operation producing a
new trusted subdatabase plus a rejection report. It must never mutate the
candidate into looking wholly trusted in place.

### Filter and transmit a subdatabase

A process can select the rows reachable from chosen roots, copy the required
schema/grounding/provenance closure, and send the resulting database. Positive
facts remain valid. Completeness and global-freshness claims require explicit
weakening or retained witnesses. This is the natural message format for
threads, processes, machines, and federated peers.

### Dump and load

An in-memory neutron can be serialized as a canonical snapshot. Loading is
always initially an untrusted parse; it becomes trusted only by recognizing a
locally created state identity, accepting an exact signature under policy,
comparing it to trusted state, or replaying/reproving its rows.

## Three interchangeable forms

1. **neutron / SQLite** — canonical live relational state and persistence;
2. **proton / specialized memory** — fast term and theorem structures viewed as
   indexes or optimized witnesses over the same relations;
3. **e-graph** — a future equality-saturation/index form, also derived from and
   exportable back to relational state.

The latter two are optimizations, not separate sources of meaning. Each needs a
checked import/export or reconstruction boundary. Discarding either must leave
the canonical trusted neutron state sufficient to continue or replay.

## Distributed shape

Every worker receives a database capability, runs local untrusted computation
and trusted primitive queries, and returns either its whole database or a
root-filtered subdatabase. Coordination becomes trusted-state merge plus
selective promotion. This naturally supports thread-local transactions, process
isolation, checkpointed autoresearch, remote proof workers, and different
physical indexes over the same logical relations.

Concurrency semantics should first be snapshot-based. Shared writable SQLite
connections, distributed consensus, and incremental view maintenance are later
optimizations.

## Minimal audit experiment

Build a toy nucleus containing `Tm`, `Ty`, `App`, `HasTy`, and a candidate
`HasTy` table. Implement only trusted lookup, projection, equi-join, compatible
trusted union, candidate intersection, proof-filtered promotion into a fresh
trusted database, and root-reachable subdatabase extraction.

Run each operation through SQLite and a tiny independent in-memory interpreter,
then compare canonical row sets and trust manifests. This is the first TCB
consilience test and should precede use of recursive SQL or complex query plans.

## Open decisions

- Is SQLite itself trusted for the selected fragment, or must every trusted
  result be cross-checked by the tiny interpreter in production/paranoid mode?
- What is the smallest typed query AST that supports actual kernel workloads?
- Does a nucleus have exactly one writable trusted neutron plus attached
  read-only inputs, or multiple writable trust scopes?
- How are `DEF` identity collisions detected across independently created DBs?
- What canonicalization makes signed snapshots insensitive to SQLite page
  layout while preserving exact relational state?
- Which provenance is row-level, table-level, or derivable from a transition
  log?
- How are SQL planner/version/configuration details represented in the
  execution TCB?

