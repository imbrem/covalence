# `covalence-haskell` — skeletons

## Severe

- **No HOL/kernel backend yet.** The demo backends produce strings only. The
  follow-on is a `Lower` impl (living with the logic, e.g. in `covalence-init`)
  that lowers the AST into real kernel `Term`s — the actual step toward writing
  `init/` in a Haskell dialect. This crate stays kernel-agnostic.

## Minor — unsupported grammar

The parser covers a deliberately small subset. Not yet supported:

- do-notation, guards, `where`/`let` blocks with multiple binders;
- type signatures and type/`data`/`class`/`instance` declarations;
- pattern matching (only bare parameter names) and multi-clause definitions;
- full Haskell layout (only newline separation + indented-continuation
  layout-lite; no offside rule, no `{ ; }` explicit blocks);
- operator sections, `if`/`case`, list/tuple syntax, negative literals,
  floating-point/char literals, user-defined operators (only `+ - * ==`).
