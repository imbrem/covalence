/// @file Tree-sitter grammar for SMT-LIB / Alethe S-expressions
/// @author Covalence contributors

module.exports = grammar({
  name: "sexp",

  extras: ($) => [/\s/, $.comment],

  rules: {
    source_file: ($) => repeat($._sexp),

    _sexp: ($) =>
      choice($.list, $.string, $.quoted_symbol, $.keyword, $.numeral, $.symbol),

    list: ($) => seq("(", repeat($._sexp), ")"),

    string: ($) =>
      seq(
        '"',
        repeat(choice($.escape_sequence, /[^"\\]+/)),
        '"',
      ),

    escape_sequence: (_$) =>
      /\\[\\\"nrtabfv]|\\x[0-9a-fA-F]{2}|\\u[0-9a-fA-F]{4}|\\u\{[0-9a-fA-F]+\}|\\U[0-9a-fA-F]{8}/,

    quoted_symbol: (_$) => /\|[^|\\]*\|/,

    keyword: (_$) => /:[a-zA-Z0-9~!@$%^&*_+\-=<>.?/]+/,

    numeral: (_$) => /#x[0-9a-fA-F]+|#b[01]+|[0-9]+(\.[0-9]+)?/,

    symbol: (_$) => /[a-zA-Z~!@$%^&*_+\-=<>.?/][a-zA-Z0-9~!@$%^&*_+\-=<>.?/]*/,

    comment: (_$) => /;[^\n]*/,
  },
});
