use covalence_cfg_parsing::ChartParseLimits;
use covalence_grammar::parse_regex_u8;
use covalence_lexer_cfg_parsing::{PipelineBudget, PipelineMode};
use covalence_lexer_parsing::{LexerBudget, LexerPolicy};
use covalence_parser_generator::{
    GrammarSpec, NamedSymbol as S, ParserSpec, ProductionSpec, TokenSpec,
};

fn main() {
    let spec = ParserSpec {
        name: "calculator".into(),
        lexer_policy: LexerPolicy::default(),
        tokens: vec![
            TokenSpec::token("NUM", parse_regex_u8("[0-9]+").unwrap(), 0),
            TokenSpec::token("PLUS", parse_regex_u8("\\+").unwrap(), 0),
            TokenSpec::skip("WS", parse_regex_u8(" +").unwrap(), 0),
        ],
        grammar: GrammarSpec {
            name: "arithmetic".into(),
            start: "expr".into(),
            nonterminals: vec!["expr".into()],
            productions: vec![
                ProductionSpec::new(
                    "expr",
                    vec![
                        S::nonterminal("expr"),
                        S::token("PLUS"),
                        S::nonterminal("expr"),
                    ],
                ),
                ProductionSpec::new("expr", vec![S::token("NUM")]),
            ],
        },
    };
    let parser = spec.compile().expect("valid specification");
    let parsed = parser
        .parse(
            b"1 + 2 + 3",
            PipelineMode::Exact,
            PipelineBudget {
                lexer: LexerBudget::new(128, 4_000, 128, 512, 128, 128),
                parser: ChartParseLimits {
                    work: 100_000,
                    results_per_cell: 1_000,
                    chart_entries: 10_000,
                },
            },
        )
        .expect("within bounds")
        .expect("recognized");

    println!(
        "{} tokens; {} packed root(s)",
        parsed.lexing.tokens.len(),
        parsed.roots.len()
    );
}
