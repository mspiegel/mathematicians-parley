//! The notations the code names, each with its fixed id, and the literals
//! it names, each at its fixed place among its notation's
//! (`formula::notation_id`). A check that asks whether a node is an
//! equation asks `node.notation() == EQUALITY`, an integer compare.
//!
//! The first four are built by the reader and the build themselves, and no
//! record declares them: a letter, a numeral, a term already in kernel
//! form, and a property a binding fills. Every other name is a notation
//! record's (`corpus/db/notation.records`), which `tests/notation_ids.rs`
//! holds, with the literals at the places this table gives them. A pattern
//! a record declares the negation of another, `_ ≠ _`, builds the negation
//! of that one's node, so its literal is no node's and is not named here.

use crate::formula::notation_id::{Known, LiteralId, NotationId, Spelling};

macro_rules! notations {
    ($($id:ident = $n:literal, $name:literal $(, [$($lit:ident = $p:literal, $text:literal),*])?;)*) => {
        $(pub const $id: NotationId = NotationId($n);)*
        $($($(pub const $lit: Spelling = Spelling::new($id, LiteralId($p));)*)?)*
        /// Every notation the code names, at its id.
        pub const KNOWN: &[Known] = &[
            $(Known {
                id: $id,
                name: $name,
                literals: &[$($((LiteralId($p), $text)),*)?],
            }),*
        ];
    };
}

notations! {
    NAME = 0, "name";
    NUMERAL = 1, "numeral";
    LITERAL = 2, "literal";
    PROPERTY_OF = 3, "property-of";
    EQUALITY = 4, "equality", [EQUALS = 1, "="];
    ORDER = 5, "order", [LESS = 1, "<", GREATER = 2, ">", AT_MOST = 3, "≤", AT_LEAST = 4, "≥"];
    MEMBERSHIP = 6, "membership", [IN = 1, "∈"];
    NUMBER_SYSTEMS = 7, "number-systems", [NATURALS = 1, "ℕ", NATURALS0 = 2, "ℕ₀", INTEGERS = 3, "ℤ", RATIONALS = 4, "ℚ", REALS = 5, "ℝ", COMPLEXES = 6, "ℂ"];
    ADDITIVE = 8, "additive", [PLUS = 1, "+", MINUS = 2, "−"];
    MULTIPLICATIVE = 9, "multiplicative", [TIMES = 1, "·", DIVIDED = 2, "/"];
    FOR_ALL = 10, "for-all";
    THERE_IS = 11, "there-is";
    FUNCTION_TYPE = 12, "function-type";
    INTEGER_RANGE = 13, "integer-range";
    CONJUNCTION = 14, "conjunction", [AND = 1, "and"];
    COMMA_CONJUNCTION = 15, "comma-conjunction";
    BICONDITIONAL = 16, "biconditional";
    IMPLICATION = 17, "implication";
    CONDITIONAL = 18, "conditional";
    LOGICAL_NOT = 19, "logical-not";
    APPLICATION = 20, "application";
    APPLICATION_TO_TWO = 21, "application-to-two";
    FUNCTIONS_FROM = 22, "functions-from";
    SUM = 23, "sum";
    SUBGROUP = 24, "subgroup";
    POLYNOMIALS = 25, "polynomials";
    IS_A_POLYNOMIAL = 26, "is-a-polynomial";
    BY_CASES = 27, "by-cases";
    POWER = 28, "power";
    SUPERSCRIPT = 29, "superscript";
    UNARY_MINUS = 30, "unary-minus";
    JUXTAPOSITION = 31, "juxtaposition";
    FOR_ALL_PART = 32, "for-all-part";
    FOR_ALL_SETS = 33, "for-all-sets";
    SUBSET = 34, "subset", [SUBSET_OF = 1, "⊆"];
    ONE_TO_ONE = 35, "one-to-one";
    ONTO = 36, "onto";
    ONE_TO_ONE_ONTO = 37, "one-to-one-onto";
    IS_A_SET = 38, "is-a-set";
    IS_A_POINT = 39, "is-a-point";
    MOD = 40, "mod";
    FACTORIAL = 41, "factorial";
    POWERSET = 42, "powerset";
    THERE_IS_SOME = 43, "there-is-some";
    FUNCTION_ON = 44, "function-on";
    PRODUCT_OVER = 45, "product-over";
    DISJUNCTION = 46, "disjunction", [OR = 1, "or"];
}
