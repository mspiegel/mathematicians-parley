//! The planted cases about points and the plane.

use super::*;

pub(super) fn cases() -> Vec<Case> {
    vec![
        // A row's atoms are real numbers (`METHODS.md`, Rows), and a point
        // is none, which no line can say: the step is told it treats the
        // point as a number, not that nothing says it is one.
        case(
            "turn a disequality of points round in an inequalities row",
            vec![edit(
                "proofs/wiedijk/point-row.proof",
                None,
                "theorem point-row\n  let A be a point                                                    (H1)\n  let C be a point                                                    (H2)\n  assume C ≠ A                                                        (H3)\n  then A ≠ C\n\n1.  A ≠ C\n    inequalities\n      C ≠ A            H3\n      A ≠ C            restate\n".to_string(),
            )],
            "proofs/wiedijk/point-row.proof:10  this step treats A as a number, and it is a point",
        ),
        // `requires C ≠ B: def:triangle` unfolds a line saying A, B, C form a
        // triangle; cited, that line is what it rests on, and without it
        // nothing is.
        case(
            "unfold a triangle no line above says",
            vec![
                edit("proofs/euclid/thales.proof", Some("import theorem            stdlib/geometry/angle-sum\n".to_string()), "import theorem            stdlib/geometry/angle-sum\nimport definition         stdlib/geometry/triangle\n".to_string()),
                edit("proofs/euclid/thales.proof", Some("    mun:angle-along-segment P := A, Q := B, R := C, S := M, from H5, H6, 1\n".to_string()), "    mun:angle-along-segment P := A, Q := B, R := C, S := M, from H6, 1\n    requires C ≠ B: def:triangle P := A, Q := B, R := C\n".to_string()),
            ],
            "the requires line of step 7 needs something that def:triangle does not conclude",
        ),
        // An angle is written only where its three points are said to
        // differ (`SYNTAX.md`, Formulas): in a statement, by its hypotheses.
        case(
            "write an angle in a statement whose hypotheses leave two of its points unsaid apart",
            vec![edit(
                "tests/elaborator/a-naming-let-with-a-requires-line.proof",
                Some("  assume A ≠ C                                                        (H6)\n".to_string()),
                String::new(),
            )],
            "the statement of a-naming-let-with-a-requires-line writes ∠ABC, and nothing where it is written says A ≠ C",
        ),
        case(
            "write an angle in a library item whose hypotheses leave two of its points unsaid apart",
            vec![edit(
                "corpus/stdlib/geometry.records",
                Some("  assume P ≠ R                                                        (H6)\n  then        ∠PQR = ∠RQP".to_string()),
                "  then        ∠PQR = ∠RQP".to_string(),
            )],
            "mundane theorem angle-turned writes ∠PQR, and its hypotheses do not say P ≠ R",
        ),
    ]
}
