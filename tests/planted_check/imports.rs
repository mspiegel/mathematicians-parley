//! The planted cases about import lines: what is imported and how, mundane marks, prefixes, forbid lines and library functions' names.

use super::*;

pub(super) fn cases() -> Vec<Case> {
    vec![
        // Definitions outside a theorem, and definitions imported.
        case(
            "import a definition from a file that is not there",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "import definition proofs/wiedijk/nonesuch/W\n\ntheorem cantor\n".to_string()),
            ],
            "names no proof file",
        ),
        case(
            "import a definition the file does not define",
            vec![
                edit("proofs/wiedijk/tri.proof", None, TRI.to_string()),
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "import definition proofs/wiedijk/tri/W\n\ntheorem cantor\n".to_string()),
            ],
            "defines no W outside its theorems",
        ),
        case(
            "import a definition and never use it",
            vec![
                edit("proofs/wiedijk/tri.proof", None, TRI.to_string()),
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "import definition proofs/wiedijk/tri/T\n\ntheorem cantor\n".to_string()),
            ],
            "imports definition T and never uses it",
        ),
        // Every define is imported as a definition, whether or not it takes
        // an argument.
        case(
            "import a define that takes an argument as a function",
            vec![
                edit("proofs/wiedijk/tri.proof", None, TRI.to_string()),
                edit("proofs/wiedijk/tri-use.proof", None, "import theorem proofs/wiedijk/tri/tri-one\nimport function proofs/wiedijk/tri/T\n\ntheorem use-one\n  then T(1) = 1\n\n1.  T(1) = 1\n    thm:tri-one\n".to_string()),
            ],
            "import function: an import says the header of the item it names",
        ),
        // An imported define's label is what a line writing it out cites, and
        // is given only where a line does.
        case(
            "label an imported definition no line writes out",
            vec![
                edit("proofs/wiedijk/tri.proof", None, TRI.to_string()),
                edit("proofs/wiedijk/tri-use.proof", None, "import theorem proofs/wiedijk/tri/tri-one\nimport definition proofs/wiedijk/tri/T (D2)\n\ntheorem use-one\n  then T(1) = 1\n\n1.  T(1) = 1\n    thm:tri-one\n".to_string()),
            ],
            "import definition proofs/wiedijk/tri/T gives the label D2, which no line cites",
        ),
        case(
            "write out an imported definition its import gives no label",
            vec![
                edit("proofs/wiedijk/tri.proof", None, TRI.to_string()),
                edit("proofs/wiedijk/tri-use.proof", None, "import definition proofs/wiedijk/tri/T\n\ntheorem use-two\n  then T(2) = 3\n\n1.  T(2) = 3\n    calculation\n      T(2) = 2(2 + 1)/2        T\n           = 3                 arithmetic\n".to_string()),
            ],
            "T is the define import definition proofs/wiedijk/tri/T brings in, which a line cites by a label its import gives, as `(D1)`: add one",
        ),
        case(
            "label an imported definition as a theorem labels a line",
            vec![
                edit("proofs/wiedijk/tri.proof", None, TRI.to_string()),
                edit("proofs/wiedijk/tri-use.proof", None, "import theorem proofs/wiedijk/tri/tri-one\nimport definition proofs/wiedijk/tri/T (H1)\n\ntheorem use-one\n  let n ∈ ℕ                                                           (H1)\n  then T(1) = 1\n\n1.  T(1) = 1\n    thm:tri-one\n".to_string()),
            ],
            "label H1 is already a define's outside theorem use-one",
        ),
        case(
            "let a function of the proof's take a library function's name",
            vec![
                edit("proofs/wiedijk/bezout.proof", Some("              gcd(a, b) ≤ d.\n".to_string()), "              gcd(a, b) ≤ d.\n  let gcd : ℕ → ℕ                                                     (H9)\n".to_string()),
            ],
            "gcd is the library's function, def:stdlib/divisibility/gcd, which this file imports; name this function something else",
        ),
        // A file that imports a library function may not give its name to a
        // function of its own; one that does not import it may.
        case(
            "define a function of the proof's with an imported library function's name",
            vec![
                edit("proofs/wiedijk/tri.proof", None, format!("import definition stdlib/counting/C\n\n{}", TRI.replacen("define T(k)", "define C(k)", 1))),
            ],
            "C is the library's function, def:stdlib/counting/C, which this file imports; name this function something else",
        ),
        case(
            "import a function under the name of an imported library function",
            vec![
                edit("proofs/wiedijk/tri.proof", None, TRI.to_string()),
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "import definition stdlib/counting/C\nimport definition proofs/wiedijk/tri/T as C\n\ntheorem cantor\n".to_string()),
            ],
            "C is the library's function, def:stdlib/counting/C, which this file imports; name this function something else",
        ),
        // A library function is in scope where it is imported, by its name,
        // from the library file that declares it.
        case(
            "apply a library function the file does not import",
            vec![
                edit("proofs/wiedijk/bezout.proof", Some("import definition         stdlib/divisibility/gcd\n".to_string()), String::new()),
            ],
            "gcd is the library's function def:stdlib/divisibility/gcd, and this file does not import it: write `import definition stdlib/divisibility/gcd`",
        ),
        case(
            "import a library function from a file that does not declare it",
            vec![
                edit("proofs/wiedijk/bezout.proof", Some("import definition         stdlib/divisibility/gcd\n".to_string()), "import definition         stdlib/numbers/gcd\n".to_string()),
            ],
            "import definition stdlib/numbers/gcd: stdlib/numbers holds no item gcd",
        ),
        // A library function is a definition, and a definition is never
        // mundane.
        case(
            "import a library function as mundane",
            vec![
                edit("proofs/wiedijk/bezout.proof", Some("import definition         stdlib/divisibility/gcd\n".to_string()), "import mundane definition stdlib/divisibility/gcd\n".to_string()),
            ],
            "import mundane definition stdlib/divisibility/gcd: an axiom or a definition gives meaning, and a pedantic textbook cites it, so it is never mundane; import it as `import definition stdlib/divisibility/gcd`",
        ),
        // An item's name may open with a Greek letter, as σ's does, and is
        // imported from the file that holds it like any other.
        case(
            "import a Greek-named item from a file that does not hold it",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "import definition stdlib/numbers/σ\n\ntheorem cantor\n".to_string()),
            ],
            "import definition stdlib/numbers/σ: stdlib/numbers holds no item σ",
        ),
        case(
            "import a name that is no item's name",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "import mundane theorem stdlib/numbers/σ₁\n\ntheorem cantor\n".to_string()),
            ],
            "import mundane theorem stdlib/numbers/σ₁: 'σ₁' is not an item's name",
        ),
        case(
            "import a definition by a subscripted name the file does not define",
            vec![
                edit("proofs/wiedijk/tri.proof", None, TRI.to_string()),
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "import definition proofs/wiedijk/tri/T₁\n\ntheorem cantor\n".to_string()),
            ],
            "defines no T₁ outside its theorems",
        ),
        case(
            "import a library function the file never applies",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "import definition         stdlib/numbers/max\n\ntheorem cantor\n".to_string()),
            ],
            "imports max and never applies it",
        ),
        case(
            "import a library function with a label",
            vec![
                edit("proofs/wiedijk/bezout.proof", Some("import definition         stdlib/divisibility/gcd\n".to_string()), "import definition         stdlib/divisibility/gcd (D9)\n".to_string()),
            ],
            "import definition stdlib/divisibility/gcd: only a define of a proof file carries a label",
        ),
        case(
            "import a library function under another name",
            vec![
                edit("proofs/wiedijk/bezout.proof", Some("import definition         stdlib/divisibility/gcd\n".to_string()), "import definition         stdlib/divisibility/gcd as hcf\n".to_string()),
            ],
            "a library function is imported by its name alone, with no `as`",
        ),
        case(
            "import a definition under a name of several letters",
            vec![
                edit("proofs/wiedijk/tri.proof", None, TRI.to_string()),
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "import definition proofs/wiedijk/tri/T as tri\n\ntheorem cantor\n".to_string()),
            ],
            "a define is imported under one letter, perhaps with a subscript or a prime, and 'tri' is not one",
        ),
        case(
            "import an item that is not in the database",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("import mundane theorem    stdlib/sets/set-builder-subset\n".to_string()), "import mundane theorem    stdlib/sets/set-builder-nonesuch\n".to_string()),
                edit("proofs/wiedijk/cantor.proof", Some("    mun:set-builder-subset, from D1".to_string()), "    mun:set-builder-nonesuch, from D1".to_string()),
            ],
            "import mundane theorem stdlib/sets/set-builder-nonesuch: stdlib/sets holds no item set-builder-nonesuch",
        ),
        case(
            "import an item from a library file that does not exist",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("import mundane theorem    stdlib/sets/set-builder-subset\n".to_string()), "import mundane theorem    stdlib/nonesuch/set-builder-subset\n".to_string()),
            ],
            "import mundane theorem stdlib/nonesuch/set-builder-subset: stdlib/nonesuch is no file",
        ),
        case(
            "cite an item the file does not import",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("    mun:set-builder-subset, from D1".to_string()), "    mun:subset-transitive, from D1".to_string()),
            ],
            "mun:subset-transitive is neither imported nor a theorem of this file",
        ),
        // An import says where an item comes from, so a citation does not.
        case(
            "cite an item by its path",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("    mun:set-builder-subset, from D1".to_string()), "    mun:stdlib/sets/set-builder-subset, from D1".to_string()),
            ],
            "mun:stdlib/sets/set-builder-subset is cited by its path",
        ),
        case(
            "use def: for something that is mundane",
            vec![
                edit("proofs/wiedijk/sqrt2-irrational.proof", Some("    mun:even-or-odd\n".to_string()), "    def:even-or-odd\n".to_string()),
            ],
            "def:even-or-odd names a mundane",
        ),
        case(
            "cite a mundane item as a theorem",
            vec![
                edit("proofs/wiedijk/sqrt2-irrational.proof", Some("    mun:even-or-odd\n".to_string()), "    thm:even-or-odd\n".to_string()),
            ],
            "thm:even-or-odd names a mundane",
        ),
        case(
            "cite an axiom as a theorem",
            vec![
                edit("proofs/wiedijk/intermediate-value.proof", Some("obtain c: axi:completeness".to_string()), "obtain c: thm:completeness".to_string()),
            ],
            "thm:completeness names an axiom",
        ),
        case(
            "cite another proof file's theorem without importing it",
            vec![
                edit("proofs/wiedijk/intermediate-value.proof", Some("import theorem            proofs/wiedijk/triangle-inequality/abs-bounds\n".to_string()), "".to_string()),
            ],
            "thm:abs-bounds is neither imported nor a theorem of this file",
        ),
        // An import names one item, and its keyword is the kind of the item.
        case(
            "import without saying what is imported",
            vec![
                edit("proofs/wiedijk/intermediate-value.proof", Some("import theorem            proofs/wiedijk/triangle-inequality/abs-bounds\n".to_string()), "import proofs/wiedijk/triangle-inequality/abs-bounds\n".to_string()),
            ],
            "an import says `import <kind> <file>/<name>`",
        ),
        case(
            "import a whole proof file",
            vec![
                edit("proofs/wiedijk/intermediate-value.proof", Some("import theorem            proofs/wiedijk/triangle-inequality/abs-bounds\n".to_string()), "import proof proofs/wiedijk/triangle-inequality\n".to_string()),
            ],
            "import proof: an import says the header of the item it names",
        ),
        // A theorem taken for granted is imported as mundane, and every other
        // item by its kind. An import says its record's header: the mark and
        // the kind both.
        case(
            "import an item as mundane without its kind",
            vec![
                edit("proofs/wiedijk/euclid.proof", Some("import axiom              stdlib/reasoning/excluded-middle\n".to_string()), "import mundane stdlib/reasoning/excluded-middle\n".to_string()),
            ],
            "import mundane: an import says the header of the item it names",
        ),
        case(
            "import an axiom as a mundane theorem",
            vec![
                edit("proofs/wiedijk/euclid.proof", Some("import axiom              stdlib/reasoning/excluded-middle\n".to_string()), "import mundane theorem    stdlib/reasoning/excluded-middle\n".to_string()),
            ],
            "import mundane theorem stdlib/reasoning/excluded-middle: stdlib/reasoning/excluded-middle is an axiom; import it as `import axiom stdlib/reasoning/excluded-middle`",
        ),
        case(
            "import a proof's define as mundane",
            vec![
                edit("proofs/wiedijk/tri.proof", None, TRI.to_string()),
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "import mundane definition proofs/wiedijk/tri/T\n\ntheorem cantor\n".to_string()),
            ],
            "import mundane definition proofs/wiedijk/tri/T: an axiom or a definition gives meaning, and a pedantic textbook cites it, so it is never mundane",
        ),
        case(
            "import an axiom as mundane",
            vec![
                edit("proofs/wiedijk/euclid.proof", Some("import axiom              stdlib/reasoning/excluded-middle\n".to_string()), "import mundane axiom      stdlib/reasoning/excluded-middle\n".to_string()),
            ],
            "import mundane axiom stdlib/reasoning/excluded-middle: an axiom or a definition gives meaning, and a pedantic textbook cites it, so it is never mundane",
        ),
        case(
            "cite an axiom as mundane",
            vec![
                edit("proofs/wiedijk/euclid.proof", Some("axi:excluded-middle".to_string()), "mun:excluded-middle".to_string()),
            ],
            "mun:excluded-middle names an axiom",
        ),
        case(
            "cite a definition as mundane",
            vec![
                edit("proofs/wiedijk/isosceles.proof", Some("def:congruent".to_string()), "mun:congruent".to_string()),
            ],
            "mun:congruent names a definition",
        ),
        // `mundane` is a mark before a kind, and only before a theorem.
        case(
            "mark a record mundane and give it no kind",
            vec![
                edit("corpus/stdlib/sets.records", Some("mundane theorem powerset-empty\n".to_string()), "mundane powerset-empty\n".to_string()),
            ],
            "mundane powerset-empty has no kind",
        ),
        case(
            "mark a definition mundane",
            vec![
                edit("corpus/stdlib/sets.records", Some("\ndefinition subset\n".to_string()), "\nmundane definition subset\n".to_string()),
            ],
            "mundane definition: an axiom or a definition gives meaning, and a pedantic textbook cites it, so it is never mundane",
        ),
        case(
            "mark an axiom mundane",
            vec![
                edit("corpus/stdlib/reasoning.records", Some("\naxiom excluded-middle\n".to_string()), "\nmundane axiom excluded-middle\n".to_string()),
            ],
            "mundane axiom: an axiom or a definition gives meaning, and a pedantic textbook cites it, so it is never mundane",
        ),
        case(
            "mark a method mundane",
            vec![
                edit("corpus/db/methods.records", Some("\nmethod arithmetic\n".to_string()), "\nmundane method arithmetic\n".to_string()),
            ],
            "mundane method: a method is named on the line that uses it, so it is never mundane",
        ),
        case(
            "mark a notation mundane",
            vec![
                edit("corpus/db/notation.records", Some("\nnotation ".to_string()), "\nmundane notation ".to_string()),
            ],
            "mundane notation: a notation is never cited, so nothing takes it for granted",
        ),
        case(
            "import a proof's theorem as a library kind",
            vec![
                edit("proofs/wiedijk/intermediate-value.proof", Some("import theorem            proofs/wiedijk/triangle-inequality/abs-bounds\n".to_string()), "import mundane theorem proofs/wiedijk/triangle-inequality/abs-bounds\n".to_string()),
            ],
            "proofs/wiedijk/triangle-inequality/abs-bounds is a theorem",
        ),
        case(
            "import a theorem and cite nothing by it",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "import theorem proofs/wiedijk/bezout/bezout\n\ntheorem cantor\n".to_string()),
            ],
            "imports bezout and cites nothing by it",
        ),
        case(
            "cite a library item without importing it",
            vec![
                edit("proofs/wiedijk/euclid.proof", Some("import axiom              stdlib/reasoning/excluded-middle\n".to_string()), String::new()),
            ],
            "axi:excluded-middle is neither imported nor a theorem of this file",
        ),
        case(
            "import a library item nothing cites",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "import mundane theorem stdlib/sets/subset-transitive\n\ntheorem cantor\n".to_string()),
            ],
            "imports subset-transitive and cites nothing by it",
        ),
        case(
            "import from a proof file that is not there",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "import theorem proofs/wiedijk/nonesuch/lemma\n\ntheorem cantor\n".to_string()),
            ],
            "import theorem proofs/wiedijk/nonesuch/lemma: proofs/wiedijk/nonesuch is no file",
        ),
        case(
            "import a theorem a proof file does not prove",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "import theorem proofs/wiedijk/bezout/nonesuch\n\ntheorem cantor\n".to_string()),
            ],
            "import theorem proofs/wiedijk/bezout/nonesuch: proofs/wiedijk/bezout holds no item nonesuch",
        ),
        case(
            "import the same item twice",
            vec![
                edit("proofs/wiedijk/intermediate-value.proof", Some("import theorem            proofs/wiedijk/triangle-inequality/abs-bounds\n".to_string()), "import theorem            proofs/wiedijk/triangle-inequality/abs-bounds\nimport theorem            proofs/wiedijk/triangle-inequality/abs-bounds\n".to_string()),
            ],
            "proofs/wiedijk/triangle-inequality/abs-bounds is imported twice",
        ),
        // A forbid names an item the file does not import, after the words
        // its record's header says, once, and after the imports.
        case(
            "import an item the file forbids",
            vec![
                edit("proofs/wiedijk/ptolemy.proof", Some("import mundane theorem    stdlib/numbers/multiply-cancel\n".to_string()), "import mundane theorem    stdlib/numbers/multiply-cancel\nforbid theorem            stdlib/geometry/law-of-cosines\n".to_string()),
            ],
            "imports stdlib/geometry/law-of-cosines, which this file forbids at line 19",
        ),
        case(
            "forbid an item with words that are not its header",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "forbid mundane theorem stdlib/geometry/law-of-cosines\n\ntheorem cantor\n".to_string()),
            ],
            "forbid mundane theorem stdlib/geometry/law-of-cosines: stdlib/geometry/law-of-cosines is a theorem; forbid it as `forbid theorem stdlib/geometry/law-of-cosines`",
        ),
        case(
            "forbid an item that is not there",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "forbid theorem stdlib/geometry/nonesuch\n\ntheorem cantor\n".to_string()),
            ],
            "forbid theorem stdlib/geometry/nonesuch: stdlib/geometry holds no item nonesuch",
        ),
        case(
            "forbid the same item twice",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "forbid theorem stdlib/geometry/law-of-cosines\nforbid theorem stdlib/geometry/law-of-cosines\n\ntheorem cantor\n".to_string()),
            ],
            "stdlib/geometry/law-of-cosines is forbidden twice",
        ),
        case(
            "an import below a forbid",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("import definition         stdlib/sets/set-builder\n".to_string()), "forbid theorem            stdlib/geometry/law-of-cosines\nimport definition         stdlib/sets/set-builder\n".to_string()),
            ],
            "an import below a forbid",
        ),
        case(
            "a forbid below a define",
            vec![
                edit("proofs/wiedijk/ballot.proof", Some("theorem good-finite\n".to_string()), "forbid theorem stdlib/geometry/law-of-cosines\n\ntheorem good-finite\n".to_string()),
            ],
            "a forbid below a define",
        ),
        // Every name a file cites is distinct within it.
        case(
            "import an item under the name of a theorem of the file",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("import mundane theorem    stdlib/sets/set-builder-subset\n".to_string()), "import mundane theorem    stdlib/sets/set-builder-subset as cantor\n".to_string()),
                edit("proofs/wiedijk/cantor.proof", Some("    mun:set-builder-subset, from D1".to_string()), "    mun:cantor, from D1".to_string()),
            ],
            "cantor is already the name of theorem cantor of this file; import one of them under another name with `as`",
        ),
        case(
            "import two items under one name",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "import mundane theorem stdlib/sets/subset-transitive as set-builder-subset\n\ntheorem cantor\n".to_string()),
            ],
            "set-builder-subset is already the name of the import at line",
        ),
        case(
            "a proof file that imports its own theorem",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "import theorem proofs/wiedijk/cantor/cantor\n\ntheorem cantor\n".to_string()),
            ],
            "proofs/wiedijk/cantor/cantor is a theorem of this file, which is cited with no import",
        ),
        case(
            "two proof files that import each other",
            vec![
                edit("proofs/wiedijk/triangle-inequality.proof", Some("theorem abs-bounds\n".to_string()), "import theorem proofs/wiedijk/intermediate-value/intermediate-value\n\ntheorem abs-bounds\n".to_string()),
            ],
            "closes a cycle",
        ),
        case(
            "write a phrase the file does not import",
            vec![
                edit("tests/elaborator/a-phrase-imported.proof", Some("import definition         tests/elaborator/a-phrase-defined/triangular-number\n".to_string()), String::new()),
            ],
            "is the phrase tests/elaborator/a-phrase-defined/triangular-number defines, which this file does not import",
        ),
        case(
            "import a phrase and neither cite it nor write it",
            vec![
                edit("tests/elaborator/a-phrase-with-and.proof", Some("define common-divisor:".to_string()), "import definition         tests/elaborator/a-phrase-defined/triangular-number\n\ndefine common-divisor:".to_string()),
            ],
            "imports triangular-number and neither cites it nor writes its phrase",
        ),
        case(
            "a chain line citing an item with no import",
            vec![
                edit("tests/elaborator/a-chain-showing-its-work.proof", Some("import mundane theorem    stdlib/numbers/multiply-cancel\n".to_string()), String::new()),
            ],
            "mun:multiply-cancel is neither imported nor a theorem of this file",
        ),
        // An item whose import is taken away is reported where it is cited.
        case(
            "cite an item whose import is taken away",
            vec![edit(
                "proofs/wiedijk/harmonic.proof",
                Some("import mundane theorem    stdlib/sums/sum-real\n".to_string()),
                String::new(),
            )],
            "mun:sum-real is neither imported nor a theorem of this file",
        ),
        // A requires line under a let's reason cites as any requires line
        // does: an item it names that nothing imports is reported.
        case(
            "cite an unknown item in a requires line under a let's reason",
            vec![edit(
                "proofs/setmm/rounding-error.proof",
                Some("    membership, from 1\n    reads the error".to_string()),
                "    membership, from 1\n    requires A ∈ ℝ: mun:no-such-record\n    reads the error"
                    .to_string(),
            )],
            "mun:no-such-record is neither imported nor a theorem of this file",
        ),
    ]
}
