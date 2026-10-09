//! The elaborator's rule tables: which set.mm lemma does each job.
//!
//! This is data, not code. Given the shape of what is wanted, a table names
//! the set.mm lemma that answers it: which lemma lifts an equation through
//! each constructor, which carries a membership from one number system to
//! another or through an operation, what a closed numeral is, and the
//! spellings in which set.mm and the page say one thing two ways.
//!
//! Growth goes here first. A pilot that meets a new difference between the
//! page and set.mm adds an entry, and the gate checks that every label here
//! is one set.mm has (`every_label`).
//!
//! `MEMBERSHIP` says which set.mm lemmas an elaborator may lean on for what
//! the readable layer never writes. That a sum of integers is an integer,
//! that an integer is a real, that two integers may be multiplied either way
//! round — these are facts about set.mm's library rather than about the
//! readable corpus, and no field of a readable database is the place for
//! them. They are one list tried by matching, because they are one question:
//! what does set.mm already prove that says this?
//!
//! Where a table is looked up by key it is a slice searched in order; where
//! a table is walked, the order written is what the walk sees. Either way
//! the order is part of what a proof comes out as, so an entry is not moved
//! without a reason.

/// The digits and the constant set.mm names each by.
pub const NUMERALS: [(&str, &str); 10] = [
    ("0", "cc0"),
    ("1", "c1"),
    ("2", "c2"),
    ("3", "c3"),
    ("4", "c4"),
    ("5", "c5"),
    ("6", "c6"),
    ("7", "c7"),
    ("8", "c8"),
    ("9", "c9"),
];

/// The constant set.mm names a digit by.
pub fn numeral_label(digit: u32) -> Option<&'static str> {
    NUMERALS.get(digit as usize).map(|(_, label)| *label)
}

/// The value of a digit's constant.
pub fn digit_of(label: &str) -> Option<u32> {
    NUMERALS
        .iter()
        .position(|(_, l)| *l == label)
        .map(|at| at as u32)
}

// Which lemma rewrites a subterm, by what encloses it and which hole it sits
// in. The tree decides; nothing is searched for. A claim may change in more
// than one place at once — the claim of an induction holds its variable
// several times — so the lemma is chosen by which operands change together
// as well as by what encloses them.
pub const CONGRUENCE: &[(&str, &[usize], &str)] = &[
    ("co", &[0], "oveq1d"),
    ("co", &[1], "oveq2d"),
    ("co", &[0, 1], "oveq12d"),
    ("wbr", &[0], "breq1d"),
    ("wbr", &[1], "breq2d"),
    ("wbr", &[0, 1], "breq12d"),
    ("cfv", &[0], "fveq2d"),
    ("cfv", &[0, 1], "fveq12d"),
    // A pair, as the state of a define by recursion holds its values.
    ("cop", &[0], "opeq1d"),
    ("cop", &[1], "opeq2d"),
    ("cop", &[0, 1], "opeq12d"),
    ("wceq", &[0], "eqeq1d"),
    ("wceq", &[1], "eqeq2d"),
    ("wceq", &[0, 1], "eqeq12d"),
    ("wne", &[0], "neeq1d"),
    ("wne", &[1], "neeq2d"),
    ("wne", &[0, 1], "neeq12d"),
    ("wcel", &[0], "eleq1d"),
    ("wcel", &[1], "eleq2d"),
    ("wcel", &[0, 1], "eleq12d"),
    ("csu", &[0], "sumeq1d"),
    ("cprod", &[0], "prodeq1d"),
    // An integral's two ends, its letter first among what it holds. set.mm
    // has the two ends at once in deduction form, and each alone only
    // closed; `proved.mm` gives each alone as the others are.
    ("cdit", &[1], "gditgeq1d"),
    ("cdit", &[2], "gditgeq2d"),
    ("cdit", &[1, 2], "ditgeq12d"),
    ("cpw", &[0], "pweqd"),
    ("csn", &[0], "sneqd"),
    ("cneg", &[0], "negeqd"),
    ("crn", &[0], "rneqd"),
    ("cun", &[0], "uneq1d"),
    ("cun", &[1], "uneq2d"),
    ("cun", &[0, 1], "uneq12d"),
    // A pair, as the two ends of an edge.
    ("cpr", &[0], "preq1d"),
    ("cpr", &[1], "preq2d"),
    ("cpr", &[0, 1], "preq12d"),
    ("cdif", &[0], "difeq1d"),
    ("cdif", &[1], "difeq2d"),
    ("cdif", &[0, 1], "difeq12d"),
    ("cin", &[0], "ineq1d"),
    ("cin", &[1], "ineq2d"),
    ("cin", &[0, 1], "ineq12d"),
    ("wss", &[0], "sseq1d"),
    ("wss", &[1], "sseq2d"),
    ("wss", &[0, 1], "sseq12d"),
    ("wfn", &[0], "fneq1d"),
    ("wfn", &[1], "fneq2d"),
    ("wfn", &[0, 1], "fneq12d"),
    ("wa", &[0], "anbi1d"),
    ("wa", &[1], "anbi2d"),
    ("wa", &[0, 1], "anbi12d"),
    ("w3a", &[0], "3anbi1d"),
    ("w3a", &[1], "3anbi2d"),
    ("w3a", &[2], "3anbi3d"),
    ("w3a", &[0, 1], "3anbi12d"),
    ("w3a", &[0, 2], "3anbi13d"),
    ("w3a", &[1, 2], "3anbi23d"),
    ("w3a", &[0, 1, 2], "3anbi123d"),
    ("wo", &[0], "orbi1d"),
    ("wo", &[1], "orbi2d"),
    ("wo", &[0, 1], "orbi12d"),
    ("wb", &[0], "bibi1d"),
    ("wb", &[1], "bibi2d"),
    ("wb", &[0, 1], "bibi12d"),
    ("wn", &[0], "notbid"),
    // A universal over an `if ... then` changes both sides at once when the
    // name it binds stands on each of them.
    ("wi", &[0], "imbi1d"),
    ("wi", &[1], "imbi2d"),
    ("wi", &[0, 1], "imbi12d"),
    ("wral", &[0], "ralbidv"),
    ("wrex", &[0], "rexbidv"),
    // Over a domain spelt another way, as a defined name read as the set it
    // names; `congruence` takes these by name, since they order their
    // variables apart from the rest.
    ("wral", &[2], "raleqdv"),
    ("wrex", &[2], "rexeqdv"),
    ("wral", &[0, 2], "raleqbidv"),
    ("wrex", &[0, 2], "rexeqbidv"),
    ("crab", &[0], "rabbidva"),
    ("crab", &[2], "rabeqdv"),
    ("cmpt", &[1], "mpteq1d"),
    ("ciun", &[1], "iuneq1d"),
    // A function against the map its define names, and a rule by cases in
    // any of its three parts; given by name too.
    ("wf", &[2], "feq1d"),
    ("wf1", &[2], "f1eq1"),
    // An image, in its function, its set, or both.
    ("cima", &[0], "imaeq1d"),
    ("cima", &[1], "imaeq2d"),
    ("cima", &[0, 1], "imaeq12d"),
    ("cif", &[0], "ifbieq12d"),
    ("cif", &[1], "ifbieq12d"),
    ("cif", &[2], "ifbieq12d"),
    ("cif", &[0, 1], "ifbieq12d"),
    ("cif", &[0, 2], "ifbieq12d"),
    ("cif", &[1, 2], "ifbieq12d"),
    ("cif", &[0, 1, 2], "ifbieq12d"),
    // And the same over every set there is, which a `let X be a set`
    // quantifies and the subsets proof inducts under.
    ("wal", &[0], "albidv"),
];

pub fn congruence(label: &str, slots: &[usize]) -> Option<&'static str> {
    CONGRUENCE
        .iter()
        .find(|(l, s, _)| *l == label && *s == slots)
        .map(|(_, _, lemma)| *lemma)
}

/// The constructors that take a function, operation or relation as an
/// operand.
pub const WRAPS: [&str; 3] = ["co", "wbr", "cfv"];

// Lifting a closed biconditional through one level of a term. The deduction
// forms `congruence` uses take the scope as an antecedent; these take
// nothing, which is what a renaming needs.
pub const RENAMED: &[(&str, usize, &str)] = &[
    ("wa", 0, "anbi1i"),
    ("wa", 1, "anbi2i"),
    ("wi", 0, "imbi1i"),
    ("wi", 1, "imbi2i"),
    ("wb", 0, "bibi1i"),
    ("wb", 1, "bibi2i"),
    ("wo", 0, "orbi1i"),
    ("wo", 1, "orbi2i"),
    ("wn", 0, "notbii"),
];

pub fn renamed(label: &str, slot: usize) -> Option<&'static str> {
    RENAMED
        .iter()
        .find(|(l, s, _)| *l == label && *s == slot)
        .map(|(_, _, lemma)| *lemma)
}

// One binder: the lemma that changes what it binds over, and the one that
// changes the name it binds. Both closed, and the `w` on the second is
// set.mm's version that does not lean on ax-13.
pub const BOUND: &[(&str, (&str, &str))] = &[
    ("wrex", ("rexbii", "cbvrexvw")),
    ("wral", ("ralbii", "cbvralvw")),
    ("wal", ("albii", "cbvalvw")),
];

// A class that binds a name, and the lemma that changes the name; its
// hypothesis says how the two bodies agree at x = y. None leans on ax-13. A
// map in a theorem the subsets proof cites binds `o` where the define it is
// compared with binds `l`, and those are one class; so are a defined sum's
// rule over `i` and the same sum a line writes over `j`.
pub const CLASS_BOUND: &[(&str, &str)] = &[
    ("cmpt", "cbvmptv"),
    ("crab", "cbvrabv"),
    ("csu", "cbvsumv"),
    ("cprod", "cbvprodv"),
    ("ciun", "cbviunv"),
    ("cdit", "cbvditgv"),
];

// And the lemma that changes what such a class says of each member, its
// letter kept, closed: where one binder sits inside another, the inner is
// renamed first and carried up through the outer by this, and the outer
// renamed after.
pub const CLASS_BODY: &[(&str, &str)] = &[
    ("cmpt", "mpteq2ia"),
    ("csu", "sumeq2i"),
    ("cprod", "prodeq2i"),
    ("ciun", "iuneq2i"),
];

// The lemmas that carry a change into an indexed sum's or product's term,
// under its letter's membership of the range, in deduction form: the term
// alone, and the range and the term together.
pub const INDEXED_BODY: &[(&str, (&str, &str))] = &[
    ("csu", ("sumeq2dv", "sumeq12dv")),
    ("cprod", ("prodeq2dv", "prodeq12dv")),
];

// A statement about classes carried across one class spelt with other bound
// letters, closed, by the predicate and the place: `eqeq1i` makes `A = B`
// into ( A = C <-> B = C ). What a renaming of the letters a class binds
// inside a statement is lifted through.
pub const PREDICATE_LIFT: &[(&str, usize, &str)] = &[
    ("wceq", 0, "eqeq1i"),
    ("wceq", 1, "eqeq2i"),
    ("wcel", 0, "eleq1i"),
    ("wcel", 1, "eleq2i"),
    ("wss", 0, "sseq1i"),
    ("wss", 1, "sseq2i"),
    ("wbr", 0, "breq1i"),
    ("wbr", 1, "breq2i"),
];

// Carrying an equality of two classes up through one place of a term,
// closed, by the constructor and the place: what two terms spelling one
// class with different bound letters inside are shown equal by. The places
// are the kernel term's, in the order its constructor takes them.
pub const CLASS_LIFT: &[(&str, usize, &str)] = &[
    ("cdif", 0, "difeq1i"),
    ("cdif", 1, "difeq2i"),
    ("crn", 0, "rneqi"),
    ("cfv", 0, "fveq2i"),
    ("cfv", 1, "fveq1i"),
    ("cun", 0, "uneq1i"),
    ("cun", 1, "uneq2i"),
    ("cin", 0, "ineq1i"),
    ("cin", 1, "ineq2i"),
    ("co", 0, "oveq1i"),
    ("co", 1, "oveq2i"),
    ("cpw", 0, "pweqi"),
    ("csn", 0, "sneqi"),
    ("cima", 0, "imaeq1i"),
    ("cima", 1, "imaeq2i"),
];

// A binder's domain changed, its body kept, closed.
pub const DOMAIN: &[(&str, &str)] =
    &[("wral", "raleqi"), ("wrex", "rexeqi"), ("cmpt", "mpteq1i")];

/// Look a label up in a table of pairs.
pub fn lookup<V: Copy>(table: &[(&str, V)], key: &str) -> Option<V> {
    table.iter().find(|(k, _)| *k == key).map(|(_, v)| *v)
}

/// How a biconditional was joined to what follows it: through an
/// implication, through a biconditional, or through a biconditional a lemma
/// states the other way round from the way a step reaches it.
///
/// The last is no label, so a statement built from it would not spell,
/// which is what stops a second antecedent being folded past one read this
/// way.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Join {
    Implies,
    Iff,
    Turned,
}

// Which lemma discharges one thing a lemma asked, by how that thing was
// joined to what follows it and whether the lemma is still bare. The first
// is composed with the lemma itself; every later one is applied to what the
// last already deduced.
pub fn discharge(join: Join, bare: bool) -> &'static str {
    match (join, bare) {
        (Join::Implies, true) => "syl",
        (Join::Implies, false) => "mpd",
        (Join::Iff, true) => "sylib",
        (Join::Iff, false) => "mpbid",
        (Join::Turned, true) => "sylibr",
        (Join::Turned, false) => "mpbird",
    }
}

// A claim `P → Q` from a biconditional between P and Q: the lemma taking it
// from left to right, then the one from right to left.
pub const ONE_WAY: (&str, &str) = ("biimpd", "biimprd");

// Instantiating a universal, by the binder: the lemma, the variable it names
// the domain by, and the domain where the binder names none. A restricted
// universal wants its term in the set it runs over, and an unrestricted one
// wants it only to be a set.
pub struct Instance {
    pub lemma: &'static str,
    pub domain_var: &'static str,
    pub domain: Option<&'static str>,
}

pub const INSTANCES: &[(&str, Instance)] = &[
    (
        "wral",
        Instance {
            lemma: "rspcv",
            domain_var: "B",
            domain: None,
        },
    ),
    (
        "wal",
        Instance {
            lemma: "spcgv",
            domain_var: "V",
            domain: Some("cvv"),
        },
    ),
];

// Which transitivity folds one link of a calculation into the run above it,
// by what each of the two claims is. Two relations in a row would want the
// transitivity of that relation and no chain writes one.
pub const FOLDING: &[((&str, &str), &str)] = &[
    (("wceq", "wceq"), "eqtrd"),
    (("wceq", "wbr"), "eqbrtrd"),
    (("wbr", "wceq"), "breqtrd"),
];

pub fn folding(first: &str, second: &str) -> Option<&'static str> {
    FOLDING
        .iter()
        .find(|((a, b), _)| *a == first && *b == second)
        .map(|(_, lemma)| *lemma)
}

// A fact that conjoins several things says each of them, and the steps below
// cite them one at a time: an `obtain` hands over one body saying that q is
// positive, that x is p over q, and that nothing divides both.
pub const SPLIT: &[(&str, &[&str])] = &[
    ("wa", &["simpl", "simpr"]),
    ("w3a", &["simp1", "simp2", "simp3"]),
];
// And the other direction: what conjoins a proof of each part into a proof
// of the whole. `SPLIT` is read where a fact is taken apart and this where a
// goal is put together, and both are asked by label so that a shape neither
// names is left alone.
pub const JOIN: &[(&str, &str)] = &[("wa", "jca"), ("w3a", "3jca")];

// What closes an induction, by the set the name inducted on runs over, and
// where that lemma starts. The two have the same six hypotheses in the same
// order and differ only in the set and the base, so choosing between them is
// choosing a label. Which one a proof wants is not the text's to say twice:
// `let n ∈ ℕ₀` already says it, and `starting at` is checked against it.
pub const INDUCTION: &[(&str, (&str, &str))] =
    &[("cn", ("nnindd", "c1")), ("cn0", ("nn0indd", "cc0"))];

// How set.mm names that a digit belongs to a number system, by the system.
// The label is the digit and this suffix throughout — `2z`, `1nn`, `0re` —
// so what a system needs here is how its name is spelt in that label and
// nothing else.
pub const SYSTEMS: &[(&str, &str)] = &[
    ("cc", "cn"),
    ("cr", "re"),
    ("cz", "z"),
    ("cn", "nn"),
    ("cn0", "nn0"),
    ("cq", "q"),
];
// The lemma that puts a sum, difference, product or power in a number system
// from its parts being there, by operator and system; a power's exponent is
// in ℕ₀ whatever the system. A compound's membership is built from its
// atoms' this way, so an atom's is the step's own line where it wrote one.
pub const CLOSED: &[((&str, &str), &str)] = &[
    (("caddc", "cc"), "addcld"),
    (("cmin", "cc"), "subcld"),
    (("cmul", "cc"), "mulcld"),
    (("cexp", "cc"), "expcld"),
    (("caddc", "cr"), "readdcld"),
    (("cmin", "cr"), "resubcld"),
    (("cmul", "cr"), "remulcld"),
    (("cexp", "cr"), "reexpcld"),
    (("caddc", "cz"), "zaddcld"),
    (("cmin", "cz"), "zsubcld"),
    (("cmul", "cz"), "zmulcld"),
    (("cexp", "cz"), "zexpcld"),
    (("caddc", "cn"), "nnaddcld"),
    (("cmul", "cn"), "nnmulcld"),
    (("cexp", "cn"), "nnexpcld"),
    (("caddc", "cn0"), "nn0addcld"),
    (("cmul", "cn0"), "nn0mulcld"),
    (("cexp", "cn0"), "nn0expcld"),
];

pub fn closed(op: &str, system: &str) -> Option<&'static str> {
    CLOSED
        .iter()
        .find(|((o, s), _)| *o == op && *s == system)
        .map(|(_, lemma)| *lemma)
}

pub const NEGATED: &[(&str, &str)] =
    &[("cc", "negcld"), ("cr", "renegcld"), ("cz", "znegcld")];
// A quotient asks a third thing of its parts, that the divisor is not zero,
// so it is closed only where the caller says how that is shown.
pub const DIVIDED: &[(&str, &str)] = &[("cc", "divcld"), ("cr", "redivcld")];

/// An operation whose value is a whole number when its parts are in the
/// systems named, whatever system its parts are asked in: the lemma says
/// the value is in ℕ₀, and a bridge carries it to the system wanted.
pub struct Whole {
    /// The operation's constant, at the head of the term.
    pub op: &'static str,
    /// The closed lemma, `( ( A e. X /\ B e. Y ) -> ( A op B ) e. NN0 )`.
    pub lemma: &'static str,
    /// The lemma's variable for the left part, and the system it asks.
    pub left: (&'static str, &'static str),
    /// The lemma's variable for the right part, and the system it asks.
    pub right: (&'static str, &'static str),
}

// A binomial coefficient of a whole number and an integer, and an integer
// modulo a natural number.
pub const WHOLE: &[Whole] = &[
    Whole {
        op: "cbc",
        lemma: "bccl",
        left: ("N", "cn0"),
        right: ("K", "cz"),
    },
    Whole {
        op: "cmo",
        lemma: "zmodcl",
        left: ("A", "cz"),
        right: ("B", "cn"),
    },
];

// Which number sets lie inside which, each with the lemma saying so of a
// member (`SYNTAX.md`: a line said of every member of a set says it of every
// member of a set inside that one). One table, read by the checker and the
// elaborator alike, and declared rather than searched.
pub const SYSTEM_OF: &[(&str, &str)] = &[
    ("ℕ", "cn"),
    ("ℕ₀", "cn0"),
    ("ℤ", "cz"),
    ("ℚ", "cq"),
    ("ℝ", "cr"),
    ("ℂ", "cc"),
];

pub fn system_of(sign: &str) -> Option<&'static str> {
    lookup(SYSTEM_OF, sign)
}

pub const WITHIN: &[(&str, &[(&str, &str)])] = &[
    (
        "cn",
        &[
            ("cn0", "nnnn0"),
            ("cz", "nnz"),
            ("cq", "nnq"),
            ("cr", "nnre"),
            ("cc", "nncn"),
        ],
    ),
    ("cn0", &[("cz", "nn0z"), ("cr", "nn0re"), ("cc", "nn0cn")]),
    ("cz", &[("cq", "zq"), ("cr", "zre"), ("cc", "zcn")]),
    ("cq", &[("cr", "qre"), ("cc", "qcn")]),
    ("cr", &[("cc", "recn")]),
];

// What else a membership says of its term, as the page writes it with x for
// the term, and the lemma that says it (`SYNTAX.md`, what a membership line
// says).
pub const IMPLIED: &[(&str, &[(&str, &str)])] = &[
    ("cn", &[("x ≥ 1", "nnge1"), ("x ≠ 0", "nnne0")]),
    ("cn0", &[("x ≥ 0", "nn0ge0")]),
];

pub fn implied(system: Option<&str>) -> &'static [(&'static str, &'static str)] {
    system.and_then(|s| lookup(IMPLIED, s)).unwrap_or(&[])
}

// A part of a set is a member of its power set and the other way round: what
// a line of the first form also says, in the page's notation, and the lemma
// that says it. `gsspw` asks that the set be a set, and the elaborator proves
// it (`made_a_set`). The checker reads the two forms, the elaborator the
// lemma.
pub const PARTS: &[(&str, &str, &str)] =
    &[("x ⊆ S", "x ∈ 𝒫S", "gsspw"), ("x ∈ 𝒫S", "x ⊆ S", "elpwi")];

// A range lies inside ℕ from 1 and ℕ₀ from 0, and inside ℤ from anywhere:
// the system, the numeral it must start at or None, the lemma. The checker
// reads what a member of a range is from it, and so does the elaborator.
pub const RANGE_WITHIN: &[(&str, Option<&str>, &str)] = &[
    ("cn", Some("c1"), "elfznn"),
    ("cn0", Some("cc0"), "elfznn0"),
    ("cz", None, "elfzelz"),
];

/// The lemmas carrying a member of `small` into `big`, by labels, in order;
/// empty where the two are one; None where the table does not put `small`
/// inside `big`. A direct entry is taken over a longer way: set.mm says
/// ℕ ⊆ ℝ as `nnre`, and ℕ₀ ⊆ ℚ only by way of ℤ.
///
/// A system is None where the page wrote a set that is none of them, and two
/// such are one as far as the table is concerned, as the reference
/// implementation has them.
pub fn within_path(
    small: Option<&str>,
    big: Option<&str>,
) -> Option<Vec<&'static str>> {
    if small == big {
        return Some(Vec::new());
    }
    let row = small.and_then(|s| lookup(WITHIN, s)).unwrap_or(&[]);
    if let Some(direct) = big.and_then(|b| lookup(row, b)) {
        return Some(vec![direct]);
    }
    for (middle, lemma) in row {
        if let Some(rest) = within_path(Some(middle), big) {
            let mut out = vec![*lemma];
            out.extend(rest);
            return Some(out);
        }
    }
    None
}

/// What a term built from numerals alone is spelt with: the digits, the
/// decimal that joins them, and the operations `arithmetic` reads.
pub fn numeric(label: &str) -> bool {
    digit_of(label).is_some()
        || matches!(
            label,
            "cdc" | "co" | "caddc" | "cmin" | "cmul" | "cdiv" | "cexp" | "cneg"
        )
}

// A whole number set.mm writes in ℕ₀ is in these by the closed lemma each
// names, which asks the number's own fact and not one in a scope.
pub const FROM_NN0: &[(&str, Option<&str>)] = &[
    ("cn0", None),
    ("cz", Some("nn0zi")),
    ("cr", Some("nn0rei")),
    ("cc", Some("nn0cni")),
];

// The lemma that makes a term a set, in set.mm's sense of not a proper
// class, by the constructor at its head; what it asks is its parts'
// sethood, which the same table answers. A kernel variable is a set by
// `vex`, and a class the statement introduced by its `let` line. This is
// apparatus, and the page never writes it.
pub const SETHOOD: &[(&str, &str)] = &[
    ("cpw", "pwexg"),
    ("cdif", "difexg"),
    ("cun", "unexg"),
    ("csn", "snex"),
    ("cpr", "prex"),
    ("crn", "rnexg"),
    ("cdm", "dmexg"),
    ("cmpt", "mptexg"),
    ("cmpo", "mpoexga"),
    ("crab", "rabexg"),
    ("c0", "0ex"),
    ("cv", "vex"),
    ("co", "ovex"),
    ("cfv", "fvex"),
    ("cif", "ifexg"),
    ("cn", "nnex"),
    ("ciun", "iunexg"),
    ("ccnv", "cnvexg"),
    ("cn0", "nn0ex"),
    ("cz", "zex"),
    ("cq", "qex"),
    ("cr", "reex"),
    ("cc", "cnex"),
    ("csu", "sumex"),
    ("cprod", "prodex"),
    ("cdit", "ditgex"),
    ("cima", "imaexg"),
    ("cop", "opex"),
    ("cdc", "decex"),
    // The numerals set.mm says are sets in one lemma; 4 to 9 it does not
    // state so, and a term holding one is not settled here.
    ("cc0", "c0ex"),
    ("c1", "1ex"),
    ("c2", "2ex"),
    ("c3", "3ex"),
];

// That a term is a set with nothing assumed, where every part is one: the
// step of a define by recursion is a set at every state it is given, which
// is what makes it a function on every set. Each lemma's variables are its
// constructor's operands in order, and what it asks is that some of them
// are sets (`ifex`), which is asked of those parts the same way.
pub const CLOSED_SETHOOD: &[(&str, &str)] = &[
    ("co", "ovex"),
    ("cfv", "fvex"),
    ("cop", "opex"),
    ("csn", "snex"),
    ("cv", "vex"),
    ("cif", "ifex"),
    ("cdc", "decex"),
    ("cc0", "c0ex"),
    ("c1", "1ex"),
    ("c2", "2ex"),
    ("c3", "3ex"),
];

// Two differences against zero added, by which of the two is strictly below
// it: the lemma that adds them and keeps the strictness.
pub const ADDING: &[((bool, bool), &str)] = &[
    ((true, false), "ltleadd"),
    ((false, true), "leltadd"),
    ((true, true), "lt2add"),
];

// A denied `<` or `≤` said the other way round, by the relation denied:
// that relation's label, the one that holds instead, and the lemma saying
// the two are the same.
pub const DENIED: &[(&str, (&str, &str, &str))] = &[
    ("<", ("clt", "cle", "lenlt")),
    ("<=", ("cle", "clt", "ltnle")),
];

// What says a thing lies in a class, by where that class stands among its
// parts: a membership, and a map's codomain. Where a map's values land is
// the same kind of question as where a set lives, and set.mm asks it the
// same way: `f1f1orn` wants a codomain and says nothing about it, because
// being one-to-one into one class is being one-to-one into any that holds
// the values. A class a lemma asks for here and nothing fixes is `_V`,
// which holds them all.
pub const HELD_IN: &[(&str, usize)] =
    &[("wcel", 1), ("wf", 1), ("wf1", 1), ("wfo", 1), ("wf1o", 1)];

// The operations a method combining atoms looks inside, and the connectives
// and relations between the terms of the claim it proves.
pub const ARITHMETIC: [&str; 4] = ["caddc", "cmin", "cmul", "cdiv"];
pub const RELATIONS: [&str; 5] = ["wceq", "wne", "wbr", "wn", "wa"];

/// A two-sided statement's sides, as children.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Side {
    Left = 0,
    Right = 1,
}

// The rules that put a statement in one standard form, so that what a lemma
// says and what is wanted can be compared as they stand: each a set.mm
// biconditional or equation, by which of its two sides is the standard one.
// A rule rewrites only toward a side whose variables all appear on the
// other, so rewriting ends and has one answer: `rexss` rewrites the page's
// restriction in the body back to set.mm's restriction in the domain,
// because the other way would have to invent the larger set. What a rule
// asks — `rexss` a subset, `exp0` a complex number — is settled where it is
// applied.
pub const STANDARD: &[(&str, Side)] = &[
    ("df-3or", Side::Right),
    ("df-ne", Side::Right),
    ("ralrp", Side::Right),
    ("rexrp", Side::Right),
    ("exp0", Side::Right),
    ("nn0absid", Side::Right),
    ("rexss", Side::Left),
    ("rextru", Side::Right),
    // A member of a power set is a part of the set, as the page writes it:
    // `let X ⊆ A` holds X ∈ 𝒫A, and a lemma asks X ⊆ A.
    ("elpwg", Side::Right),
];

// The rules whose two sides are the same shape the other way round, which no
// direction can orient: the two sides are put in a fixed order instead, the
// one whose reverse Polish sorts first on the left. Inequalities are never
// among them, since their sides are not interchangeable.
pub const SYMMETRIC: [&str; 3] = ["eqcom", "addcom", "mulcom"];

// Every lemma the elaborator may lean on for a fact the text does not
// write, tried by matching its conclusion against what is wanted. A closed
// one settles it outright, one with an antecedent leaves that antecedent to
// settle in turn, and a biconditional is read whichever way reaches it.
//
// Saying it by statement rather than by shape is what lets one list answer
// every side condition there is: `k e. CC` because k runs over a range of
// integers, `( p ^ 2 ) e. ZZ` because p is one, `{ x e. A | ph } e. _V`
// because A is a set. It is declared rather than searched for: an
// elaborator that hunted through set.mm for anything that fitted would
// settle side conditions by means the text never names. The comment on
// each group says why it is here.
pub const MEMBERSHIP: &[&str] = &[
    "ax-1cn",
    "1re",
    "1z",
    "1nn",
    "2cn",
    "2re",
    "2z",
    "2nn",
    "0cn",
    "0re",
    "0z",
    "0nn0",
    "3cn",
    "3re",
    "3z",
    "4cn",
    "4re",
    "4z",
    // A numeral of more than one digit is not among these: its membership is
    // built from its digits, because `deccl` asks its parts as closed facts
    // and a search proves everything under the step's scope.
    //
    // A thing's membership of a wider system, from the narrowest system it
    // is known in first, ℕ ⊂ ℕ₀ ⊂ ℤ ⊂ ℚ ⊂ ℝ ⊂ ℂ: the most precise fact is
    // the one a membership rests on.
    "nnz",
    "nnre",
    "nncn",
    "nnnn0",
    "nn0z",
    "nn0re",
    "nn0cn",
    "zre",
    "zcn",
    "qre",
    "qcn",
    "recn",
    "elnnuz",
    "eluz2",
    "eluz2b1",
    "eluz2b2",
    "eluz2gt1",
    // Where a restriction sits is not what a claim says, and set.mm states
    // that in general: quantifying over a subset is quantifying over the set
    // with membership of the subset in the body.
    "rexss",
    "prmssnn",
    // A summation index runs over a range of integers, and what the summand
    // asks of it is not always integrality.
    "elfzelz",
    "elfznn0",
    "abscl",
    "zaddcl",
    "zsubcl",
    "zmulcl",
    "zsqcl",
    // A sum asks that its range be finite and that each of its terms be a
    // number, and a term is often a function's value at the index.
    "fzfi",
    "ffvelcdm",
    "zexpcl",
    // A binomial coefficient is a whole number at every integer, and a
    // power's exponent n − k is a whole number when k is in 0 … n.
    "bccl",
    "fznn0sub",
    // and an index of a sum to m is in the range to m + 1.
    "fzelp1",
    // An index of a sum from 1 is a natural number, where a power wants it.
    "elfznn",
    // set.mm says a coefficient is zero when k < 0 or n < k, as one
    // disjunction, and a proof says which of the two holds.
    "olc",
    "orc",
    "addcl",
    "subcl",
    "mulcl",
    "sqcl",
    "readdcl",
    "remulcl",
    "resqcl",
    "renegcl",
    "negcl",
    "reexpcl",
    "nn0expcl",
    "2nn0",
    "peano2nn0",
    // and what a commuting pair asks, which `corpus/db/notation.records` declares
    // by notation and this answers by statement
    "mulcom",
    "addcom",
    "prcom",
    // A singleton holds what it names, which `elpwg`'s users ask.
    "snidg",
    // A map sends no two things to the same place, and set.mm reaches
    // equinumerosity from it through the map itself.
    "f1f1orn",
    "f1mpt",
    // and finiteness, which the readable layer never says at all.
    "hashvnfin",
    "enfi",
    // A claim that there is one of a thing and says nothing about it is
    // nonemptiness.
    "ne0i",
    "n0",
    "rextru",
    // and what an order relation asks, which is the same kind of thing.
    "ltle",
    "ltnri",
    "leid",
    "nn0ge0",
    "nngt0",
    "nn0p1gt0",
    // A lemma stated over the integers asks what a natural number being one
    // does not say in those words.
    "nnne0",
    // The two equations in this list, and what a fact is rewritten by.
    "nn0absid",
    "exp0",
    // A disequality is one fact in two orders and the corpus writes it as a
    // negated equation, which set.mm names and then commutes.
    "df-ne",
    "necom",
    // A continuous function's domain and codomain lie in ℂ.
    "cncfrss",
    "cncfrss2",
    // A range from a to a holds a, which a sum of one term asks of its
    // term's argument.
    "elfz3",
    // and a part of ℝ is a part of ℂ, which continuity asks of a domain the
    // page says is real.
    "sstr",
    "ax-resscn",
    // And a pair that cannot both hold because one of them does not.
    "intnanrt",
    // A one-to-one function is a function.
    "f1f",
    // A function obtained from "there is f : X → Y with …" is held as a
    // member of the functions from X to Y, and is a function from X to Y.
    "elmapi",
    // A function on a set is a set, which an image under it asks.
    "fex",
    // A part of a set is a member of its power set, and the other way.
    "gsspw",
    "elpwi",
];

/// Every string the tables hold, with the table that holds it, the tables
/// in the order of their names, keys before values. Most are labels; the
/// gate keeps those that look like one and checks each against set.mm, so a
/// label written from memory into a table is caught the day it is written.
///
/// `SYSTEMS` gives its keys alone, since each value is the suffix a digit's
/// label ends with and not a label.
pub fn every_label() -> Vec<(&'static str, &'static str)> {
    let mut out: Vec<(&'static str, &'static str)> = Vec::new();
    let mut put = |table: &'static str, items: &[&'static str]| {
        out.extend(items.iter().map(|s| (table, *s)));
    };
    for (_, lemma) in ADDING {
        put("ADDING", &[lemma]);
    }
    put("ARITHMETIC", &ARITHMETIC);
    for (k, (a, b)) in BOUND {
        put("BOUND", &[k, a, b]);
    }
    for (k, v) in CLASS_BODY {
        put("CLASS_BODY", &[k, v]);
    }
    for (k, v) in CLASS_BOUND {
        put("CLASS_BOUND", &[k, v]);
    }
    for (k, _, v) in CLASS_LIFT {
        put("CLASS_LIFT", &[k, v]);
    }
    for ((op, system), v) in CLOSED {
        put("CLOSED", &[op, system, v]);
    }
    for (k, v) in CLOSED_SETHOOD {
        put("CLOSED_SETHOOD", &[k, v]);
    }
    for (k, _, v) in CONGRUENCE {
        put("CONGRUENCE", &[k, v]);
    }
    for (k, (a, b, c)) in DENIED {
        put("DENIED", &[k, a, b, c]);
    }
    for join in [Join::Implies, Join::Iff] {
        let key = if join == Join::Implies { "wi" } else { "wb" };
        put(
            "DISCHARGE",
            &[key, discharge(join, true), key, discharge(join, false)],
        );
    }
    put(
        "DISCHARGE",
        &[
            discharge(Join::Turned, true),
            discharge(Join::Turned, false),
        ],
    );
    for (k, v) in DIVIDED {
        put("DIVIDED", &[k, v]);
    }
    for (k, v) in DOMAIN {
        put("DOMAIN", &[k, v]);
    }
    for ((a, b), v) in FOLDING {
        put("FOLDING", &[a, b, v]);
    }
    for (k, v) in FROM_NN0 {
        put("FROM_NN0", &[k]);
        if let Some(v) = v {
            put("FROM_NN0", &[v]);
        }
    }
    for (k, _) in HELD_IN {
        put("HELD_IN", &[k]);
    }
    for (k, said) in IMPLIED {
        put("IMPLIED", &[k]);
        for (_, lemma) in *said {
            put("IMPLIED", &[lemma]);
        }
    }
    for (k, (a, b)) in INDUCTION {
        put("INDUCTION", &[k, a, b]);
    }
    for (k, i) in INSTANCES {
        put("INSTANCES", &[k, i.lemma]);
        if let Some(d) = i.domain {
            put("INSTANCES", &[d]);
        }
    }
    for (k, v) in JOIN {
        put("JOIN", &[k, v]);
    }
    put("MEMBERSHIP", MEMBERSHIP);
    for (k, v) in NEGATED {
        put("NEGATED", &[k, v]);
    }
    let numeric: Vec<&'static str> = NUMERALS
        .iter()
        .map(|(_, l)| *l)
        .chain(["cdc", "co", "caddc", "cmin", "cmul", "cdiv", "cexp", "cneg"])
        .collect();
    put("NUMERIC", &numeric);
    put("ONE_WAY", &[ONE_WAY.0, ONE_WAY.1]);
    for (_, _, lemma) in PARTS {
        put("PARTS", &[lemma]);
    }
    for (system, first, lemma) in RANGE_WITHIN {
        put("RANGE_WITHIN", &[system]);
        if let Some(first) = first {
            put("RANGE_WITHIN", &[first]);
        }
        put("RANGE_WITHIN", &[lemma]);
    }
    put("RELATIONS", &RELATIONS);
    for (k, _, v) in RENAMED {
        put("RENAMED", &[k, v]);
    }
    for (k, v) in SETHOOD {
        put("SETHOOD", &[k, v]);
    }
    for (k, v) in SPLIT {
        put("SPLIT", &[k]);
        put("SPLIT", v);
    }
    for (k, _) in STANDARD {
        put("STANDARD", &[k]);
    }
    put("SYMMETRIC", &SYMMETRIC);
    for (k, _) in SYSTEMS {
        put("SYSTEMS", &[k]);
    }
    for (k, v) in SYSTEM_OF {
        put("SYSTEM_OF", &[k, v]);
    }
    for (k, row) in WITHIN {
        put("WITHIN", &[k]);
        for (a, b) in *row {
            put("WITHIN", &[a, b]);
        }
    }
    for w in WHOLE {
        put("WHOLE", &[w.op, w.lemma, w.left.1, w.right.1]);
    }
    put("WRAPS", &WRAPS);
    out
}
