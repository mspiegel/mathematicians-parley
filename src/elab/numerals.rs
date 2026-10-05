//! Whole numbers as set.mm writes them, and the closed facts about them.
//!
//! A digit is its own constant, `c7`, and a longer number is set.mm's
//! decimal `; A B`: A the number its digits before the last make, B the last
//! digit, so 123 is `; ; 1 2 3`. Every fact here is closed, as
//! `|- ( ; 1 8 + 4 ) = ; 2 2` is, and is worked the way a sum is worked on
//! paper: the last digits from set.mm's tables of digits, the digits before
//! them by the same procedure, and a carry where the last digits pass nine
//! (`decadd`, `decaddc`, `decmul1`, `decmul1c`, `declt`, `decltc`). A number
//! of one digit is the table's own entry, and a number of any length is
//! computed with.
//!
//! The tables state a sum or product past nine only with the larger digit
//! first, `9p3e12` and `6t3e18`, and the other order is turned round by
//! `addcomi` or `mulcomi`.

use crate::binds;
use crate::mm::kernel::Term;
use crate::mm::spell::{Builder, Proof};
use crate::rules::{digit_of, numeral_label};
use crate::t;

const ADD: &str = "caddc";
const MUL: &str = "cmul";

/// A whole number as set.mm spells it, in reverse Polish.
pub fn spell(value: u64) -> String {
    if value < 10 {
        digit(value).to_string()
    } else {
        t!(spell(value / 10), digit(value % 10), "cdc")
    }
}

/// The number a term spells, where it is a digit or a decimal of digits
/// spelt as `spell` spells it: `; 0 5` is not how five is written, and is
/// read as no number.
pub fn value(term: &Term) -> Option<u64> {
    if term.variable().is_some() {
        return None;
    }
    let label = term.label()?;
    if let Some(d) = digit_of(label) {
        return term.children().is_empty().then_some(d as u64);
    }
    if label != "cdc" || term.children().len() != 2 {
        return None;
    }
    let upper = value(&term.children()[0])?;
    let last = term.children()[1].label().and_then(digit_of)?;
    (upper > 0 && term.children()[1].children().is_empty())
        .then_some(upper * 10 + last as u64)
}

fn digit(value: u64) -> &'static str {
    numeral_label(value as u32).expect("a digit")
}

fn op(left: &str, right: &str, what: &str) -> String {
    t!(left, right, what, "co")
}

/// |- n e. NN0
pub fn nn0(b: &Builder, n: u64) -> Proof {
    if n < 10 {
        return b.step(&format!("{n}nn0"));
    }
    b.ap(
        "deccl",
        &binds! {"A" => spell(n / 10), "B" => digit(n % 10)},
        &[&nn0(b, n / 10), &nn0(b, n % 10)],
    )
}

/// |- n e. NN, for n at least one: a decimal is positive by its last digit
/// (`decnncl`) or, ending in zero, by the digits before it (`decnncl2`).
pub fn nn(b: &Builder, n: u64) -> Proof {
    if n < 10 {
        return b.step(&format!("{n}nn"));
    }
    if !n.is_multiple_of(10) {
        return b.ap(
            "decnncl",
            &binds! {"A" => spell(n / 10), "B" => digit(n % 10)},
            &[&nn0(b, n / 10), &nn(b, n % 10)],
        );
    }
    b.ap(
        "decnncl2",
        &binds! {"A" => spell(n / 10)},
        &[&nn(b, n / 10)],
    )
}

/// |- n e. CC. set.mm takes the one for 1 as an axiom.
pub fn cc(b: &Builder, n: u64) -> Proof {
    match n {
        1 => b.step("ax-1cn"),
        0..=9 => b.step(&format!("{n}cn")),
        _ => b.ap("nn0cni", &binds! {"A" => spell(n)}, &[&nn0(b, n)]),
    }
}

/// |- n e. RR
pub fn re(b: &Builder, n: u64) -> Proof {
    if n < 10 {
        return b.step(&format!("{n}re"));
    }
    b.ap("nn0rei", &binds! {"A" => spell(n)}, &[&nn0(b, n)])
}

/// |- n =/= 0, for n at least one.
pub fn ne0(b: &Builder, n: u64) -> Proof {
    match n {
        1 => b.step("ax-1ne0"),
        0..=9 => b.step(&format!("{n}ne0")),
        _ => b.ap("nnne0i", &binds! {"A" => spell(n)}, &[&nn(b, n)]),
    }
}

/// |- 0 < n, for n at least one: `npos` for a digit, and `0lt1` for one.
pub fn pos(b: &Builder, n: u64) -> Proof {
    match n {
        1 => b.step("0lt1"),
        0..=9 => b.step(&format!("{n}pos")),
        _ => b.ap("nngt0i", &binds! {"A" => spell(n)}, &[&nn(b, n)]),
    }
}

/// |- ( a = c ) from |- a = b and |- b = c.
fn chain(
    b: &Builder,
    first: &Proof,
    second: &Proof,
    a: &str,
    m: &str,
    c: &str,
) -> Proof {
    b.ap(
        "eqtri",
        &binds! {"A" => a, "B" => m, "C" => c},
        &[first, second],
    )
}

/// |- ( ( x F y ) G z ) = ( w G z ) from |- ( x F y ) = w: the first
/// operand of an outer operation replaced by what it equals.
fn first_replaced(
    b: &Builder,
    inner: &Proof,
    was: &str,
    now: &str,
    by: &str,
    what: &str,
) -> Proof {
    b.ap(
        "oveq1i",
        &binds! {"A" => was, "B" => now, "C" => by, "F" => what},
        &[inner],
    )
}

/// |- `n = ; A B` for the digits before the last and the last: a decimal is
/// that already (`eqid`), and a digit is `; 0 n` (`dec0h`).
fn split(b: &Builder, n: u64) -> Proof {
    if n >= 10 {
        return b.ap("eqid", &binds! {"A" => spell(n)}, &[]);
    }
    b.ap("dec0h", &binds! {"A" => spell(n)}, &[&nn0(b, n)])
}

/// |- ( m + n ) = s, s spelt as `spell` spells m + n.
pub fn sum(b: &Builder, m: u64, n: u64) -> Proof {
    let (sm, sn) = (spell(m), spell(n));
    if n == 0 {
        return b.ap("addridi", &binds! {"A" => &sm}, &[&cc(b, m)]);
    }
    if m == 0 {
        return b.ap("addlidi", &binds! {"A" => &sn}, &[&cc(b, n)]);
    }
    if m < 10 && n < 10 {
        if m >= n || m + n < 10 {
            return b.step(&format!("{m}p{n}e{}", m + n));
        }
        let turned = b.ap(
            "addcomi",
            &binds! {"A" => &sm, "B" => &sn},
            &[&cc(b, m), &cc(b, n)],
        );
        let s = spell(m + n);
        return chain(
            b,
            &turned,
            &sum(b, n, m),
            &op(&sm, &sn, ADD),
            &op(&sn, &sm, ADD),
            &s,
        );
    }
    let (a, last_m, c, last_n) = (m / 10, m % 10, n / 10, n % 10);
    let (sa, sc) = (spell(a), spell(c));
    let total = m + n;
    let mut binds = binds! {
        "A" => &sa, "B" => digit(last_m), "C" => &sc, "D" => digit(last_n),
        "M" => &sm, "N" => &sn,
        "E" => spell(total / 10), "F" => digit(total % 10),
    };
    let shared = [
        nn0(b, a),
        nn0(b, last_m),
        nn0(b, c),
        nn0(b, last_n),
        split(b, m),
        split(b, n),
    ];
    if last_m + last_n < 10 {
        let upper = sum(b, a, c);
        let lower = sum(b, last_m, last_n);
        let hyps: Vec<&Proof> = shared.iter().chain([&upper, &lower]).collect();
        return b.ap("decadd", &binds, &hyps);
    }
    // The last digits pass nine: one is carried to the digits before.
    let upper = sum(b, a, c);
    let carried =
        first_replaced(b, &upper, &op(&sa, &sc, ADD), &spell(a + c), digit(1), ADD);
    let once_more = sum(b, a + c, 1);
    let e = chain(
        b,
        &carried,
        &once_more,
        &op(&op(&sa, &sc, ADD), digit(1), ADD),
        &op(&spell(a + c), digit(1), ADD),
        &spell(a + c + 1),
    );
    binds.insert("E".to_string(), spell(a + c + 1));
    let f = nn0(b, (last_m + last_n) % 10);
    let lower = sum(b, last_m, last_n);
    let hyps: Vec<&Proof> = shared.iter().chain([&e, &f, &lower]).collect();
    b.ap("decaddc", &binds, &hyps)
}

/// |- ( m x. p ) = r, r spelt as `spell` spells m times p: the last digit
/// of m times p, and the digits before it times p with what that carries.
pub fn product(b: &Builder, m: u64, p: u64) -> Proof {
    let (sm, sp) = (spell(m), spell(p));
    if p == 0 {
        return b.ap("mul01i", &binds! {"A" => &sm}, &[&cc(b, m)]);
    }
    if m == 0 {
        return b.ap("mul02i", &binds! {"A" => &sp}, &[&cc(b, p)]);
    }
    if p == 1 {
        return b.ap("mulridi", &binds! {"A" => &sm}, &[&cc(b, m)]);
    }
    if m == 1 {
        return b.ap("mullidi", &binds! {"A" => &sp}, &[&cc(b, p)]);
    }
    if m < 10 && p < 10 && (m >= p || m * p < 10) {
        return b.step(&format!("{m}t{p}e{}", m * p));
    }
    if m < 10 {
        let turned = b.ap(
            "mulcomi",
            &binds! {"A" => &sm, "B" => &sp},
            &[&cc(b, m), &cc(b, p)],
        );
        let r = spell(m * p);
        return chain(
            b,
            &turned,
            &product(b, p, m),
            &op(&sm, &sp, MUL),
            &op(&sp, &sm, MUL),
            &r,
        );
    }
    let (a, last) = (m / 10, m % 10);
    let sa = spell(a);
    let low = last * p;
    let whole = m * p;
    let binds = binds! {
        "P" => &sp, "A" => &sa, "B" => digit(last), "N" => &sm,
        "C" => spell(whole / 10), "D" => digit(whole % 10), "E" => spell(low / 10),
    };
    let shared = [nn0(b, p), nn0(b, a), nn0(b, last), split(b, m)];
    let upper = product(b, a, p);
    let lower = product(b, last, p);
    if low < 10 {
        let hyps: Vec<&Proof> = shared.iter().chain([&upper, &lower]).collect();
        return b.ap("decmul1", &binds, &hyps);
    }
    // The last digit's product passes nine: its tens are carried.
    let carry = low / 10;
    let replaced = first_replaced(
        b,
        &upper,
        &op(&sa, &sp, MUL),
        &spell(a * p),
        &spell(carry),
        ADD,
    );
    let added = sum(b, a * p, carry);
    let c = chain(
        b,
        &replaced,
        &added,
        &op(&op(&sa, &sp, MUL), &spell(carry), ADD),
        &op(&spell(a * p), &spell(carry), ADD),
        &spell(a * p + carry),
    );
    let (d, e) = (nn0(b, low % 10), nn0(b, carry));
    let hyps: Vec<&Proof> = shared.iter().chain([&d, &e, &c, &lower]).collect();
    b.ap("decmul1c", &binds, &hyps)
}

/// |- d < ; 1 0, for a digit.
fn below_ten(b: &Builder, d: u64) -> Proof {
    if d == 0 {
        return pos(b, 10);
    }
    b.step(&format!("{d}lt10"))
}

/// |- a < c, for a below c: by the digits before the last where they
/// differ (`decltc`), and by the last digits where they do not (`declt`).
pub fn below(b: &Builder, a: u64, c: u64) -> Proof {
    assert!(a < c, "{a} is not below {c}");
    if a == 0 {
        return pos(b, c);
    }
    if c < 10 {
        return b.step(&format!("{a}lt{c}"));
    }
    let (cu, cl) = (c / 10, c % 10);
    if a < 10 {
        return b.ap(
            "declti",
            &binds! {"A" => spell(cu), "B" => digit(cl), "C" => digit(a)},
            &[&nn(b, cu), &nn0(b, cl), &nn0(b, a), &below_ten(b, a)],
        );
    }
    let (au, al) = (a / 10, a % 10);
    if au == cu {
        return b.ap(
            "declt",
            &binds! {"A" => spell(au), "B" => digit(al), "C" => digit(cl)},
            &[&nn0(b, au), &nn0(b, al), &nn(b, cl), &below(b, al, cl)],
        );
    }
    b.ap(
        "decltc",
        &binds! {"A" => spell(au), "B" => spell(cu), "C" => digit(al), "D" => digit(cl)},
        &[
            &nn0(b, au),
            &nn0(b, cu),
            &nn0(b, al),
            &nn0(b, cl),
            &below_ten(b, al),
            &below(b, au, cu),
        ],
    )
}
