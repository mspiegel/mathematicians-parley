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
//! computed with: the numbers are held as big integers, so a product of
//! sixty digits is spelt as exactly as a digit is.
//!
//! The tables state a sum or product past nine only with the larger digit
//! first, `9p3e12` and `6t3e18`, and the other order is turned round by
//! `addcomi` or `mulcomi`.

use num_bigint::BigUint;
use num_traits::{One, ToPrimitive, Zero};

use crate::binds;
use crate::mm::kernel::{FloatLabels, Term};
use crate::mm::spell::{Builder, Proof};
use crate::rules::{digit_of, numeral_label};
use crate::t;

const ADD: &str = "caddc";
const SUB: &str = "cmin";
const MUL: &str = "cmul";
const EXP: &str = "cexp";
const MOD: &str = "cmo";

/// The digits before the last, and the last.
fn last_off(n: &BigUint) -> (BigUint, u32) {
    let last = (n % 10u32).to_u32().expect("a digit");
    (n / 10u32, last)
}

/// The number itself where it is one digit.
fn one_digit(n: &BigUint) -> Option<u32> {
    (*n < BigUint::from(10u32)).then(|| n.to_u32().expect("a digit"))
}

/// A whole number as set.mm spells it, in reverse Polish.
pub fn spell(value: impl Into<BigUint>) -> String {
    spelt(&value.into())
}

fn spelt(value: &BigUint) -> String {
    match one_digit(value) {
        Some(d) => digit(d).to_string(),
        None => {
            let (upper, last) = last_off(value);
            t!(spelt(&upper), digit(last), "cdc")
        }
    }
}

/// The number a term spells, where it is a digit or a decimal of digits
/// spelt as `spell` spells it: `; 0 5` is not how five is written, and is
/// read as no number.
pub fn value(term: &Term) -> Option<BigUint> {
    if term.variable().is_some() {
        return None;
    }
    let label = term.label()?;
    if let Some(d) = digit_of(label) {
        return term.children().is_empty().then(|| BigUint::from(d));
    }
    if label != "cdc" || term.children().len() != 2 {
        return None;
    }
    let upper = value(&term.children()[0])?;
    let last = term.children()[1].label().and_then(digit_of)?;
    (!upper.is_zero() && term.children()[1].children().is_empty())
        .then(|| upper * 10u32 + last)
}

fn digit(value: u32) -> &'static str {
    numeral_label(value).expect("a digit")
}

fn op(left: &str, right: &str, what: &str) -> String {
    t!(left, right, what, "co")
}

/// |- n e. NN0
pub fn nn0(b: &Builder, n: impl Into<BigUint>) -> Proof {
    nn0_of(b, &n.into())
}

fn nn0_of(b: &Builder, n: &BigUint) -> Proof {
    if let Some(d) = one_digit(n) {
        return b.step(&format!("{d}nn0"));
    }
    let (upper, last) = last_off(n);
    b.ap(
        "deccl",
        &binds! {"A" => spelt(&upper), "B" => digit(last)},
        &[&nn0_of(b, &upper), &nn0_of(b, &BigUint::from(last))],
    )
}

/// |- n e. NN, for n at least one: a decimal is positive by its last digit
/// (`decnncl`) or, ending in zero, by the digits before it (`decnncl2`).
pub fn nn(b: &Builder, n: impl Into<BigUint>) -> Proof {
    nn_of(b, &n.into())
}

fn nn_of(b: &Builder, n: &BigUint) -> Proof {
    if let Some(d) = one_digit(n) {
        return b.step(&format!("{d}nn"));
    }
    let (upper, last) = last_off(n);
    if last != 0 {
        return b.ap(
            "decnncl",
            &binds! {"A" => spelt(&upper), "B" => digit(last)},
            &[&nn0_of(b, &upper), &nn_of(b, &BigUint::from(last))],
        );
    }
    b.ap(
        "decnncl2",
        &binds! {"A" => spelt(&upper)},
        &[&nn_of(b, &upper)],
    )
}

/// |- n e. CC. set.mm takes the one for 1 as an axiom.
pub fn cc(b: &Builder, n: impl Into<BigUint>) -> Proof {
    cc_of(b, &n.into())
}

fn cc_of(b: &Builder, n: &BigUint) -> Proof {
    match one_digit(n) {
        Some(1) => b.step("ax-1cn"),
        Some(d) => b.step(&format!("{d}cn")),
        None => b.ap("nn0cni", &binds! {"A" => spelt(n)}, &[&nn0_of(b, n)]),
    }
}

/// |- n e. RR
pub fn re(b: &Builder, n: impl Into<BigUint>) -> Proof {
    let n = n.into();
    if let Some(d) = one_digit(&n) {
        return b.step(&format!("{d}re"));
    }
    b.ap("nn0rei", &binds! {"A" => spelt(&n)}, &[&nn0_of(b, &n)])
}

/// |- n =/= 0, for n at least one.
pub fn ne0(b: &Builder, n: impl Into<BigUint>) -> Proof {
    let n = n.into();
    match one_digit(&n) {
        Some(1) => b.step("ax-1ne0"),
        Some(d) => b.step(&format!("{d}ne0")),
        None => b.ap("nnne0i", &binds! {"A" => spelt(&n)}, &[&nn_of(b, &n)]),
    }
}

/// |- 0 < n, for n at least one: `npos` for a digit, and `0lt1` for one.
pub fn pos(b: &Builder, n: impl Into<BigUint>) -> Proof {
    pos_of(b, &n.into())
}

fn pos_of(b: &Builder, n: &BigUint) -> Proof {
    match one_digit(n) {
        Some(1) => b.step("0lt1"),
        Some(d) => b.step(&format!("{d}pos")),
        None => b.ap("nngt0i", &binds! {"A" => spelt(n)}, &[&nn_of(b, n)]),
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
fn split(b: &Builder, n: &BigUint) -> Proof {
    if one_digit(n).is_none() {
        return b.ap("eqid", &binds! {"A" => spelt(n)}, &[]);
    }
    b.ap("dec0h", &binds! {"A" => spelt(n)}, &[&nn0_of(b, n)])
}

/// |- ( m + n ) = s, s spelt as `spell` spells m + n.
pub fn sum(b: &Builder, m: impl Into<BigUint>, n: impl Into<BigUint>) -> Proof {
    sum_of(b, &m.into(), &n.into())
}

fn sum_of(b: &Builder, m: &BigUint, n: &BigUint) -> Proof {
    let (sm, sn) = (spelt(m), spelt(n));
    if n.is_zero() {
        return b.ap("addridi", &binds! {"A" => &sm}, &[&cc_of(b, m)]);
    }
    if m.is_zero() {
        return b.ap("addlidi", &binds! {"A" => &sn}, &[&cc_of(b, n)]);
    }
    if let (Some(dm), Some(dn)) = (one_digit(m), one_digit(n)) {
        if dm >= dn || dm + dn < 10 {
            return b.step(&format!("{dm}p{dn}e{}", dm + dn));
        }
        let turned = b.ap(
            "addcomi",
            &binds! {"A" => &sm, "B" => &sn},
            &[&cc_of(b, m), &cc_of(b, n)],
        );
        return chain(
            b,
            &turned,
            &sum_of(b, n, m),
            &op(&sm, &sn, ADD),
            &op(&sn, &sm, ADD),
            &spelt(&(m + n)),
        );
    }
    let ((a, last_m), (c, last_n)) = (last_off(m), last_off(n));
    let (sa, sc) = (spelt(&a), spelt(&c));
    let total = m + n;
    let (total_upper, total_last) = last_off(&total);
    let mut binds = binds! {
        "A" => &sa, "B" => digit(last_m), "C" => &sc, "D" => digit(last_n),
        "M" => &sm, "N" => &sn,
        "E" => spelt(&total_upper), "F" => digit(total_last),
    };
    let (bm, bn) = (BigUint::from(last_m), BigUint::from(last_n));
    let shared = [
        nn0_of(b, &a),
        nn0_of(b, &bm),
        nn0_of(b, &c),
        nn0_of(b, &bn),
        split(b, m),
        split(b, n),
    ];
    if last_m + last_n < 10 {
        let upper = sum_of(b, &a, &c);
        let lower = sum_of(b, &bm, &bn);
        let hyps: Vec<&Proof> = shared.iter().chain([&upper, &lower]).collect();
        return b.ap("decadd", &binds, &hyps);
    }
    // The last digits pass nine: one is carried to the digits before.
    let upper = sum_of(b, &a, &c);
    let ac = &a + &c;
    let carried =
        first_replaced(b, &upper, &op(&sa, &sc, ADD), &spelt(&ac), digit(1), ADD);
    let once_more = sum_of(b, &ac, &BigUint::one());
    let e = chain(
        b,
        &carried,
        &once_more,
        &op(&op(&sa, &sc, ADD), digit(1), ADD),
        &op(&spelt(&ac), digit(1), ADD),
        &spelt(&(&ac + 1u32)),
    );
    binds.insert("E".to_string(), spelt(&(&ac + 1u32)));
    let f = nn0_of(b, &BigUint::from((last_m + last_n) % 10));
    let lower = sum_of(b, &bm, &bn);
    let hyps: Vec<&Proof> = shared.iter().chain([&e, &f, &lower]).collect();
    b.ap("decaddc", &binds, &hyps)
}

/// |- ( m x. p ) = r, r spelt as `spell` spells m times p: the last digit
/// of m times p, and the digits before it times p with what that carries.
pub fn product(b: &Builder, m: impl Into<BigUint>, p: impl Into<BigUint>) -> Proof {
    product_of(b, &m.into(), &p.into())
}

fn product_of(b: &Builder, m: &BigUint, p: &BigUint) -> Proof {
    let (sm, sp) = (spelt(m), spelt(p));
    if p.is_zero() {
        return b.ap("mul01i", &binds! {"A" => &sm}, &[&cc_of(b, m)]);
    }
    if m.is_zero() {
        return b.ap("mul02i", &binds! {"A" => &sp}, &[&cc_of(b, p)]);
    }
    if p.is_one() {
        return b.ap("mulridi", &binds! {"A" => &sm}, &[&cc_of(b, m)]);
    }
    if m.is_one() {
        return b.ap("mullidi", &binds! {"A" => &sp}, &[&cc_of(b, p)]);
    }
    if let (Some(dm), Some(dp)) = (one_digit(m), one_digit(p)) {
        if dm >= dp || dm * dp < 10 {
            return b.step(&format!("{dm}t{dp}e{}", dm * dp));
        }
    }
    if one_digit(m).is_some() {
        let turned = b.ap(
            "mulcomi",
            &binds! {"A" => &sm, "B" => &sp},
            &[&cc_of(b, m), &cc_of(b, p)],
        );
        return chain(
            b,
            &turned,
            &product_of(b, p, m),
            &op(&sm, &sp, MUL),
            &op(&sp, &sm, MUL),
            &spelt(&(m * p)),
        );
    }
    let (a, last) = last_off(m);
    let sa = spelt(&a);
    let bl = BigUint::from(last);
    let low = &bl * p;
    let whole = m * p;
    let ((whole_upper, whole_last), (carry, low_last)) =
        (last_off(&whole), last_off(&low));
    let binds = binds! {
        "P" => &sp, "A" => &sa, "B" => digit(last), "N" => &sm,
        "C" => spelt(&whole_upper), "D" => digit(whole_last), "E" => spelt(&carry),
    };
    let shared = [nn0_of(b, p), nn0_of(b, &a), nn0_of(b, &bl), split(b, m)];
    let upper = product_of(b, &a, p);
    let lower = product_of(b, &bl, p);
    if carry.is_zero() {
        let hyps: Vec<&Proof> = shared.iter().chain([&upper, &lower]).collect();
        return b.ap("decmul1", &binds, &hyps);
    }
    // The last digit's product passes nine: its tens are carried.
    let ap = &a * p;
    let replaced = first_replaced(
        b,
        &upper,
        &op(&sa, &sp, MUL),
        &spelt(&ap),
        &spelt(&carry),
        ADD,
    );
    let added = sum_of(b, &ap, &carry);
    let c = chain(
        b,
        &replaced,
        &added,
        &op(&op(&sa, &sp, MUL), &spelt(&carry), ADD),
        &op(&spelt(&ap), &spelt(&carry), ADD),
        &spelt(&(&ap + &carry)),
    );
    let (d, e) = (nn0_of(b, &BigUint::from(low_last)), nn0_of(b, &carry));
    let hyps: Vec<&Proof> = shared.iter().chain([&d, &e, &c, &lower]).collect();
    b.ap("decmul1c", &binds, &hyps)
}

/// |- ( a ^ k ) = r, r spelt as `spell` spells a to the k: a to one less,
/// times a (`numexpp1`), down to `numexp1` and `numexp0`.
pub fn power(b: &Builder, a: impl Into<BigUint>, k: u32) -> Proof {
    power_of(b, &a.into(), k)
}

fn power_of(b: &Builder, a: &BigUint, k: u32) -> Proof {
    let sa = spelt(a);
    match k {
        0 => return b.ap("numexp0", &binds! {"A" => &sa}, &[&nn0_of(b, a)]),
        1 => return b.ap("numexp1", &binds! {"A" => &sa}, &[&nn0_of(b, a)]),
        _ => {}
    }
    let less = BigUint::from(k - 1);
    let sl = spelt(&less);
    let below = a.pow(k - 1);
    let raised = &below * a;
    let replaced = first_replaced(
        b,
        &power_of(b, a, k - 1),
        &op(&sa, &sl, EXP),
        &spelt(&below),
        &sa,
        MUL,
    );
    let times = chain(
        b,
        &replaced,
        &product_of(b, &below, a),
        &op(&op(&sa, &sl, EXP), &sa, MUL),
        &op(&spelt(&below), &sa, MUL),
        &spelt(&raised),
    );
    b.ap(
        "numexpp1",
        &binds! {"A" => &sa, "M" => &sl, "N" => spelt(&BigUint::from(k)), "C" => spelt(&raised)},
        &[&nn0_of(b, a), &nn0_of(b, &less), &sum_of(b, &less, &BigUint::one()), &times],
    )
}

/// |- ( x mod n ) = r, for n at least 1 and r what is left of x on taking
/// away the most whole multiples of n it holds (`METHODS.md`, arithmetic):
/// x is r + q·n, `modcyc` takes the q·n away, and `modid` says r, being
/// below n, is its own remainder.
fn remainder_of(b: &Builder, x: &BigUint, n: &BigUint) -> Proof {
    let (q, r) = (x / n, x % n);
    let (sx, sn, sq, sr) = (spelt(x), spelt(n), spelt(&q), spelt(&r));
    let positive = b.ap(
        "ax-mp",
        &binds! {"ph" => t!(sn, "cn", "wcel"), "ps" => t!(sn, "crp", "wcel")},
        &[&nn_of(b, n), &b.ap("nnrp", &binds! {"A" => &sn}, &[])],
    );
    let real_r = re(b, r.clone());
    let sizes = b.ap(
        "pm3.2i",
        &binds! {"ph" => t!(sr, "cr", "wcel"), "ps" => t!(sn, "crp", "wcel")},
        &[&real_r, &positive],
    );
    let bounds = b.ap(
        "pm3.2i",
        &binds! {"ph" => t!("cc0", sr, "cle", "wbr"), "ps" => t!(sr, sn, "clt", "wbr")},
        &[
            &b.ap("nn0ge0i", &binds! {"N" => &sr}, &[&nn0_of(b, &r)]),
            &below_of(b, &r, n),
        ],
    );
    let own = b.ap(
        "mp2an",
        &binds! {
            "ph" => t!(t!(sr, "cr", "wcel"), t!(sn, "crp", "wcel"), "wa"),
            "ps" => t!(t!("cc0", sr, "cle", "wbr"), t!(sr, sn, "clt", "wbr"), "wa"),
            "ch" => t!(op(&sr, &sn, MOD), sr, "wceq"),
        },
        &[
            &sizes,
            &bounds,
            &b.ap("modid", &binds! {"A" => &sr, "B" => &sn}, &[]),
        ],
    );
    if q.is_zero() {
        return own;
    }
    // x = r + q·n, worked from q·n = p and r + p = x.
    let times = op(&sq, &sn, MUL);
    let p = &q * n;
    let sp = spelt(&p);
    let added = op(&sr, &times, ADD);
    let moved = b.ap(
        "oveq2i",
        &binds! {"A" => &times, "B" => &sp, "C" => &sr, "F" => ADD},
        &[&product_of(b, &q, n)],
    );
    let total = b.ap(
        "eqtri",
        &binds! {"A" => &added, "B" => op(&sr, &sp, ADD), "C" => &sx},
        &[&moved, &sum_of(b, &r, &p)],
    );
    let written = b.ap(
        "oveq1i",
        &binds! {"A" => &sx, "B" => &added, "C" => &sn, "F" => MOD},
        &[&b.ap("eqcomi", &binds! {"A" => &added, "B" => &sx}, &[&total])],
    );
    let cycled = b.ap(
        "mp3an",
        &binds! {
            "ph" => t!(sr, "cr", "wcel"), "ps" => t!(sn, "crp", "wcel"),
            "ch" => t!(sq, "cz", "wcel"),
            "th" => t!(op(&added, &sn, MOD), op(&sr, &sn, MOD), "wceq"),
        },
        &[
            &real_r,
            &positive,
            &b.ap("nn0zi", &binds! {"N" => &sq}, &[&nn0_of(b, &q)]),
            &b.ap("modcyc", &binds! {"A" => &sr, "B" => &sn, "N" => &sq}, &[]),
        ],
    );
    let gone = b.ap(
        "eqtri",
        &binds! {"A" => op(&added, &sn, MOD), "B" => op(&sr, &sn, MOD), "C" => &sr},
        &[&cycled, &own],
    );
    b.ap(
        "eqtri",
        &binds! {"A" => op(&sx, &sn, MOD), "B" => op(&added, &sn, MOD), "C" => &sr},
        &[&written, &gone],
    )
}

/// A closed term of whole numbers, sums, products, whole powers and
/// remainders, with its value and |- term = value; None for anything else. A numeral is its
/// own value, and is proved so by `eqid`.
pub fn worked(
    b: &Builder,
    term: &Term,
    labels: &FloatLabels,
) -> Option<(BigUint, Proof)> {
    let said = term.rpn(labels).to_string();
    if let Some(v) = value(term) {
        let same = b.ap("eqid", &binds! {"A" => &said}, &[]);
        return Some((v, same));
    }
    if term.variable().is_none() && term.label() == Some("cprod") {
        return product_over_range(b, term, labels);
    }
    if term.variable().is_some()
        || term.label() != Some("co")
        || term.children().len() != 3
    {
        return None;
    }
    let kids = term.children();
    let how = kids[2].label()?;
    if ![ADD, SUB, MUL, EXP, MOD].contains(&how) {
        return None;
    }
    let (left, first) = worked(b, &kids[0], labels)?;
    let (right, second) = worked(b, &kids[1], labels)?;
    let (sl, sr) = (spelt(&left), spelt(&right));
    let (result, value_of) = match how {
        ADD => (&left + &right, sum_of(b, &left, &right)),
        // A difference is worked only where it is a whole number again.
        SUB if right <= left => {
            let gap = &left - &right;
            let held = b.ap(
                "subaddrii",
                &binds! {"A" => &sl, "B" => &sr, "C" => spelt(&gap)},
                &[
                    &cc_of(b, &left),
                    &cc_of(b, &right),
                    &cc_of(b, &gap),
                    &sum_of(b, &right, &gap),
                ],
            );
            (gap, held)
        }
        SUB => return None,
        MUL => (&left * &right, product_of(b, &left, &right)),
        // A remainder is worked only on dividing by a whole number of at
        // least 1.
        MOD if right.is_zero() => return None,
        MOD => (&left % &right, remainder_of(b, &left, &right)),
        _ => {
            let k = right.to_u32()?;
            (left.pow(k), power_of(b, &left, k))
        }
    };
    let parts = b.ap(
        "oveq12i",
        &binds! {
            "A" => kids[0].rpn(labels).to_string(), "B" => &sl,
            "C" => kids[1].rpn(labels).to_string(), "D" => &sr,
            "F" => how,
        },
        &[&first, &second],
    );
    let whole = chain(
        b,
        &parts,
        &value_of,
        &said,
        &op(&sl, &sr, how),
        &spelt(&result),
    );
    Some((result, whole))
}

/// The numeral `value` as a term.
fn numeral_term(value: &BigUint) -> Term {
    match one_digit(value) {
        Some(d) => Term::apply(digit(d), Vec::new()),
        None => {
            let (upper, last) = last_off(value);
            Term::apply(
                "cdc",
                vec![numeral_term(&upper), Term::apply(digit(last), Vec::new())],
            )
        }
    }
}

/// The term with the numeral `value` written for the letter k.
pub fn at_number(term: &Term, k: &str, value: &BigUint) -> Term {
    put(term, k, &numeral_term(value))
}

/// Whether a term is the letter k used as a number, `cv k`.
fn is_letter(term: &Term, k: &str) -> bool {
    term.label() == Some("cv")
        && term.children().len() == 1
        && term.children()[0].variable() == Some(k)
}

/// The term with `at` written for the letter k.
fn put(term: &Term, k: &str, at: &Term) -> Term {
    if is_letter(term, k) {
        return at.clone();
    }
    match term.label() {
        Some(label) if term.variable().is_none() => Term::apply(
            label,
            term.children().iter().map(|c| put(c, k, at)).collect(),
        ),
        _ => term.clone(),
    }
}

/// |- ( k = at -> body = body at at ), by `id` at the letter, `eqidd`
/// where it is absent, and `oveq12d` through each operation.
fn at_index(
    b: &Builder,
    body: &Term,
    k: &str,
    at: &Term,
    labels: &FloatLabels,
) -> Option<Proof> {
    let kv = Term::var(k).rpn(labels).to_string();
    let hyp = t!(&kv, "cv", at.rpn(labels).to_string(), "wceq");
    if is_letter(body, k) {
        return Some(b.ap("id", &binds! {"ph" => &hyp}, &[]));
    }
    if !body.names().iter().any(|n| &**n == k) {
        return Some(b.ap(
            "eqidd",
            &binds! {"ph" => &hyp, "A" => body.rpn(labels).to_string()},
            &[],
        ));
    }
    if body.variable().is_some()
        || body.label() != Some("co")
        || body.children().len() != 3
    {
        return None;
    }
    let kids = body.children();
    let first = at_index(b, &kids[0], k, at, labels)?;
    let second = at_index(b, &kids[1], k, at, labels)?;
    Some(b.ap(
        "oveq12d",
        &binds! {
            "ph" => &hyp,
            "A" => kids[0].rpn(labels).to_string(), "B" => put(&kids[0], k, at).rpn(labels).to_string(),
            "C" => kids[1].rpn(labels).to_string(), "D" => put(&kids[1], k, at).rpn(labels).to_string(),
            "F" => kids[2].rpn(labels).to_string(),
        },
        &[&first, &second],
    ))
}

/// |- ( context -> body e. CC ), from what the context says of k.
fn complex_in(
    b: &Builder,
    context: &str,
    body: &Term,
    k: &str,
    k_complex: &Proof,
    labels: &FloatLabels,
) -> Option<Proof> {
    if is_letter(body, k) {
        return Some(k_complex.clone());
    }
    let said = body.rpn(labels).to_string();
    if let Some(v) = value(body) {
        return Some(b.ap(
            "a1i",
            &binds! {"ph" => t!(&said, "cc", "wcel"), "ps" => context},
            &[&cc_of(b, &v)],
        ));
    }
    if body.variable().is_some()
        || body.label() != Some("co")
        || body.children().len() != 3
    {
        return None;
    }
    let kids = body.children();
    let (sa, sb) = (
        kids[0].rpn(labels).to_string(),
        kids[1].rpn(labels).to_string(),
    );
    let first = complex_in(b, context, &kids[0], k, k_complex, labels)?;
    let law = match kids[2].label()? {
        ADD => "addcld",
        SUB => "subcld",
        MUL => "mulcld",
        EXP => {
            let by = value(&kids[1])?;
            let natural = b.ap(
                "a1i",
                &binds! {"ph" => t!(&sb, "cn0", "wcel"), "ps" => context},
                &[&nn0_of(b, &by)],
            );
            return Some(b.ap(
                "expcld",
                &binds! {"ph" => context, "A" => &sa, "N" => &sb},
                &[&first, &natural],
            ));
        }
        _ => return None,
    };
    let second = complex_in(b, context, &kids[1], k, k_complex, labels)?;
    Some(b.ap(
        law,
        &binds! {"ph" => context, "A" => &sa, "B" => &sb},
        &[&first, &second],
    ))
}

/// A product over a range of numerals, ∏(k ∈ {a, …, n}) body, worked a
/// factor at a time: the last factor taken off (`fprodp1`) down to the
/// first alone (`fprod1`), each factor worked as a closed term.
fn product_over_range(
    b: &Builder,
    term: &Term,
    labels: &FloatLabels,
) -> Option<(BigUint, Proof)> {
    let kids = term.children();
    if kids.len() != 3 {
        return None;
    }
    let (range, body) = (&kids[0], &kids[1]);
    let k = kids[2].variable()?.to_string();
    if range.label() != Some("co")
        || range.children().len() != 3
        || range.children()[2].label() != Some("cfz")
    {
        return None;
    }
    let from = value(&range.children()[0])?;
    let to = value(&range.children()[1])?;
    if to < from {
        return None;
    }
    let names_only_k = body.names().iter().all(|n| **n == *k);
    if !names_only_k {
        return None;
    }
    product_up_to(b, body, &k, &from, &to, labels)
}

/// |- prod_ k e. ( from ... to ) body = value.
fn product_up_to(
    b: &Builder,
    body: &Term,
    k: &str,
    from: &BigUint,
    to: &BigUint,
    labels: &FloatLabels,
) -> Option<(BigUint, Proof)> {
    let kv = Term::var(k).rpn(labels).to_string();
    let sbody = body.rpn(labels).to_string();
    let sf = spelt(from);
    let product = |top: &str| t!(op(&sf, top, "cfz"), &sbody, &kv, "cprod");
    if to == from {
        let at = numeral_term(from);
        let instance = put(body, k, &at);
        let si = instance.rpn(labels).to_string();
        let (v, is) = worked(b, &instance, labels)?;
        let complex = b.ap(
            "eqeltrri",
            &binds! {"A" => spelt(&v), "B" => &si, "C" => "cc"},
            &[&eqcom(b, &is, &si, &spelt(&v)), &cc_of(b, &v)],
        );
        let integer = b.ap("nn0zi", &binds! {"N" => &sf}, &[&nn0_of(b, from)]);
        let law = b.ap(
            "fprod1",
            &binds! {"k" => &kv, "M" => &sf, "A" => &sbody, "B" => &si},
            &[&at_index(b, body, k, &at, labels)?],
        );
        let alone = b.ap(
            "mp2an",
            &binds! {
                "ph" => t!(&sf, "cz", "wcel"), "ps" => t!(&si, "cc", "wcel"),
                "ch" => t!(product(&sf), &si, "wceq"),
            },
            &[&integer, &complex, &law],
        );
        return Some((
            v.clone(),
            chain(b, &alone, &is, &product(&sf), &si, &spelt(&v)),
        ));
    }
    let less = to - 1u32;
    let sl = spelt(&less);
    let next = op(&sl, digit(1), ADD);
    let next_term = Term::apply(
        "co",
        vec![
            numeral_term(&less),
            Term::apply(digit(1), Vec::new()),
            Term::apply(ADD, Vec::new()),
        ],
    );
    let instance = put(body, k, &next_term);
    let si = instance.rpn(labels).to_string();
    let truth = "wtru";
    // less is in the integers from `from` up.
    let real_from = re(b, from.clone());
    let real_less = re(b, less.clone());
    let ordered = if *from == less {
        b.ap("leidi", &binds! {"A" => &sf}, &[&real_from])
    } else {
        let law = b.ap(
            "ltlei",
            &binds! {"A" => &sf, "B" => &sl},
            &[&real_from, &real_less],
        );
        b.ap(
            "ax-mp",
            &binds! {"ph" => t!(&sf, &sl, "clt", "wbr"), "ps" => t!(&sf, &sl, "cle", "wbr")},
            &[&below_of(b, from, &less), &law],
        )
    };
    let upper = t!(&sf, "cuz", "cfv");
    let reaches = b.ap(
        "mpbir3an",
        &binds! {
            "ph" => t!(&sl, &upper, "wcel"),
            "ps" => t!(&sf, "cz", "wcel"), "ch" => t!(&sl, "cz", "wcel"),
            "th" => t!(&sf, &sl, "cle", "wbr"),
        },
        &[
            &b.ap("nn0zi", &binds! {"N" => &sf}, &[&nn0_of(b, from)]),
            &b.ap("nn0zi", &binds! {"N" => &sl}, &[&nn0_of(b, &less)]),
            &ordered,
            &b.ap("eluz2", &binds! {"M" => &sf, "N" => &sl}, &[]),
        ],
    );
    let reaches = b.ap(
        "a1i",
        &binds! {"ph" => t!(&sl, &upper, "wcel"), "ps" => truth},
        &[&reaches],
    );
    // Every factor is a complex number, from k's being an integer.
    let within = t!(&kv, "cv", op(&sf, &next, "cfz"), "wcel");
    let context = t!(truth, &within, "wa");
    let integer_k = b.ap(
        "syl",
        &binds! {"ph" => &context, "ps" => &within, "ch" => t!(&kv, "cv", "cz", "wcel")},
        &[
            &b.ap("simpr", &binds! {"ph" => truth, "ps" => &within}, &[]),
            &b.ap("elfzelz", &binds! {"K" => t!(&kv, "cv"), "M" => &sf, "N" => &next}, &[]),
        ],
    );
    let complex_k = b.ap(
        "zcnd",
        &binds! {"ph" => &context, "A" => t!(&kv, "cv")},
        &[&integer_k],
    );
    let factors = complex_in(b, &context, body, k, &complex_k, labels)?;
    let split = b.ap(
        "fprodp1",
        &binds! {"ph" => truth, "k" => &kv, "M" => &sf, "N" => &sl, "A" => &sbody, "B" => &si},
        &[&reaches, &factors, &at_index(b, body, k, &next_term, labels)?],
    );
    let split_said = t!(product(&next), t!(product(&sl), &si, MUL, "co"), "wceq");
    let split = b.ap("mptru", &binds! {"ph" => &split_said}, &[&split]);
    // ( less + 1 ) is `to`, so the range is the one written.
    let st = spelt(to);
    let ends = b.ap(
        "oveq2i",
        &binds! {"A" => &next, "B" => &st, "C" => &sf, "F" => "cfz"},
        &[&sum_of(b, &less, &BigUint::one())],
    );
    let same_range = b.ap(
        "prodeq1i",
        &binds! {"k" => &kv, "A" => op(&sf, &next, "cfz"), "B" => op(&sf, &st, "cfz"), "C" => &sbody},
        &[&ends],
    );
    let peeled_said = t!(product(&sl), &si, MUL, "co");
    let peeled = b.ap(
        "eqtr3i",
        &binds! {"A" => product(&next), "B" => product(&st), "C" => &peeled_said},
        &[&same_range, &split],
    );
    let (rest, rest_is) = product_up_to(b, body, k, from, &less, labels)?;
    let (last, last_is) = worked(b, &instance, labels)?;
    let (sr, sla) = (spelt(&rest), spelt(&last));
    let valued = b.ap(
        "oveq12i",
        &binds! {"A" => product(&sl), "B" => &sr, "C" => &si, "D" => &sla, "F" => MUL},
        &[&rest_is, &last_is],
    );
    let whole = &rest * &last;
    let times = chain(
        b,
        &valued,
        &product_of(b, &rest, &last),
        &peeled_said,
        &op(&sr, &sla, MUL),
        &spelt(&whole),
    );
    Some((
        whole.clone(),
        chain(
            b,
            &peeled,
            &times,
            &product(&st),
            &peeled_said,
            &spelt(&whole),
        ),
    ))
}

/// |- b = a from |- a = b.
fn eqcom(b: &Builder, held: &Proof, a: &str, c: &str) -> Proof {
    b.ap("eqcomi", &binds! {"A" => a, "B" => c}, &[held])
}

/// |- d < ; 1 0, for a digit.
fn below_ten(b: &Builder, d: u32) -> Proof {
    if d == 0 {
        return pos_of(b, &BigUint::from(10u32));
    }
    b.step(&format!("{d}lt10"))
}

/// |- a < c, for a below c: by the digits before the last where they
/// differ (`decltc`), and by the last digits where they do not (`declt`).
pub fn below(b: &Builder, a: impl Into<BigUint>, c: impl Into<BigUint>) -> Proof {
    below_of(b, &a.into(), &c.into())
}

fn below_of(b: &Builder, a: &BigUint, c: &BigUint) -> Proof {
    assert!(a < c, "{a} is not below {c}");
    if a.is_zero() {
        return pos_of(b, c);
    }
    if let (Some(da), Some(dc)) = (one_digit(a), one_digit(c)) {
        return b.step(&format!("{da}lt{dc}"));
    }
    let (cu, cl) = last_off(c);
    if let Some(da) = one_digit(a) {
        return b.ap(
            "declti",
            &binds! {"A" => spelt(&cu), "B" => digit(cl), "C" => digit(da)},
            &[
                &nn_of(b, &cu),
                &nn0_of(b, &BigUint::from(cl)),
                &nn0_of(b, a),
                &below_ten(b, da),
            ],
        );
    }
    let (au, al) = last_off(a);
    if au == cu {
        return b.ap(
            "declt",
            &binds! {"A" => spelt(&au), "B" => digit(al), "C" => digit(cl)},
            &[
                &nn0_of(b, &au),
                &nn0_of(b, &BigUint::from(al)),
                &nn_of(b, &BigUint::from(cl)),
                &below_of(b, &BigUint::from(al), &BigUint::from(cl)),
            ],
        );
    }
    b.ap(
        "decltc",
        &binds! {"A" => spelt(&au), "B" => spelt(&cu), "C" => digit(al), "D" => digit(cl)},
        &[
            &nn0_of(b, &au),
            &nn0_of(b, &cu),
            &nn0_of(b, &BigUint::from(al)),
            &nn0_of(b, &BigUint::from(cl)),
            &below_ten(b, al),
            &below_of(b, &au, &cu),
        ],
    )
}
