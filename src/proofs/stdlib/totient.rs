//! Euler's φ, congruences, and products over a finite set, for `proved.mm`.
//!
//! Euler's theorem is proved by the rearrangement argument: multiplying each
//! remainder coprime to n by a, and reducing, permutes those remainders, so
//! the product of all of them is the same before and after, and a^φ(n)
//! cancels from it. set.mm proves the theorem itself (`eulerth`) by the
//! same argument over a sequence; the readable layer takes it a step at a
//! time, and the items its steps cite are set.mm's lemmas restated, each in
//! the shape its record states it:
//!
//! - φ(n) counts the remainders 0, …, n − 1 coprime to n: `dfphi2`, with
//!   `fzoval` reading 0 ..^ n as 0 ... n − 1;
//! - two numbers coprime to n have a product coprime to n: `rpmul`, which
//!   puts n first in each gcd;
//! - a number dividing a product and coprime to one factor divides the
//!   other: `coprmdvds`, with the factors the other way round;
//! - a common factor coprime to n cancels from a congruence: `subdir`
//!   writes x·c − y·c as (x − y)·c, and then the line above;
//! - equal remainders are a congruence, and a number is congruent to its
//!   remainder: `moddvds`, the second with `modabs2`;
//! - two remainders that are congruent are equal: `fzocongeq`;
//! - a remainder lies in 0 … n − 1: `elfzo0`;
//! - a product over a finite set of integers is an integer (`fprodzcl`),
//!   loses a common factor once per term (`fprodmul`, `fprodconst`), is
//!   unchanged by a one-to-one map of the set to itself (`f1finf1o`,
//!   `fprodf1o`), and is congruent to another taken term by term
//!   (`fprodmodd`);
//! - a product of numbers coprime to n is coprime to n. set.mm states this
//!   only of factors coprime to each other as well (`coprmprod`), so it is
//!   proved here by induction on the finite set (`findcard2d`), a factor at
//!   a time (`fprodsplitsn`).

use super::parallels::{statement, Prover, Said};
use crate::mm::Builder;
use crate::proofs::Lemma;

pub const HEAD: &str =
    "$( Totient: Euler's phi, congruences, and products over a finite set. $)
$( A product binds k, and a step of the induction binds w, y and z, apart
   from the set, the factor and the modulus; the \"for all\" binds x, and
   renaming a product's letter binds n. The bound letters are held apart
   from each other and from the classes, and the classes not from each
   other: a lemma about A and N says nothing of A and N sharing a letter. $)
$d k n x y z w $.
$d k A $.  $d k C $.  $d k F $.  $d k N $.  $d k X $.
$d n A $.  $d n C $.  $d n F $.  $d n N $.  $d n X $.
$d x A $.  $d x C $.  $d x F $.  $d x N $.  $d x X $.
$d y A $.  $d y C $.  $d y F $.  $d y N $.  $d y X $.
$d z A $.  $d z C $.  $d z F $.  $d z N $.  $d z X $.
$d w A $.  $d w C $.  $d w F $.  $d w N $.  $d w X $.
";

pub fn proofs(b: &mut Builder) -> Vec<Lemma> {
    let p = Prover { b };
    vec![
        phi_value(&p),
        coprime_product_lemma(&p),
        remainder_in_range(&p),
        equal_remainders(&p),
        coprime_divides_lemma(&p),
        congruent_cancel(&p),
        congruent_in_range(&p),
        congruent_to_remainder(&p),
        product_integer(&p),
        product_factor(&p),
        product_reorder(&p),
        product_congruent(&p),
        product_coprime(&p),
    ]
}

fn lemma(p: &Prover, label: &str, said: Said) -> Lemma {
    Lemma::new(label, statement(p, &said), said.proof)
}

/// The lemma under the conjunction of `conjuncts`, curried, having checked
/// it proves `text`.
fn finish(
    p: &Prover,
    label: &str,
    said: Said,
    conjuncts: &[&str],
    text: &str,
) -> Lemma {
    lemma(p, label, p.is(p.curried(said, conjuncts), text))
}

/// ( g -> ( A x. B ) gcd N = 1 ) from A and B in ZZ, N in ZZ, and each of
/// ( A gcd N ) and ( B gcd N ) 1: `rpmul` asks n first in each gcd.
fn coprime_product(
    p: &Prover,
    a: &Said,
    b: &Said,
    nz: &Said,
    ca: &Said,
    cb: &Said,
) -> Said {
    let na = p.by("eqtr3d", &[&p.apply("gcdcom", &[a, nz], &[]), ca], &[]);
    let nb = p.by("eqtr3d", &[&p.apply("gcdcom", &[b, nz], &[]), cb], &[]);
    let both = p.by("jca", &[&na, &nb], &[]);
    let n_first = p.by("mpd", &[&both, &p.apply("rpmul", &[nz, a, b], &[])], &[]);
    let product = p.apply("zmulcl", &[a, b], &[]);
    p.by(
        "eqtrd",
        &[&p.apply("gcdcom", &[&product, nz], &[]), &n_first],
        &[],
    )
}

/// ( g -> N || A ) from N dividing ( A x. C ) with ( C gcd N ) 1:
/// `coprmdvds` has the coprime factor first and n first in the gcd.
fn coprime_divides(
    p: &Prover,
    a: &Said,
    c: &Said,
    nz: &Said,
    divides: &Said,
    coprime: &Said,
) -> Said {
    let turned = p.apply(
        "mulcom",
        &[&p.apply("zcn", &[a], &[]), &p.apply("zcn", &[c], &[])],
        &[],
    );
    let divides = p.by("breqtrd", &[divides, &turned], &[]);
    let n_first = p.by("eqtrd", &[&p.apply("gcdcom", &[nz, c], &[]), coprime], &[]);
    let both = p.by("jca", &[&divides, &n_first], &[]);
    p.by(
        "mpd",
        &[&both, &p.apply("coprmdvds", &[nz, c, a], &[])],
        &[],
    )
}

/// ( N e. NN -> ( phi ` N ) = ( # ` { x e. ( 0 ... ( N - 1 ) ) | ( x gcd N ) = 1 } ) )
fn phi_value(p: &Prover) -> Lemma {
    let counted = p.by("dfphi2", &[], &[("N", "N"), ("x", "x")]);
    let integer = p.by("nnz", &[], &[("N", "N")]);
    let range = p.by(
        "syl",
        &[&integer, &p.by("fzoval", &[], &[("M", "0"), ("N", "N")])],
        &[],
    );
    let same_set = p.by(
        "rabeqdv",
        &[&range],
        &[("x", "x"), ("ps", "( x gcd N ) = 1")],
    );
    let same_count = p.by("fveq2d", &[&same_set], &[("F", "#")]);
    let said = p.is(
        p.by("eqtrd", &[&counted, &same_count], &[]),
        "( N e. NN -> ( phi ` N ) = ( # ` { x e. ( 0 ... ( N - 1 ) ) | ( x gcd N ) = 1 } ) )",
    );
    lemma(p, "gphival", said)
}

/// A, B coprime to N, so their product is: `coprime-product`.
fn coprime_product_lemma(p: &Prover) -> Lemma {
    let conj = [
        "A e. ZZ",
        "B e. ZZ",
        "N e. NN",
        "( A gcd N ) = 1",
        "( B gcd N ) = 1",
    ];
    let [a, b, nn, ca, cb] = parts::<5>(p, &conj);
    let nz = p.apply("nnz", &[&nn], &[]);
    let said = coprime_product(p, &a, &b, &nz, &ca, &cb);
    finish(
        p,
        "grpmul",
        said,
        &conj,
        "( A e. ZZ -> ( B e. ZZ -> ( N e. NN -> ( ( A gcd N ) = 1 -> ( ( B gcd N ) = 1 -> ( ( A x. B ) gcd N ) = 1 ) ) ) ) )",
    )
}

/// A whole number below M is one of 0, …, M − 1: `range-from-bounds`.
fn remainder_in_range(p: &Prover) -> Lemma {
    let conj = ["M e. NN", "A e. NN0", "A < M"];
    let [m, a, below] = parts::<3>(p, &conj);
    let three = p.by("3jca", &[&a, &m, &below], &[]);
    let half_open = p.by(
        "sylibr",
        &[&three, &p.by("elfzo0", &[], &[("A", "A"), ("B", "M")])],
        &[],
    );
    let closed = p.apply("fzoval", &[&p.apply("nnz", &[&m], &[])], &[("M", "0")]);
    let said = p.by("eleqtrd", &[&half_open, &closed], &[]);
    finish(
        p,
        "gelfz0m1",
        said,
        &conj,
        "( M e. NN -> ( A e. NN0 -> ( A < M -> A e. ( 0 ... ( M - 1 ) ) ) ) )",
    )
}

/// Equal remainders on dividing by N are a congruence: `mod-equal-congruent`.
fn equal_remainders(p: &Prover) -> Lemma {
    let conj = ["A e. ZZ", "B e. ZZ", "N e. NN", "( A mod N ) = ( B mod N )"];
    let [a, b, nn, equal] = parts::<4>(p, &conj);
    let said = p.by(
        "mpbid",
        &[&equal, &p.apply("moddvds", &[&nn, &a, &b], &[])],
        &[],
    );
    finish(
        p,
        "gmodeqdvds",
        said,
        &conj,
        "( A e. ZZ -> ( B e. ZZ -> ( N e. NN -> ( ( A mod N ) = ( B mod N ) -> N || ( A - B ) ) ) ) )",
    )
}

/// N dividing A·C, coprime to C, divides A: `coprime-divides`.
fn coprime_divides_lemma(p: &Prover) -> Lemma {
    let conj = [
        "A e. ZZ",
        "C e. ZZ",
        "N e. NN",
        "N || ( A x. C )",
        "( C gcd N ) = 1",
    ];
    let [a, c, nn, divides, coprime] = parts::<5>(p, &conj);
    let nz = p.apply("nnz", &[&nn], &[]);
    let said = coprime_divides(p, &a, &c, &nz, &divides, &coprime);
    finish(
        p,
        "gcoprmdvds",
        said,
        &conj,
        "( A e. ZZ -> ( C e. ZZ -> ( N e. NN -> ( N || ( A x. C ) -> ( ( C gcd N ) = 1 -> N || A ) ) ) ) )",
    )
}

/// A factor coprime to N cancels from a congruence: `congruent-cancel`.
fn congruent_cancel(p: &Prover) -> Lemma {
    let conj = [
        "A e. ZZ",
        "B e. ZZ",
        "C e. ZZ",
        "N e. NN",
        "N || ( ( A x. C ) - ( B x. C ) )",
        "( C gcd N ) = 1",
    ];
    let [a, b, c, nn, divides, coprime] = parts::<6>(p, &conj);
    let nz = p.apply("nnz", &[&nn], &[]);
    let complex = |z: &Said| p.apply("zcn", &[z], &[]);
    let factored = p.apply("subdir", &[&complex(&a), &complex(&b), &complex(&c)], &[]);
    let divides = p.by("breqtrrd", &[&divides, &factored], &[]);
    let difference = p.apply("zsubcl", &[&a, &b], &[]);
    let said = coprime_divides(p, &difference, &c, &nz, &divides, &coprime);
    finish(
        p,
        "gcongrcan",
        said,
        &conj,
        "( A e. ZZ -> ( B e. ZZ -> ( C e. ZZ -> ( N e. NN -> ( N || ( ( A x. C ) - ( B x. C ) ) -> ( ( C gcd N ) = 1 -> N || ( A - B ) ) ) ) ) ) )",
    )
}

/// Two of 0, …, N − 1 congruent modulo N are equal: `congruent-in-range`.
fn congruent_in_range(p: &Prover) -> Lemma {
    let conj = [
        "N e. NN",
        "A e. ( 0 ... ( N - 1 ) )",
        "B e. ( 0 ... ( N - 1 ) )",
        "N || ( A - B )",
    ];
    let [nn, a, b, divides] = parts::<4>(p, &conj);
    let closed = p.apply("fzoval", &[&p.apply("nnz", &[&nn], &[])], &[("M", "0")]);
    let a_open = p.by("eleqtrrd", &[&a, &closed], &[]);
    let b_open = p.by("eleqtrrd", &[&b, &closed], &[]);
    let rule = p.apply("fzocongeq", &[&a_open, &b_open], &[]);
    let less_nothing = p.apply("subid1", &[&p.apply("nncn", &[&nn], &[])], &[]);
    let divides = p.by("eqbrtrd", &[&less_nothing, &divides], &[]);
    let said = p.by("mpbid", &[&divides, &rule], &[]);
    finish(
        p,
        "gfzocong0",
        said,
        &conj,
        "( N e. NN -> ( A e. ( 0 ... ( N - 1 ) ) -> ( B e. ( 0 ... ( N - 1 ) ) -> ( N || ( A - B ) -> A = B ) ) ) )",
    )
}

/// A number is congruent to its remainder: `mod-congruent`.
fn congruent_to_remainder(p: &Prover) -> Lemma {
    let conj = ["A e. ZZ", "N e. NN"];
    let [a, nn] = parts::<2>(p, &conj);
    let remainder = p.apply("nn0z", &[&p.apply("zmodcl", &[&a, &nn], &[])], &[]);
    let again = p.apply(
        "modabs2",
        &[&p.apply("zre", &[&a], &[]), &p.apply("nnrp", &[&nn], &[])],
        &[],
    );
    let again = p.by("eqcomd", &[&again], &[]);
    let rule = p.apply("moddvds", &[&nn, &a, &remainder], &[]);
    let said = p.by("mpbid", &[&again, &rule], &[]);
    finish(
        p,
        "gmodcong",
        said,
        &conj,
        "( A e. ZZ -> ( N e. NN -> N || ( A - ( A mod N ) ) ) )",
    )
}

/// ( ( g /\ k e. X ) -> k e. ZZ ), from ( g -> X e. ~P ZZ ).
fn member_integer(p: &Prover, power: &Said) -> Said {
    p.by("sselda", &[&p.apply("elpwi", &[power], &[])], &[("C", "k")])
}

/// A product of integers over a finite set is an integer: `product-integer`.
fn product_integer(p: &Prover) -> Lemma {
    let conj = ["X e. ~P ZZ", "X e. Fin"];
    let [power, finite] = parts::<2>(p, &conj);
    let said = p.by("fprodzcl", &[&finite, &member_integer(p, &power)], &[]);
    finish(
        p,
        "gfprodz",
        said,
        &conj,
        "( X e. ~P ZZ -> ( X e. Fin -> prod_ k e. X k e. ZZ ) )",
    )
}

/// A factor common to every term comes out once per term: `product-factor`.
fn product_factor(p: &Prover) -> Lemma {
    let conj = ["X e. ~P ZZ", "X e. Fin", "C e. ZZ"];
    let [power, finite, c] = parts::<3>(p, &conj);
    let k_complex = p.by("zcnd", &[&member_integer(p, &power)], &[]);
    let c_complex = p.by("zcnd", &[&c], &[]);
    let c_at_k = p.lift(&c_complex, "k e. X");
    let split = p.by("fprodmul", &[&finite, &k_complex, &c_at_k], &[]);
    let constant = p.apply("fprodconst", &[&finite, &c_complex], &[("k", "k")]);
    let constant = p.by(
        "oveq2d",
        &[&constant],
        &[("C", "prod_ k e. X k"), ("F", "x.")],
    );
    let product = p.by("fprodcl", &[&finite, &k_complex], &[]);
    let power_of_c = p.apply(
        "expcl",
        &[&c_complex, &p.apply("hashcl", &[&finite], &[])],
        &[],
    );
    let turned = p.apply("mulcom", &[&product, &power_of_c], &[]);
    let said = p.by(
        "eqtrd",
        &[&split, &p.by("eqtrd", &[&constant, &turned], &[])],
        &[],
    );
    finish(
        p,
        "gfprodmulc",
        said,
        &conj,
        "( X e. ~P ZZ -> ( X e. Fin -> ( C e. ZZ -> prod_ k e. X ( k x. C ) = ( ( C ^ ( # ` X ) ) x. prod_ k e. X k ) ) ) )",
    )
}

/// A one-to-one map of a finite set to itself leaves the product of its
/// members as it was: `product-reorder`.
fn product_reorder(p: &Prover) -> Lemma {
    let conj = [
        "X e. ~P ZZ",
        "X e. Fin",
        "( F : X --> X /\\ F : X -1-1-> X )",
    ];
    let [power, finite, map] = parts::<3>(p, &conj);
    let g = Prover::conjoined(&conj);
    let one_to_one = p.by("simprd", &[&map], &[]);
    let paired = p.apply("enrefg", &[&finite], &[]);
    let rule = p.apply("f1finf1o", &[&paired, &finite], &[("F", "F")]);
    let onto = p.by("mpbid", &[&one_to_one, &rule], &[]);
    let term = p.by("id", &[], &[("ph", "k = ( F ` n )")]);
    let value = p.by(
        "eqidd",
        &[],
        &[("ph", &format!("( {g} /\\ n e. X )")), ("A", "( F ` n )")],
    );
    let k_complex = p.by("zcnd", &[&member_integer(p, &power)], &[]);
    let moved = p.by(
        "fprodf1o",
        &[&term, &finite, &onto, &value, &k_complex],
        &[("D", "( F ` n )")],
    );
    let letter = p.by("fveq2", &[], &[("A", "n"), ("B", "k"), ("F", "F")]);
    let renamed = p.by(
        "cbvprodv",
        &[&letter],
        &[("j", "n"), ("k", "k"), ("A", "X")],
    );
    let said = p.by("eqtrd", &[&moved, &p.always(&renamed, &g)], &[]);
    let said = p.by("eqcomd", &[&said], &[]);
    finish(
        p,
        "gfprodf1",
        said,
        &conj,
        "( X e. ~P ZZ -> ( X e. Fin -> ( ( F : X --> X /\\ F : X -1-1-> X ) -> prod_ k e. X ( F ` k ) = prod_ k e. X k ) ) )",
    )
}

/// Products congruent term by term are congruent: `product-congruent`.
fn product_congruent(p: &Prover) -> Lemma {
    let conj = [
        "X e. ~P ZZ",
        "X e. Fin",
        "C e. ZZ",
        "N e. NN",
        "F : X --> X",
        "A. x e. X N || ( ( x x. C ) - ( F ` x ) )",
    ];
    let [power, finite, c, nn, map, each] = parts::<6>(p, &conj);
    let g = Prover::conjoined(&conj);
    let k_in = p.by("simpr", &[], &[("ph", &g), ("ps", "k e. X")]);
    let k_integer = member_integer(p, &power);
    let term = p.apply("zmulcl", &[&k_integer, &p.lift(&c, "k e. X")], &[]);
    let image = p.by("ffvelcdmd", &[&p.lift(&map, "k e. X"), &k_in], &[]);
    let within = p.lift(&p.apply("elpwi", &[&power], &[]), "k e. X");
    let image = p.by("sseldd", &[&within, &image], &[]);
    let left = p.by(
        "oveq1",
        &[],
        &[("A", "x"), ("B", "k"), ("C", "C"), ("F", "x.")],
    );
    let right = p.by("fveq2", &[], &[("A", "x"), ("B", "k"), ("F", "F")]);
    let both = p.by("oveq12d", &[&left, &right], &[("F", "-")]);
    let read = p.by("breq2d", &[&both], &[("C", "N"), ("R", "||")]);
    let at_k = p.by("rspcdva", &[&read, &p.lift(&each, "k e. X"), &k_in], &[]);
    let nn_at_k = p.lift(&nn, "k e. X");
    let rule = p.apply("moddvds", &[&nn_at_k, &term, &image], &[]);
    let same_remainder = p.by("mpbird", &[&at_k, &rule], &[]);
    let products = p.by(
        "fprodmodd",
        &[&finite, &term, &image, &nn, &same_remainder],
        &[],
    );
    let first = p.by("fprodzcl", &[&finite, &term], &[]);
    let second = p.by("fprodzcl", &[&finite, &image], &[]);
    let rule = p.apply("moddvds", &[&nn, &first, &second], &[]);
    let said = p.by("mpbid", &[&products, &rule], &[]);
    finish(
        p,
        "gfprodcong",
        said,
        &conj,
        "( X e. ~P ZZ -> ( X e. Fin -> ( C e. ZZ -> ( N e. NN -> ( F : X --> X -> ( A. x e. X N || ( ( x x. C ) - ( F ` x ) ) -> N || ( prod_ k e. X ( k x. C ) - prod_ k e. X ( F ` k ) ) ) ) ) ) ) )",
    )
}

/// A product of numbers coprime to N is coprime to N: `product-coprime`, by
/// induction on the finite set, a factor at a time.
fn product_coprime(p: &Prover) -> Lemma {
    let conj = [
        "X e. ~P ZZ",
        "X e. Fin",
        "N e. NN",
        "A. x e. X ( x gcd N ) = 1",
    ];
    let [power, finite, nn, each] = parts::<4>(p, &conj);
    let g = Prover::conjoined(&conj);
    let nz = p.apply("nnz", &[&nn], &[]);
    let says = |set: &str| format!("( prod_ k e. {set} k gcd N ) = 1");
    // What the induction says of a set w, read at each set it is asked of.
    let at = |set: &str| {
        let same = p.by(
            "prodeq1",
            &[],
            &[("A", "w"), ("B", set), ("C", "k"), ("k", "k")],
        );
        let gcd = p.by("oveq1d", &[&same], &[("C", "N"), ("F", "gcd")]);
        p.by("eqeq1d", &[&gcd], &[("C", "1")])
    };
    // The empty product is 1, and 1 is coprime to anything.
    let empty = p.always(&p.by("prod0", &[], &[("A", "k"), ("k", "k")]), &g);
    let empty = p.by("oveq1d", &[&empty], &[("C", "N"), ("F", "gcd")]);
    let base = p.by("eqtrd", &[&empty, &p.apply("1gcd", &[&nz], &[])], &[]);
    // A set y within X and one more member z of X: the product over both is
    // the product over y times z, and each is coprime to N.
    let step = "( y C_ X /\\ z e. ( X \\ y ) )";
    let h = format!("( {g} /\\ {step} )");
    let lift = |s: &Said| p.lift(s, step);
    let inside = p.by(
        "simprl",
        &[],
        &[("ph", &g), ("ps", "y C_ X"), ("ch", "z e. ( X \\ y )")],
    );
    let new = p.by(
        "simprr",
        &[],
        &[("ph", &g), ("ps", "y C_ X"), ("ch", "z e. ( X \\ y )")],
    );
    let z_in = p.apply("eldifi", &[&new], &[]);
    let z_out = p.apply("eldifn", &[&new], &[]);
    let y_finite = p.apply("ssfi", &[&lift(&finite), &inside], &[]);
    let integers = lift(&p.apply("elpwi", &[&power], &[]));
    let y_integers = p.by("sstrd", &[&inside, &integers], &[]);
    let z_integer = p.by("sseldd", &[&integers, &z_in], &[]);
    let k_integer = p.by("sselda", &[&y_integers], &[("C", "k")]);
    let k_complex = p.by("zcnd", &[&k_integer], &[]);
    let split = p.by(
        "fprodsplitsn",
        &[
            &p.by("nfv", &[], &[("x", "k"), ("ph", &h)]),
            &p.by("nfcv", &[], &[("x", "k"), ("A", "z")]),
            &y_finite,
            &z_integer,
            &z_out,
            &k_complex,
            &p.by("id", &[], &[("ph", "k = z")]),
            &p.by("zcnd", &[&z_integer], &[]),
        ],
        &[],
    );
    let earlier = says("y");
    let held = p.by("simpr", &[], &[("ph", &h), ("ps", &earlier)]);
    let up = |s: &Said| p.lift(s, &earlier);
    let y_product = up(&p.by("fprodzcl", &[&y_finite, &k_integer], &[]));
    let read = p.by(
        "oveq1d",
        &[&p.by("id", &[], &[("ph", "x = z")])],
        &[("C", "N"), ("F", "gcd")],
    );
    let read = p.by("eqeq1d", &[&read], &[("C", "1")]);
    let z_coprime = p.by("rspcdva", &[&read, &lift(&each), &z_in], &[]);
    let both = coprime_product(
        p,
        &y_product,
        &up(&z_integer),
        &up(&lift(&nz)),
        &held,
        &up(&z_coprime),
    );
    let split = p.by("oveq1d", &[&up(&split)], &[("C", "N"), ("F", "gcd")]);
    let grown = p.by("eqtrd", &[&split, &both], &[]);
    let grown = p.by("ex", &[&grown], &[("ph", &h)]);
    let said = p.by(
        "findcard2d",
        &[
            &at("(/)"),
            &at("y"),
            &at("( y u. { z } )"),
            &at("X"),
            &base,
            &grown,
            &finite,
        ],
        &[("x", "w")],
    );
    finish(
        p,
        "gfprodrp",
        said,
        &conj,
        "( X e. ~P ZZ -> ( X e. Fin -> ( N e. NN -> ( A. x e. X ( x gcd N ) = 1 -> ( prod_ k e. X k gcd N ) = 1 ) ) ) )",
    )
}

/// Each conjunct of the antecedent, proved from it, as an array.
fn parts<const N: usize>(p: &Prover, conjuncts: &[&str]) -> [Said; N] {
    p.parts(conjuncts)
        .try_into()
        .unwrap_or_else(|_| panic!("{N} conjuncts expected"))
}
