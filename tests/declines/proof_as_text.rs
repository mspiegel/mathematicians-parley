// A proof handed where the builder joins text. A term built from a proof
// would carry nothing of what the proof rests on, and `eqid` takes a class,
// which a proof is not.
use parley::mm::{Builder, Signatures};

fn main() {
    let b = Builder::new(Signatures::new());
    let proof = b.ap("0re", &[], &[]);
    let _ = b.term(&[&proof, "eqid"]);
}
