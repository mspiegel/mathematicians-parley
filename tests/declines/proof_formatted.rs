// A proof written into text by a format. Its text is `.text()`, asked for
// by name; a proof that became a string by accident would have lost what it
// rests on.
use parley::mm::{Builder, Signatures};

fn main() {
    let b = Builder::new(Signatures::new());
    let proof = b.ap("0re", &[], &[]);
    let _ = format!("{proof}");
}
