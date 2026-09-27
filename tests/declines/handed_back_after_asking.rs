// A function that asks whether a route declined and gives the answer back
// either way declines too, and its caller has to ask again.
use parley::Route;

fn fitted() -> Route<String> {
    Route::no("does not fit")
}

fn relayed() -> Route<String> {
    let found = fitted();
    if found.is_declined() {
        return found;
    }
    found
}

fn join(proof: String) -> String {
    proof
}

fn main() {
    let _ = join(relayed());
}
