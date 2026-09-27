// A route's answer asked whether it declined, and then passed on whole. The
// question does not take the built value out; only a match does, so the
// answer is still a route where a proof is wanted.
use parley::Route;

fn fitted() -> Route<String> {
    Route::no("does not fit")
}

fn join(proof: String) -> String {
    proof
}

fn main() {
    let made = fitted();
    if made.is_declined() {
        return;
    }
    let _ = join(made);
}
