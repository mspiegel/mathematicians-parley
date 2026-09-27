// A route's answer handed straight to something that wants what the route
// builds.
use parley::Route;

fn fitted() -> Route<String> {
    Route::no("does not fit")
}

fn join(proof: String) -> String {
    proof
}

fn main() {
    let _ = join(fitted());
}
