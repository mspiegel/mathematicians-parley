// A route's answer bound to a name, and the name passed on as though it held
// what the route builds.
use parley::Route;

fn fitted() -> Route<String> {
    Route::no("does not fit")
}

fn join(proof: String) -> String {
    proof
}

fn main() {
    let made = fitted();
    let _ = join(made);
}
