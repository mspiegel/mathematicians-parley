// A route that builds several steps, its answer spread into a call that
// takes the steps one by one.
use parley::Route;

fn steps() -> Route<Vec<String>> {
    Route::no("does not fit")
}

fn seq(parts: impl IntoIterator<Item = String>) -> String {
    parts.into_iter().collect::<Vec<_>>().join(" ")
}

fn main() {
    let _ = seq(steps());
}
