// A route's answer written into text by a format, as though it were a term.
use parley::Route;

fn fitted() -> Route<String> {
    Route::no("does not fit")
}

fn main() {
    let _ = format!("{} cv", fitted());
}
