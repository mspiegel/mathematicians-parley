// A route's answer stored in a table of facts, where every value is a proof.
use indexmap::IndexMap;
use parley::Route;

fn fitted() -> Route<String> {
    Route::no("does not fit")
}

fn main() {
    let mut facts: IndexMap<&str, String> = IndexMap::new();
    facts.insert("k", fitted());
}
