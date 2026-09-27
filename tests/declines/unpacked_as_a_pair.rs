// A route that builds a pair, its answer unpacked as though it were the pair.
use parley::Route;

fn pair() -> Route<(String, String)> {
    Route::no("does not fit")
}

fn main() {
    let (lemma, _flipped) = pair();
    let _ = lemma;
}
