// The ways of asking that are right, which must compile: a match that takes
// the built value out, a decline handed up unchanged, the next route tried
// only after a decline, and several routes asked in turn before any is used.
use parley::{Built, Declined, Route};

fn fitted(x: u32) -> Route<String> {
    if x > 0 {
        return Route::no("does not fit");
    }
    Route::Built(x.to_string())
}

fn join(proof: String) -> String {
    proof
}

fn asked_before_used() -> Route<String> {
    match fitted(1) {
        Built(made) => Built(join(made)),
        Declined(why) => Declined(why),
    }
}

fn asked_in_turn() -> Route<String> {
    let a = match fitted(1) {
        Built(a) => a,
        Declined(why) => return Declined(why),
    };
    let b = match fitted(2) {
        Built(b) => b,
        Declined(why) => return Declined(why),
    };
    Built(join(a + &b))
}

fn one_route_then_another() -> Route<String> {
    fitted(1).or_try(|| fitted(0)).map(join)
}

fn main() {
    let _ = asked_before_used();
    let _ = asked_in_turn();
    let _ = one_route_then_another();
}
