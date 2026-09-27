// A route defined in another module, called on a value that is not the
// caller's own, its answer passed on as though it were a proof.
mod normal {
    use parley::Route;

    pub struct Work;

    impl Work {
        pub fn normalize(&self, _at: u32) -> Route<String> {
            Route::no("does not normalize")
        }
    }
}

fn join(proof: String) -> String {
    proof
}

fn main() {
    let work = normal::Work;
    let _ = join(work.normalize(1));
}
