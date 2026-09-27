// A route that is a method of the same value, written in an impl block in
// another module, its answer reached through `self` and passed on.
pub struct Whole;

mod part {
    use parley::Route;

    impl super::Whole {
        pub fn route(&self, x: u32) -> Route<String> {
            if x > 0 {
                return Route::no("does not apply");
            }
            Route::Built(x.to_string())
        }
    }
}

fn join(proof: String) -> String {
    proof
}

impl Whole {
    fn g(&self) -> String {
        join(self.route(1))
    }
}

fn main() {
    let _ = Whole.g();
}
