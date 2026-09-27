//! What a tool says: what it printed, what it complained of, and the status
//! it exits with.

#[derive(Clone, Debug, Default)]
pub struct Said {
    pub printed: String,
    pub complained: String,
    pub status: i32,
}

impl Said {
    pub fn green(&self) -> bool {
        self.status == 0
    }
}
