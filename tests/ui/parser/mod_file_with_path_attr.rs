//@ normalize-stderr: "not_a_real_file.rs`:.*\(" -> "not_a_real_file.rs`: $$FILE_NOT_FOUND_MSG ("

#[path = "not_a_real_file.rs"]
mod m; //~ ERROR couldn't find file

fn main() {
    assert_eq!(m::foo(), 10);
}
