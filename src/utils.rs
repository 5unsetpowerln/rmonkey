use anyhow::Error;

pub fn print_errors(msg: &str, err: Error) {
    println!("{msg}: {err}");

    let mut current = err.source();

    while let Some(s) = current {
        println!("<- {s}");
        current = s.source();
    }
}
