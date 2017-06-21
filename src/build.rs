extern crate lalrpop;

fn main() {
    lalrpop::Configuration::new()
        .use_colors_if_tty()
        .use_cargo_dir_conventions()
        .process()
        .unwrap();
}
