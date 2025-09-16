use std::path::PathBuf;

#[test]
#[ignore]
fn compile_test() {
    let mut config = compiletest_rs::Config {
        mode: compiletest_rs::common::CompileFail,
        src_base: PathBuf::from("tests/compile-fail"),
        ..Default::default()
    };
    config.link_deps();
    //config.clean_rlib();
    //config.clean_rmeta();

    compiletest_rs::run_tests(&config);
}
