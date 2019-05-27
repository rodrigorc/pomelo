use std::path::PathBuf;

#[test]
#[ignore]
fn compile_test() {
    let mut config = compiletest_rs::Config::default();
    config.mode = compiletest_rs::common::CompileFail;
    config.src_base = PathBuf::from("tests/compile-fail");
    config.link_deps();
    //config.clean_rmeta();

    compiletest_rs::run_tests(&config);
}
