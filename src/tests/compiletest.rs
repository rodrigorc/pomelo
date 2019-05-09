use std::path::PathBuf;

#[test]
fn compile_test() {
    let mut config = compiletest_rs::Config::default();
    config.mode = compiletest_rs::common::CompileFail;
    config.src_base = PathBuf::from("src/tests/compile-fail");
    config.target_rustcflags = Some("-L target/debug/deps".to_string());
    config.clean_rmeta();

    compiletest_rs::run_tests(&config);
}
