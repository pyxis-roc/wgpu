use std::io::Write;

use crate::snapshots::Input;
use abc_helper::{ConstraintId, IntervalKind};
use naga::bounds::{AddressSpacesToCheck, BoundsCheckResult, report_to_json};
use naga::valid::{Capabilities, ValidationFlags};
use naga::FastHashMap;

fn init_logging() {
    env_logger::builder()
        .is_test(true)
        .filter_level(log::LevelFilter::Trace)
        .try_init()
        .unwrap();
}


fn do_bounds_check_test(source: &str, idx: u32) -> FastHashMap<u32, Vec<IntervalKind>> {
    let mut parser = naga::front::wgsl::Frontend::new();
    let module = parser.parse(&source).unwrap();

    let mut validator = naga::valid::Validator::new(ValidationFlags::all(), Capabilities::all());

    let module_info = validator.validate(&module).unwrap();

    let config = AddressSpacesToCheck::all();
    let mut bounds_checker = naga::bounds::BoundsChecker::new(config);

    bounds_checker
        .abc_impl(&module, &module_info)
        .expect("Bounds check failed");

    bounds_checker
        .helper
        .solve(idx)
        .expect("Bounds check failed")
}

fn do_bounds_report(source: &str) -> Vec<BoundsCheckResult> {
    let mut parser = naga::front::wgsl::Frontend::new();
    let module = parser.parse(&source).unwrap();

    let mut validator = naga::valid::Validator::new(ValidationFlags::all(), Capabilities::all());

    let module_info = validator.validate(&module).unwrap();

    let config = AddressSpacesToCheck::all();
    let mut bounds_checker = naga::bounds::BoundsChecker::new(config);

    bounds_checker
        .abc_impl(&module, &module_info)
        .expect("Bounds check failed");

    bounds_checker.make_report().expect("Bounds check failed")
}

fn do_shader_test(subdir: Option<&str>, path: &str, extension: &str) {
    let input = Input::new(subdir, path, extension);
    let source = input.read_source();
    let mut parser = naga::front::wgsl::Frontend::new();
    let module = parser.parse(&source).unwrap();

    let mut validator = naga::valid::Validator::new(ValidationFlags::all(), Capabilities::all());

    let module_info = validator.validate(&module).unwrap();

    let config = AddressSpacesToCheck::all();
    let mut bounds_checker = naga::bounds::BoundsChecker::new(config);

    let res = bounds_checker.abc_impl(&module, &module_info);

    if let Err(e) = &res {
        println!("Error: {:?}", e);
    }

    bounds_checker
        .helper
        .write_to_stream(&mut std::io::stdout())
        .unwrap();
    res.expect("Bounds check failed");
}

///
#[test]
fn test_shader_1() {
    do_shader_test(Some("abc"), "shader_1", "wgsl");
}

/// # Features tested:
/// - Splat expression
#[test]
fn test_shader_3() {
    do_shader_test(Some("abc"), "shader_3", "wgsl");
}

/// # Features tested:
/// - As expression i32(...)
/// - For loop
#[test]
fn test_concatenate10() {
    do_shader_test(Some("abc"), "concatenate10_kernel", "wgsl");
}

#[test]
fn test_shader_17() {
    do_shader_test(Some("abc"), "shader_17", "wgsl");
}

#[test]
fn test_global_var_initializer() {
    do_shader_test(Some("abc"), "global_var_initializer", "wgsl");
}

#[test]
fn test_complex_structs() {
    do_shader_test(Some("abc"), "complex_structs", "wgsl");
}

#[test]
fn test_complex_structs2() {
    do_shader_test(Some("abc"), "complex_structs2", "wgsl");
}

#[test]
fn test_if_else() {
    do_shader_test(Some("abc"), "if_else", "wgsl");
}

#[test]
fn test_simple_alias() {
    do_shader_test(Some("abc"), "simple_alias", "wgsl");
}

#[test]
fn test_simple_loop() {
    do_shader_test(Some("abc"), "simple_loop", "wgsl");
}

#[test]
fn test_unsupported_ignored() {
    do_shader_test(Some("abc"), "unsupported_ignored", "wgsl");
}

#[test]
fn test_hello_bounds_elimination() {
    init_logging();
    let input = Input::new(Some("abc"), "hello_bounds_elimination", "wgsl");
    let res = do_bounds_check_test(&input.read_source(), 0);
    for solution in res.values() {
        for subinterval in solution {
            assert_eq!(subinterval, &IntervalKind::from(true));
        }
    }
}

#[test]
fn test_concatenate10_elimination() {
    init_logging();
    let input = Input::new(Some("abc"), "concatenate10_kernel", "wgsl");
    do_bounds_check_test(&input.read_source(), 0);
}

#[test]
fn test_shader_17_elimination() {
    // init_logging();

    let input = Input::new(Some("abc"), "shader_17", "wgsl");
    let source = input.read_source();

    let res = do_bounds_report(&source);


    let res = report_to_json(&res, &source);
    std::io::stdout().write_all(res.as_bytes()).unwrap();
    std::io::stdout().flush().unwrap();
}
