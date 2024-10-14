use naga::valid::{Capabilities, ValidationFlags};

use crate::snapshots::Input;

fn do_shader_test(subdir: Option<&str>, path: &str, extension: &str) {
    let input = Input::new(subdir, path, extension);
    let source = input.read_source();
    let mut parser = naga::front::wgsl::Frontend::new();
    let module = parser.parse(&source).unwrap();

    let mut validator = naga::valid::Validator::new(ValidationFlags::all(), Capabilities::all());

    let module_info = validator.validate(&module).unwrap();

    let mut bounds_checker = naga::bounds::BoundsChecker::new();

    let res = bounds_checker.abc_impl(&module, &module_info);

    if let Err(e) = &res {
        println!("Error: {:?}", e);
    }

    bounds_checker.helper.write_to_stream(&mut std::io::stdout()).unwrap();
    assert!(res.is_ok());
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