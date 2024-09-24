use naga::valid::{Capabilities, ValidationFlags};

use crate::snapshots::Input;

#[test]
fn test_bounds_checker_simple() {
    let input = Input::new(Some("abc"), "shader_17", "wgsl");
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

    // bounds_checker.helper.write_to_stream(&mut std::io::stdout()).unwrap();
    assert!(res.is_ok());
}
