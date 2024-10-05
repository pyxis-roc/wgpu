struct B {
  a: i32,
  b: i32,
}
struct S {
  a: array<B, 2>,
  b: i32,
}

@group(0) @binding(0) var<storage, read_write> c: array<S, 2>;


@compute @workgroup_size(1, 1, 1)
fn foo() {
  c[0].a[1].b = i32(1);
}
