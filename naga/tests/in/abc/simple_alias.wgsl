@group(0) @binding(0) var<storage, read_write> x: i32;

fn foo() -> i32 {
  let a = &x;
  *a = 4;
  return x;
}

// We assume the above is rejected.