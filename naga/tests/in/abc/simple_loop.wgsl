@group(0) @binding(0) var<storage> a : array<u32>;
@group(0) @binding(0) var<storage> b : array<u32>;
@group(0) @binding(0) var<storage, read_write> c : array<u32>;


// The simplest loop I can think of.
fn test_loop() {
    // What we need here is to be able to output this:
    for(var i = 0i; i < 10; i++) {
        c[i] = a[i] + b[i];
    }
}