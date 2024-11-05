@group(0) @binding(0) var<storage> a : array<u32>;
@group(0) @binding(1) var<storage> b : array<u32>;
@group(0) @binding(2) var<storage, read_write> c : array<u32>;
@group(0) @binding(3) var<storage> idx: u32;

var<workgroup> d: atomic<u32>;

// The simplest loop I can think of.
// We have stuff here that we don't need for bounds checks and should be ignored.
// We shouldn't panic.

fn test_loop() {
    // this add does nothing for accesses, and should be ignored.
    let r = atomicAdd(&d, 1u);

    c[idx] = a[idx] + b[idx] + r;

}