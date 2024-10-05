fn test_kernel(cond: bool) -> u32{
    var y: u32 = 1u;
    if (cond) {
        y = y + 1;
    } else {
        y = y - 1;
    }

    return y;
}

fn test_kernel2(cond: bool) -> u32{
    var y: vec3<u32>;
    if (cond) {
        y[0] = y[0] + 1;
    } else {
        y[0] = y[0] - 1;
    }

    return y[0];
}