// enable f32;

struct Uniforms { outputSize:u32, sizeInConcatAxis0:u32, sizeInConcatAxis1:u32, input0_shape:vec4<u32>, input0_strides:vec4<u32>, input1_shape:vec4<u32>, input1_strides:vec4<u32>, output_shape:vec4<u32>, output_strides:vec4<u32> };
@group(0) @binding(3) var<uniform> uniforms: Uniforms;
fn i2o_input0(indices: vec4<u32>) -> u32 {
    return uniforms.input0_strides[3] * (indices[3])+uniforms.input0_strides[2] * (indices[2])+uniforms.input0_strides[1] * (indices[1])+uniforms.input0_strides[0] * (indices[0]);
}

fn get_input0ByIndices(indices: vec4<u32>) -> f32 {
    return input0[i2o_input0(indices)];
}

fn i2o_input1(indices: vec4<u32>) -> u32 {
    return uniforms.input1_strides[3] * (indices[3])+uniforms.input1_strides[2] * (indices[2])+uniforms.input1_strides[1] * (indices[1])+uniforms.input1_strides[0] * (indices[0]);
}

fn get_input1ByIndices(indices: vec4<u32>) -> f32 {
    return input1[i2o_input1(indices)];
}

fn o2i_output(offset: u32) -> vec4<u32> {
    var indices: vec4<u32>;
    var current = offset;

    let dim0 = current / uniforms.output_strides[0];
    let rest0 = current % uniforms.output_strides[0];
    indices[0] = dim0;
    current = rest0;

    let dim1 = current / uniforms.output_strides[1];
    let rest1 = current % uniforms.output_strides[1];
    indices[1] = dim1;
    current = rest1;

    let dim2 = current / uniforms.output_strides[2];
    let rest2 = current % uniforms.output_strides[2];
    indices[2] = dim2;
    current = rest2;
    indices[3] = current;
    return indices;
}


@group(0) @binding(0) var<storage, read> input0: array<f32>;
@group(0) @binding(1) var<storage, read> input1: array<f32>;
@group(0) @binding(2) var<storage, read_write> output: array<f32>;

  
fn calculateInputIndex(index: u32) -> u32 {
    let sizeInConcatAxis = array<u32, 2u>(uniforms.sizeInConcatAxis0,uniforms.sizeInConcatAxis1);
    for (var i: u32 = 0u; i < 2; i += 1u ) {
        if (index < sizeInConcatAxis[i]) {
        return i;
        }
    }
    return 2u;
}

@compute @workgroup_size(64, 1, 1)
fn main(@builtin(global_invocation_id) global_id : vec3<u32>,
        @builtin(workgroup_id) workgroup_id : vec3<u32>,
        @builtin(local_invocation_id) local_id : vec3<u32>) {
    let global_idx = global_id.x; let local_idx = local_id.x;
  
    if (global_idx >= uniforms.outputSize) { return; }

    var indices = o2i_output(global_idx);

    let inputIndex = calculateInputIndex(indices[2]);
    if (inputIndex != 0u) {
      let sizeInConcatAxis = array<u32, 2u>(uniforms.sizeInConcatAxis0,uniforms.sizeInConcatAxis1);
      indices[2] -= sizeInConcatAxis[inputIndex - 1u];
    }

    if (inputIndex == 0u) { output[global_idx]=get_input0ByIndices(indices); }
    else { output[global_idx]=get_input1ByIndices(indices); }
}