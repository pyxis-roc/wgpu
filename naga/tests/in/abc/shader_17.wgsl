// enable f32;
// For right now, just assume f32...
// type f32 = f32;


struct Uniforms { 
    output_size:u32,
    a_shape:array<vec4<u32>, 2>,
    a_strides:array<vec4<u32>, 2>,
    output_shape:array<vec4<u32>, 2>,
    output_strides:array<vec4<u32>, 2>,
};


@group(0) @binding(2) var<uniform> uniforms: Uniforms;
fn i2o_a(indices: array<u32, 6>) -> u32 {
  return uniforms.a_strides[1][1] * (indices[5])+uniforms.a_strides[1][0] * (indices[4])+uniforms.a_strides[0][3] * (indices[3])+uniforms.a_strides[0][2] * (indices[2])+uniforms.a_strides[0][1] * (indices[1])+uniforms.a_strides[0][0] * (indices[0]);
}

fn get_aByIndices(indices: array<u32, 6>) -> f32 {
  return a[i2o_a(indices)];
}

fn o2i_output(offset: u32) -> array<u32, 6> {
  var indices: array<u32, 6>;
  var current = offset;
  
  let dim0 = current / uniforms.output_strides[0][0];
  let rest0 = current % uniforms.output_strides[0][0];
  indices[0] = dim0;
  current = rest0;
  
  let dim1 = current / uniforms.output_strides[0][1];
  let rest1 = current % uniforms.output_strides[0][1];
  indices[1] = dim1;
  current = rest1;
  
  let dim2 = current / uniforms.output_strides[0][2];
  let rest2 = current % uniforms.output_strides[0][2];
  indices[2] = dim2;
  current = rest2;
  
  let dim3 = current / uniforms.output_strides[0][3];
  let rest3 = current % uniforms.output_strides[0][3];
  indices[3] = dim3;
  current = rest3;
  
  let dim4 = current / uniforms.output_strides[1][0];
  let rest4 = current % uniforms.output_strides[1][0];
  indices[4] = dim4;
  current = rest4;
  indices[5] = current;
  return indices;
}

@group(0) @binding(0) var<storage, read> a: array<f32>;
@group(0) @binding(1) var<storage, read_write> output: array<f32>;

fn perm(i: array<u32, 6>) -> array<u32, 6> {
    var a: array<u32, 6>;
  a[0]=i[0];
  a[1]=i[1];
  a[3]=i[2];
  a[2]=i[3];
  a[4]=i[4];
  a[5]=i[5];
  return a;
}

@compute @workgroup_size(64, 1, 1)
fn main(@builtin(global_invocation_id) global_id : vec3<u32>,
  @builtin(workgroup_id) workgroup_id : vec3<u32>,
  @builtin(local_invocation_id) local_id : vec3<u32>) {
  let global_idx = global_id.x; let local_idx = local_id.x;

  if (global_idx >= uniforms.output_size) { return; }

  let indices = o2i_output(global_idx);
  let aIndices = perm(indices);

  output[global_idx]=get_aByIndices(aIndices);
}