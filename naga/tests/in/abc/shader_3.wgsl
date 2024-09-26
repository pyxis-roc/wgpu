// enable f32;

struct Uniforms { vec_size:u32, aData_shape:vec2<u32>, aData_strides:vec2<u32>, outputData_shape:vec2<u32>, outputData_strides:vec2<u32> };
@group(0) @binding(3) var<uniform> uniforms: Uniforms;

@group(0) @binding(0) var<storage, read> aData: array<vec4<f32>>;
@group(0) @binding(1) var<storage, read> bData: array<vec4<f32>>;
@group(0) @binding(2) var<storage, read_write> outputData: array<vec4<f32>>;

        

@compute @workgroup_size(64, 1, 1)
fn main(@builtin(global_invocation_id) global_id : vec3<u32>,
        @builtin(workgroup_id) workgroup_id : vec3<u32>,
        @builtin(local_invocation_id) local_id : vec3<u32>) {
    let global_idx = global_id.x; let local_idx = local_id.x;
    if (global_idx >= uniforms.vec_size) { return; }
    outputData[global_idx]=aData[global_idx]*vec4<f32>(bData[0].x);
}