//----------------------------------------
// Function: concatenate10_kernel
//----------------------------------------
@group(0) @binding(0) var<storage, read_write> T_concat : array<f32>;
@group(0) @binding(1) var<storage, read> rxplaceholder : array<f32>;
@group(0) @binding(2) var<storage, read> rxplaceholder_1 : array<f32>;

struct PODArgs {
  packGridDimX: u32
}
@group(0) @binding(3) var<uniform> podArgs : PODArgs;

@compute @workgroup_size(256, 1, 1)
fn concatenate10_kernel(
  @builtin(workgroup_id) blockIdx : vec3<u32>,
  @builtin(num_workgroups) gridDim : vec3<u32>,
  @builtin(local_invocation_id) threadIdx : vec3<u32>
) {
  if (blockIdx.z * gridDim.x + blockIdx.x > podArgs.packGridDimX) { return; }
  let v__1 : i32 = i32(blockIdx.z * gridDim.x + blockIdx.x);
  for (var ax0_ax1_ax2_ax3_fused_0 : i32 = 0; ax0_ax1_ax2_ax3_fused_0 < 80i; ax0_ax1_ax2_ax3_fused_0++) {
    var condval : f32;
    if ((20i <= (ax0_ax1_ax2_ax3_fused_0 % 40i))) {
      condval = rxplaceholder[((((((ax0_ax1_ax2_ax3_fused_0 / 40i) * 1310720i) + ((ax0_ax1_ax2_ax3_fused_0 % 40i) * 65536i)) + (v__1 * 256i)) + i32(threadIdx.x)) - 1310720i)];
} else {
      condval = rxplaceholder_1[(((((ax0_ax1_ax2_ax3_fused_0 / 40i) * 1310720i) + ((ax0_ax1_ax2_ax3_fused_0 % 40i) * 65536i)) + (v__1 * 256i)) + i32(threadIdx.x))];
}
    T_concat[(((ax0_ax1_ax2_ax3_fused_0 * 65536i) + (v__1 * 256i)) + i32(threadIdx.x))] = condval;
  }
}