

theorem Topology.closure_preimage_closed_of_continuous
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) {B : Set Y} (hB : IsClosed B) :
    closure (f ⁻¹' B) = f ⁻¹' B := by
  have hClosed : IsClosed (f ⁻¹' B) := hB.preimage hf
  simpa using hClosed.closure_eq