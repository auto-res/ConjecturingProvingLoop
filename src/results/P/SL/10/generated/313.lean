

theorem Topology.P2_iff_P3_preimage_closed {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) {A : Set Y}
    (hA : IsClosed A) :
    Topology.P2 (f ⁻¹' A) ↔ Topology.P3 (f ⁻¹' A) := by
  -- The preimage of a closed set under a continuous map is closed.
  have hClosed : IsClosed (f ⁻¹' A) := hA.preimage hf
  -- Apply the existing equivalence for closed sets.
  simpa using
    (Topology.P2_iff_P3_of_isClosed (X := X) (A := f ⁻¹' A) hClosed)