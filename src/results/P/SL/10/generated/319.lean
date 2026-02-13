

theorem Topology.interior_preimage_open {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) {A : Set Y}
    (hA : IsOpen A) :
    interior (f ⁻¹' A) = f ⁻¹' A := by
  have hOpen : IsOpen (f ⁻¹' A) := hA.preimage hf
  simpa [hOpen.interior_eq]