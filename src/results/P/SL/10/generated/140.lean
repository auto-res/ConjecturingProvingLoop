

theorem Topology.P2_preimage_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) {A : Set Y} (hA : IsOpen A) :
    Topology.P2 (f ⁻¹' A) := by
  have h_open : IsOpen (f ⁻¹' A) := hA.preimage hf
  exact Topology.isOpen_implies_P2 (X := X) (A := f ⁻¹' A) h_open