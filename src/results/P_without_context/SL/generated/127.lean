

theorem isOpen_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hx
  have h_nhds_A : (A : Set X) ∈ 𝓝 x := hA.mem_nhds hx
  have h_nhds_closure : closure A ∈ 𝓝 x :=
    Filter.mem_of_superset h_nhds_A subset_closure
  exact (mem_interior_iff_mem_nhds).2 h_nhds_closure