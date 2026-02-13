

theorem Topology.P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior A) := by
  unfold Topology.P1
  intro x hx
  have h : x ∈ closure (interior A) := subset_closure hx
  simpa [interior_interior] using h