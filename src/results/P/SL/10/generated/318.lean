

theorem Topology.boundary_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) :
    closure A \ interior A ⊆ closure B := by
  intro x hx
  exact (closure_mono hAB) hx.1