

theorem Topology.P1_closure_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → Topology.P1 (closure A) := by
  intro hP3
  intro x hx_closureA
  have hsubset : (closure A : Set X) ⊆ closure (interior (closure A)) :=
    Topology.P3_implies_closure_subset_closure_interior_closure (A := A) hP3
  exact hsubset hx_closureA