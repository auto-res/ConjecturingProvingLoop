

theorem Topology.closure_interior_closure_eq_closure_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} (hP3 : Topology.P3 A) :
    closure (interior (closure A)) = closure A := by
  apply subset_antisymm
  ·
    exact Topology.closure_interior_closure_subset_closure (A := A)
  ·
    have h_subset : A ⊆ interior (closure A) := hP3
    have : closure A ⊆ closure (interior (closure A)) := closure_mono h_subset
    exact this