

theorem Topology.interior_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ⊆ closure A := by
  intro x hx
  have hxA : (x : X) ∈ A := interior_subset hx
  exact subset_closure hxA