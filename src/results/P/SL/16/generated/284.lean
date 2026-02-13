

theorem Topology.P2_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → A ⊆ interior (closure A) := by
  intro hP2 x hxA
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
  have hSubset :
      interior (closure (interior A)) ⊆ interior (closure A) :=
    Topology.interior_closure_interior_subset_interior_closure (X := X) (A := A)
  exact hSubset hxInt