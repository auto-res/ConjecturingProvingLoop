

theorem subset_interior_closure_of_subset_P3 {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hP3B : Topology.P3 (X := X) B) (hAB : A ⊆ B) :
    A ⊆ interior (closure B) := by
  intro x hxA
  have hxB : x ∈ B := hAB hxA
  exact hP3B hxB