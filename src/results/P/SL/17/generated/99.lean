

theorem Topology.subset_interior_closure_of_P3 {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) (hP3B : Topology.P3 B) :
    A ⊆ interior (closure B) := by
  intro x hxA
  have hxB : x ∈ B := hAB hxA
  exact hP3B hxB