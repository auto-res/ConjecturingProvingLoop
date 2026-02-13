

theorem Topology.subset_closure_interior_of_P1 {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) (hP1B : Topology.P1 B) :
    A ⊆ closure (interior B) := by
  intro x hxA
  have hxB : x ∈ B := hAB hxA
  exact hP1B hxB