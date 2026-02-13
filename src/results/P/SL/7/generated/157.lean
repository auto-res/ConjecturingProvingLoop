

theorem Topology.subset_interiorClosureInterior_of_subset_P2
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (hP2B : Topology.P2 B) :
    A ⊆ interior (closure (interior B)) := by
  intro x hxA
  have hxB : x ∈ B := hAB hxA
  exact hP2B hxB