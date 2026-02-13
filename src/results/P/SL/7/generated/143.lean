

theorem Topology.subset_interiorClosure_of_subset_P2 {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) (hP2B : Topology.P2 B) :
    A ⊆ interior (closure B) := by
  intro x hxA
  have hxB : x ∈ B := hAB hxA
  have hxInt : x ∈ interior (closure (interior B)) := hP2B hxB
  have hIncl : interior (closure (interior B)) ⊆ interior (closure B) :=
    interiorClosureInterior_subset_interiorClosure (A := B)
  exact hIncl hxInt