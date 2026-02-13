

theorem Topology.Subset_interiorClosureInterior_of_P2
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) (hB : Topology.P2 B) :
    (A : Set X) ⊆ interior (closure (interior B)) := by
  dsimp [Topology.P2] at hB
  intro x hxA
  have hxB : (x : X) ∈ B := hAB hxA
  exact hB hxB