

theorem Topology.P2_superset_of_subset_interiorClosureInterior
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (hBsubset : B ⊆ interior (closure (interior A))) :
    Topology.P2 B := by
  dsimp [Topology.P2] at *
  intro x hxB
  have hxIntA : x ∈ interior (closure (interior A)) := hBsubset hxB
  have hIncl : interior (closure (interior A)) ⊆
      interior (closure (interior B)) := by
    apply interior_mono
    apply closure_mono
    apply interior_mono
    exact hAB
  exact hIncl hxIntA