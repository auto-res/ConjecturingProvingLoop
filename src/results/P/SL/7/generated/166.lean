

theorem Topology.P3_superset_of_subset_interiorClosure {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) (hBsubset : B ⊆ interior (closure A)) :
    Topology.P3 B := by
  dsimp [Topology.P3] at *
  intro x hxB
  have hxIntA : x ∈ interior (closure A) := hBsubset hxB
  have hIncl : interior (closure A) ⊆ interior (closure B) :=
    interior_mono (closure_mono hAB)
  exact hIncl hxIntA