

theorem Topology.P3_superset_of_subset_interiorClosureInterior
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (hBsubset : B ⊆ interior (closure (interior A))) :
    Topology.P3 B := by
  dsimp [Topology.P3] at *
  intro x hxB
  have hxIntA : x ∈ interior (closure (interior A)) := hBsubset hxB
  have hMono₁ :
      interior (closure (interior A)) ⊆
        interior (closure (interior B)) :=
    Topology.interiorClosureInterior_mono hAB
  have hMono₂ :
      interior (closure (interior B)) ⊆ interior (closure B) :=
    Topology.interiorClosureInterior_subset_interiorClosure (A := B)
  exact hMono₂ (hMono₁ hxIntA)