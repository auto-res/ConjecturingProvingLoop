

theorem P2_of_subset_and_subset_interiorClosure {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B)
    (hBsubset : B ⊆ interior (closure (interior A))) :
    Topology.P2 B := by
  dsimp [Topology.P2] at *
  intro x hxB
  -- From the hypothesis `hBsubset`, the point `x` already lies in
  -- `interior (closure (interior A))`.
  have hx₁ : x ∈ interior (closure (interior A)) := hBsubset hxB
  -- Since `A ⊆ B`, we have `interior A ⊆ interior B`.
  have hInt : interior A ⊆ interior B := interior_mono hAB
  -- Taking closures preserves inclusions.
  have hCl : closure (interior A) ⊆ closure (interior B) :=
    closure_mono hInt
  -- Applying `interior_mono` yields the desired containment between interiors.
  have hIncl :
      interior (closure (interior A)) ⊆
        interior (closure (interior B)) :=
    interior_mono hCl
  -- Conclude that `x ∈ interior (closure (interior B))`.
  exact hIncl hx₁