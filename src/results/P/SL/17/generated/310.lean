

theorem Topology.frontier_diff_subset_union_frontier {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    frontier (A \ B) ⊆ frontier A ∪ frontier B := by
  intro x hx
  -- Rewrite the frontier of the difference as the frontier of an intersection.
  have h_eq : frontier (A \ B) = frontier (A ∩ Bᶜ) := by
    simp [Set.diff_eq]
  -- Transport the membership along the equality.
  have hx' : x ∈ frontier (A ∩ Bᶜ) := by
    simpa [h_eq] using hx
  -- Apply the existing inclusion for frontiers of intersections.
  have hx'' :
      x ∈ frontier A ∪ frontier (Bᶜ) :=
    (Topology.frontier_inter_subset_union_frontier
      (A := A) (B := Bᶜ)) hx'
  -- Replace `frontier (Bᶜ)` with `frontier B`.
  cases hx'' with
  | inl hA =>
      exact Or.inl hA
  | inr hBc =>
      have hB : x ∈ frontier B := by
        simpa [Topology.frontier_compl (A := B)] using hBc
      exact Or.inr hB