

theorem Topology.frontier_diff_subset_union_frontier {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    frontier (A \ B : Set X) ⊆ frontier A ∪ frontier B := by
  classical
  intro x hx
  -- Rewrite the difference as an intersection with the complement.
  have hx' : x ∈ frontier (A ∩ Bᶜ : Set X) := by
    simpa [Set.diff_eq] using hx
  -- Apply the lemma for intersections.
  have hStep :=
    (Topology.frontier_inter_subset_union_frontier
        (A := A) (B := Bᶜ)) hx'
  -- Convert the frontier of `Bᶜ` back to `B` using `frontier_compl`.
  cases hStep with
  | inl hA =>
      exact Or.inl hA
  | inr hBcompl =>
      have hB : x ∈ frontier (B : Set X) := by
        simpa [frontier_compl (A := B)] using hBcompl
      exact Or.inr hB