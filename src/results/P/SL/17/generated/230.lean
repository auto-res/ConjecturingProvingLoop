

theorem Topology.frontier_union_subset_union_frontier {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    frontier (A ∪ B) ⊆ frontier A ∪ frontier B := by
  intro x hx
  rcases hx with ⟨hClUnion, hNotIntUnion⟩
  -- `x` lies in either `closure A` or `closure B`
  have hCl : x ∈ closure A ∪ closure B := by
    simpa [closure_union] using hClUnion
  -- The interiors satisfy `interior A ∪ interior B ⊆ interior (A ∪ B)`
  have hIntSubset : interior A ∪ interior B ⊆ interior (A ∪ B) := by
    intro y hy
    cases hy with
    | inl hIntA =>
        exact
          (interior_mono (Set.subset_union_left : A ⊆ A ∪ B)) hIntA
    | inr hIntB =>
        exact
          (interior_mono (Set.subset_union_right : B ⊆ A ∪ B)) hIntB
  -- Case analysis on which closure contains `x`
  cases hCl with
  | inl hClA =>
      have hNotIntA : x ∉ interior A := by
        intro hIntA
        have : x ∈ interior (A ∪ B) := hIntSubset (Or.inl hIntA)
        exact hNotIntUnion this
      exact Or.inl ⟨hClA, hNotIntA⟩
  | inr hClB =>
      have hNotIntB : x ∉ interior B := by
        intro hIntB
        have : x ∈ interior (A ∪ B) := hIntSubset (Or.inr hIntB)
        exact hNotIntUnion this
      exact Or.inr ⟨hClB, hNotIntB⟩