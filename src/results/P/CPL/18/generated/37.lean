

theorem P3_of_dense_iUnion {X : Type*} [TopologicalSpace X] {A : ℕ → Set X} (hA : ∀ n, Dense (A n)) : Topology.P3 (⋃ n, A n) := by
  -- Unfold the definition of `P3`.
  dsimp [Topology.P3]
  intro x hx
  -- First, prove that the closure of the union is `univ`.
  have h_closure_univ :
      closure (⋃ n, (A n : Set X)) = (Set.univ : Set X) := by
    -- `A 0` is dense, hence its closure is `univ`.
    have hA0 : closure (A 0 : Set X) = (Set.univ : Set X) := by
      simpa using (hA 0).closure_eq
    -- `A 0 ⊆ ⋃ n, A n`.
    have hA0_subset : (A 0 : Set X) ⊆ ⋃ n, A n := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨0, hy⟩
    -- Therefore `closure (A 0) ⊆ closure (⋃ n, A n)`.
    have h_closure_subset :
        closure (A 0 : Set X) ⊆ closure (⋃ n, A n : Set X) :=
      closure_mono hA0_subset
    -- Rewrite the inclusion using `hA0`.
    have : (Set.univ : Set X) ⊆ closure (⋃ n, A n : Set X) := by
      simpa [hA0] using h_closure_subset
    -- Conclude with set equality.
    exact Set.Subset.antisymm (Set.subset_univ _) this
  -- Now `interior (closure …) = univ`, so the goal is immediate.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_closure_univ, interior_univ] using this