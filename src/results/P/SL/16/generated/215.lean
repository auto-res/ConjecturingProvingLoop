

theorem Topology.closure_interior_union_eq_univ_of_dense_left
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h_dense : closure (interior A) = (Set.univ : Set X)) :
    closure (interior (A ∪ B)) = (Set.univ : Set X) := by
  apply subset_antisymm
  · intro x _
    simp
  · intro x _
    -- From the density hypothesis, `x ∈ closure (interior A)`.
    have hxA : (x : X) ∈ closure (interior A) := by
      simpa [h_dense] using (by simp : (x : X) ∈ (Set.univ : Set X))
    -- `interior A ⊆ interior (A ∪ B)` by monotonicity of `interior`.
    have h_int_subset : (interior A : Set X) ⊆ interior (A ∪ B) := by
      have hA_subset : (A : Set X) ⊆ A ∪ B := by
        intro y hy; exact Or.inl hy
      exact interior_mono hA_subset
    -- Taking closures preserves inclusions.
    have h_cl_subset :
        closure (interior A) ⊆ closure (interior (A ∪ B)) :=
      closure_mono h_int_subset
    -- Conclude that `x ∈ closure (interior (A ∪ B))`.
    have : (x : X) ∈ closure (interior (A ∪ B)) := h_cl_subset hxA
    simpa using this