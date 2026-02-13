

theorem Topology.dense_iff_interior_closure_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Dense A ↔ interior (closure A) = (Set.univ : Set X) := by
  constructor
  · intro hDense
    exact Topology.interior_closure_eq_univ_of_dense (A := A) hDense
  · intro hInt
    -- First, deduce `closure A = Set.univ`.
    have h_closure_univ : closure A = (Set.univ : Set X) := by
      apply Set.Subset.antisymm
      · intro _x _hx; simp
      ·
        have h_subset : interior (closure A) ⊆ closure A := interior_subset
        simpa [hInt] using h_subset
    -- Build the desired `Dense A`.
    have hDense : Dense A := by
      intro x
      have : x ∈ (Set.univ : Set X) := by simp
      simpa [h_closure_univ] using this
    exact hDense