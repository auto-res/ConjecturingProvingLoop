

theorem Topology.P3_union_dense_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} (h_dense : closure A = (Set.univ : Set X)) :
    Topology.P3 (A ∪ B) := by
  -- First, show that `closure (A ∪ B) = univ`.
  have h_closure_union : closure (A ∪ B) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · exact Set.Subset_univ
    · intro x _
      -- Since `closure A = univ`, every point lies in `closure A`.
      have hx_clA : (x : X) ∈ closure A := by
        simpa [h_dense]
      -- Monotonicity of `closure` gives the desired membership.
      have h_mono : closure A ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_left : A ⊆ A ∪ B)
      exact h_mono hx_clA
  -- Conclude using the criterion for dense sets.
  exact Topology.P3_of_dense (X := X) (A := A ∪ B) h_closure_union