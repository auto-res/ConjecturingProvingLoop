

theorem interior_closure_eq_univ_iff_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) = (Set.univ : Set X) ↔
      closure (A : Set X) = (Set.univ : Set X) := by
  constructor
  · intro hInt
    have hSub : (Set.univ : Set X) ⊆ closure (A : Set X) := by
      intro x _
      have hx : (x : X) ∈ interior (closure (A : Set X)) := by
        simpa [hInt] using (Set.mem_univ (x : X))
      exact (interior_subset (s := closure (A : Set X))) hx
    exact Set.Subset.antisymm (Set.subset_univ _) hSub
  · intro hCl
    exact interior_closure_eq_univ_of_dense (A := A) hCl