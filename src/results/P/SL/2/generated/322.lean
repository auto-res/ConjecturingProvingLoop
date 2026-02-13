

theorem Topology.frontier_eq_compl_of_open_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsOpen A → Dense A → frontier (A : Set X) = (Aᶜ : Set X) := by
  intro hOpen hDense
  have h := Topology.frontier_eq_univ_diff_interior_of_dense (A := A) hDense
  simpa [hOpen.interior_eq, Set.compl_eq_univ_diff] using h