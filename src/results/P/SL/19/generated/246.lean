

theorem Topology.frontier_eq_compl_interior_of_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} (hDense : closure A = (Set.univ : Set X)) :
    frontier A = (interior A)ᶜ := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hxNotInt
    have hxClos : x ∈ closure A := by
      have : x ∈ (Set.univ : Set X) := Set.mem_univ x
      simpa [hDense] using this
    exact And.intro hxClos hxNotInt