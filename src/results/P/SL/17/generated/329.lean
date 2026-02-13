

theorem Topology.frontier_subset_compl_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen A) :
    frontier A ⊆ Aᶜ := by
  intro x hx
  -- From `hx : x ∈ frontier A`, we have `x ∉ interior A`.
  have h_not_int : x ∉ interior A := hx.2
  -- Since `A` is open, `interior A = A`.
  have hIntEq : interior A = A := hA.interior_eq
  -- Therefore `x ∉ A`.
  have h_notA : x ∉ A := by
    simpa [hIntEq] using h_not_int
  -- Hence `x` belongs to the complement of `A`.
  simpa [Set.mem_compl] using h_notA