

theorem Topology.frontier_subset_compl_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : frontier A ⊆ Aᶜ := by
  intro x hx
  -- `hx` gives `x ∉ interior A`.
  have hNotInt : x ∉ interior A := hx.2
  -- Since `A` is open, `interior A = A`.
  have hIntEq : interior A = A := hA.interior_eq
  -- Therefore, `x ∉ A`.
  have hNotA : x ∉ A := by
    simpa [hIntEq] using hNotInt
  -- Hence, `x ∈ Aᶜ`.
  simpa using hNotA