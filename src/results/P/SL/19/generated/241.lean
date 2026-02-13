

theorem Topology.frontier_subset_compl_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} :
    (frontier A ⊆ Aᶜ) ↔ IsOpen A := by
  constructor
  · intro hSub
    -- We prove that every point of `A` is interior, hence `A` is open.
    have hInt : (A : Set X) ⊆ interior A := by
      intro x hxA
      by_cases hxInt : x ∈ interior A
      · exact hxInt
      ·
        -- If `x ∉ interior A`, then `x` lies in the frontier of `A`.
        have hxFront : x ∈ frontier A := by
          have hxClos : x ∈ closure A := subset_closure hxA
          exact And.intro hxClos hxInt
        -- But the frontier is assumed to be contained in `Aᶜ`, contradicting `x ∈ A`.
        have : x ∈ Aᶜ := hSub hxFront
        exact (this hxA).elim
    -- Since `interior A ⊆ A` always holds, we have `interior A = A`.
    have hEq : interior A = A := Set.Subset.antisymm interior_subset hInt
    simpa [hEq] using (isOpen_interior : IsOpen (interior A))
  · intro hOpen
    exact frontier_subset_compl_of_isOpen (A := A) hOpen