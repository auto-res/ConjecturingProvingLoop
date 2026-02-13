

theorem Topology.frontier_eq_closure_diff_self_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsOpen (A : Set X) → frontier (A : Set X) = closure (A : Set X) \ A := by
  intro hOpen
  simpa [frontier, hOpen.interior_eq]