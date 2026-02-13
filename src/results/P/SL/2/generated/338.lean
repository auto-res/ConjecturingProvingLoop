

theorem Topology.frontier_inter_self_eq_empty_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsOpen A → frontier (A : Set X) ∩ A = (∅ : Set X) := by
  intro hOpen
  simpa [hOpen.interior_eq] using
    (Topology.frontier_inter_interior_eq_empty (A := A))