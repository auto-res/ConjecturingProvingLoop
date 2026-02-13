

theorem Topology.interior_closureInterior_eq_interior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    interior (closure (interior A)) = interior A := by
  apply subset_antisymm
  ·
    have h_sub : closure (interior A) ⊆ (A : Set X) :=
      Topology.closureInterior_subset_of_isClosed (A := A) hA_closed
    exact interior_mono h_sub
  ·
    have h_sub : (interior A : Set X) ⊆ closure (interior A) := subset_closure
    exact interior_maximal h_sub isOpen_interior