

theorem Topology.closureInterior_eq_univ_of_open_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_open : IsOpen (A : Set X)) (h_dense : Dense (A : Set X)) :
    closure (interior A) = (Set.univ : Set X) := by
  have h_int : interior A = A := h_open.interior_eq
  have h_cl : closure A = (Set.univ : Set X) := h_dense.closure_eq
  calc
    closure (interior A) = closure A := by
      simpa [h_int]
    _ = (Set.univ : Set X) := by
      simpa [h_cl]