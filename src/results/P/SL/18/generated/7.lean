

theorem P3_closed_iff_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P3 A ↔ IsOpen A := by
  -- first, rewrite `closure A` using closedness of `A`
  have hClosure : closure A = A := hA_closed.closure_eq
  unfold Topology.P3
  constructor
  · intro hP3
    -- from `P3`, deduce `A ⊆ interior A`
    have hSub : A ⊆ interior A := by
      simpa [hClosure] using hP3
    -- combine with `interior_subset` to get equality
    have hEq : interior A = A := by
      apply Set.Subset.antisymm
      · exact interior_subset
      · exact hSub
    -- use the fact that `interior A` is open
    have hOpenInt : IsOpen (interior A) := isOpen_interior
    simpa [hEq] using hOpenInt
  · intro hOpen
    -- an open set is contained in the interior of its closure
    exact interior_maximal subset_closure hOpen