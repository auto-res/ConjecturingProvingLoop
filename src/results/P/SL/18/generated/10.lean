

theorem P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P3 A := by
  -- An open set is contained in the interior of its closure.
  exact
    (interior_maximal (subset_closure : (A : Set X) ⊆ closure A) hA)