

theorem P1_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A := by
  -- Since `A` is open, its interior coincides with itself.
  have hInt : interior A = A := hA.interior_eq
  -- Every set is contained in the closure of itself.
  have : (A : Set X) ⊆ closure (interior A) := by
    simpa [hInt] using (subset_closure : A ⊆ closure A)
  exact this