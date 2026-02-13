

theorem Topology.P1_iff_closure_subset_closureInterior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (X := X) A ↔ closure (A : Set X) ⊆ closure (interior A) := by
  constructor
  · intro hP1
    -- From `P1`, we have equality of the two closures, hence the desired subset.
    have h_eq : closure (A : Set X) = closure (interior A) :=
      (Topology.P1_iff_closure_eq_closureInterior (X := X) (A := A)).1 hP1
    simpa [h_eq]
  · intro h_subset
    -- The reverse inclusion always holds, giving equality of the closures.
    have h_subset' : closure (interior A) ⊆ closure (A : Set X) :=
      closure_mono (interior_subset : interior A ⊆ A)
    have h_eq : closure (A : Set X) = closure (interior A) :=
      Set.Subset.antisymm h_subset h_subset'
    -- Convert the equality back to `P1`.
    exact
      (Topology.P1_iff_closure_eq_closureInterior (X := X) (A := A)).2 h_eq