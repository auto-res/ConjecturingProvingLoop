

theorem P3_imp_eq_empty_of_interiorClosure_empty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A)
    (hInt : interior (closure A) = (∅ : Set X)) :
    A = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hxA
    have : (x : X) ∈ interior (closure A) := hP3 hxA
    simpa [hInt] using this
  · exact Set.empty_subset _