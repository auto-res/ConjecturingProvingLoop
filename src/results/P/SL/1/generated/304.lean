

theorem Topology.interior_inter_eq_empty_of_interiors_disjoint
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : interior A ∩ interior B = (∅ : Set X)) :
    interior (A ∩ B) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hx' : x ∈ interior A ∩ interior B :=
      (Topology.interior_inter_subset (A := A) (B := B)) hx
    have : x ∈ (∅ : Set X) := by
      simpa [h] using hx'
    exact this
  · exact Set.empty_subset _