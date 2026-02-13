

theorem Topology.eq_empty_of_P1_of_interior_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hInt : interior A = (∅ : Set X)) (hP1 : Topology.P1 A) :
    (A : Set X) = (∅ : Set X) := by
  have hsubset : (A : Set X) ⊆ (∅ : Set X) := by
    intro x hx
    have hx_cl : x ∈ closure (interior A) := hP1 hx
    simpa [hInt, closure_empty] using hx_cl
  exact Set.Subset.antisymm hsubset (Set.empty_subset _)