

theorem P1_imp_eq_empty_of_closureInterior_empty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A)
    (hClInt : closure (interior A) = (∅ : Set X)) :
    A = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hxA
    have hxCl : (x : X) ∈ closure (interior A) := hP1 hxA
    simpa [hClInt] using hxCl
  · exact Set.empty_subset _