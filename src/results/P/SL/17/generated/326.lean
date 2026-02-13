

theorem Topology.interior_subset_closure_of_subset_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ closure B) :
    interior A ⊆ closure B := by
  intro x hxIntA
  exact hAB (interior_subset hxIntA)