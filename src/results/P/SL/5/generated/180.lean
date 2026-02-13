

theorem subset_closure_interior_of_subset_P1 {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hB : Topology.P1 (X := X) B) (hAB : A ⊆ B) :
    A ⊆ closure (interior B) := by
  intro x hxA
  exact hB (hAB hxA)