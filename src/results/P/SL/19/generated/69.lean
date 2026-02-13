

theorem Topology.closure_eq_of_subset_of_subset_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) (hBClA : B ⊆ closure A) :
    closure A = closure B := by
  apply Set.Subset.antisymm
  · exact closure_mono hAB
  ·
    have h : closure B ⊆ closure (closure A) := closure_mono hBClA
    simpa [closure_closure] using h