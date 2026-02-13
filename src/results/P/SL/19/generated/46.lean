

theorem Topology.closure_interior_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (h : A ⊆ B) :
    closure (interior A) ⊆ closure (interior B) := by
  have hInt : interior A ⊆ interior B := interior_mono h
  exact closure_mono hInt