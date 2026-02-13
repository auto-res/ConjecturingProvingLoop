

theorem Topology.closure_interior_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : (A : Set X) ⊆ B) :
    closure (interior A) ⊆ closure (interior B) := by
  have hInt : (interior A : Set X) ⊆ interior B := interior_mono hAB
  exact closure_mono hInt