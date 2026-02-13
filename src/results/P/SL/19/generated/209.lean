

theorem Topology.frontier_subset_closure_of_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) :
    frontier A ⊆ closure B := by
  intro x hx
  have hxClosA : x ∈ closure A := hx.1
  have hSub : closure A ⊆ closure B := closure_mono hAB
  exact hSub hxClosA