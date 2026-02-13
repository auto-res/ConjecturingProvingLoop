

theorem Topology.interior_closure_union_subset_union_closure {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    interior (closure ((A ∪ B) : Set X)) ⊆
      closure (A : Set X) ∪ closure B := by
  intro x hx
  have hx' : (x : X) ∈ closure ((A ∪ B) : Set X) := interior_subset hx
  simpa [closure_union] using hx'