

theorem Topology.interior_closure_union_eq {X : Type*} [TopologicalSpace X]
    (A B : Set X) :
    interior (closure (A ∪ B)) = interior (closure A ∪ closure B) := by
  have h := Topology.closure_union_eq (A) (B)
  simpa [h]