

theorem Topology.interior_closure_union_subset_union_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure ((A ∪ B) : Set X)) ⊆
      closure (A : Set X) ∪ closure (B : Set X) := by
  intro x hx
  -- From membership in the interior, obtain membership in the closure.
  have hx_cl : (x : X) ∈ closure ((A ∪ B) : Set X) := interior_subset hx
  -- Rewrite the closure of the union as the union of the closures.
  simpa [closure_union] using hx_cl