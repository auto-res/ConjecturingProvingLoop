

theorem Topology.frontier_closure_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    frontier (closure (A : Set X)) ⊆ closure (A : Set X) := by
  -- Apply the general inclusion `frontier S ⊆ closure S` to `S = closure A`.
  have h :
      frontier (closure (A : Set X)) ⊆ closure (closure (A : Set X)) :=
    Topology.frontier_subset_closure (A := closure (A : Set X))
  simpa [closure_closure] using h