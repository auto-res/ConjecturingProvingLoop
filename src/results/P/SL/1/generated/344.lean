

theorem Topology.interior_closure_union_subset_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∪ B : Set X)) ⊆ closure A ∪ closure B := by
  intro x hx
  -- From `hx : x ∈ interior (closure (A ∪ B))` we first deduce that
  -- `x` lies in `closure (A ∪ B)` by `interior_subset`.
  have hcl : x ∈ closure (A ∪ B : Set X) := interior_subset hx
  -- Next, rewrite `closure (A ∪ B)` using `closure_union`.
  -- This shows `x ∈ closure A ∪ closure B`, as desired.
  simpa [closure_union] using hcl