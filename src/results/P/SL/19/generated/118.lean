

theorem Topology.closure_interior_closure_inter_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure A)) ∩ interior (closure A) =
      interior (closure A) := by
  apply Set.Subset.antisymm
  · intro x hx
    exact hx.2
  · intro x hxInt
    have hxClos : x ∈ closure (interior (closure A)) := by
      have hSub : (interior (closure A) : Set X) ⊆ closure (interior (closure A)) :=
        subset_closure
      exact hSub hxInt
    exact And.intro hxClos hxInt