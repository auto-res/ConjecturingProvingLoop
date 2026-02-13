

theorem Topology.interior_closure_diff_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure ((A \ B) : Set X)) ⊆ interior (closure (A : Set X)) := by
  -- Since `A \ B ⊆ A`, monotonicity gives all required inclusions.
  have hSub : ((A \ B) : Set X) ⊆ (A : Set X) := by
    intro x hx
    exact hx.1
  have hCl : closure ((A \ B) : Set X) ⊆ closure (A : Set X) :=
    closure_mono hSub
  exact interior_mono hCl