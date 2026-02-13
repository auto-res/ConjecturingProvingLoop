

theorem Topology.interior_closure_diff_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (A \ B)) ⊆ interior (closure A) := by
  have h_closure : closure (A \ B) ⊆ closure A :=
    closure_mono (Set.diff_subset : A \ B ⊆ A)
  exact interior_mono h_closure