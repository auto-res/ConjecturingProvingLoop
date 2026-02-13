

theorem Topology.closureInterior_diff_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A \ B : Set X)) ⊆ closure (interior (A : Set X)) := by
  exact
    closure_mono
      (interior_mono (Set.diff_subset : (A \ B : Set X) ⊆ (A : Set X)))