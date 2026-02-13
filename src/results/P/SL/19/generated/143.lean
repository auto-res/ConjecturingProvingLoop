

theorem Topology.closure_diff_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A \ B) ⊆ closure A := by
  intro x hx
  have hMono : closure (A \ B) ⊆ closure A := closure_mono (by
    intro z hz
    exact hz.1)
  exact hMono hx