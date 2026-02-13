

theorem Topology.interior_closure_diff_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (A \ B)) ⊆ interior (closure A) := by
  intro x hx
  have hSub : (A \ B : Set X) ⊆ A := by
    intro z hz
    exact hz.1
  have hClosSub : closure (A \ B) ⊆ closure A := closure_mono hSub
  exact (interior_mono hClosSub) hx