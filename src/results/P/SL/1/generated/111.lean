

theorem Topology.interior_closure_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (h : A ⊆ B) :
    interior (closure A) ⊆ interior (closure B) := by
  exact interior_mono (closure_mono h)