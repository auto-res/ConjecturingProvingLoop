

theorem Topology.P1_implies_closure_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A → closure A ⊆ closure (interior A) := by
  intro hP1
  have h : closure A ⊆ closure (closure (interior A)) := closure_mono hP1
  simpa [closure_closure] using h