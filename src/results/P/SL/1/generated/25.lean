

theorem Topology.closure_eq_closure_interior_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → closure A = closure (interior A) := by
  intro hP1
  apply Set.Subset.antisymm
  ·
    have hsub : (A : Set X) ⊆ closure (interior A) := hP1
    have : closure A ⊆ closure (closure (interior A)) := closure_mono hsub
    simpa using this
  ·
    have hsub : interior A ⊆ (A : Set X) := interior_subset
    have : closure (interior A) ⊆ closure A := closure_mono hsub
    simpa using this