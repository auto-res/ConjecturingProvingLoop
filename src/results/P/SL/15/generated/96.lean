

theorem P3_implies_closure_eq_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → closure A = closure (interior (closure A)) := by
  intro hP3
  apply Set.Subset.antisymm
  · -- `closure A ⊆ closure (interior (closure A))`
    have h_sub : A ⊆ interior (closure A) := hP3
    have : closure A ⊆ closure (interior (closure A)) := closure_mono h_sub
    exact this
  · -- `closure (interior (closure A)) ⊆ closure A`
    have h_sub : interior (closure A) ⊆ closure A := interior_subset
    have : closure (interior (closure A)) ⊆ closure A := by
      simpa [closure_closure] using closure_mono h_sub
    exact this