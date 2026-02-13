

theorem Topology.P3_implies_closure_interior_closure_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → closure (interior (closure A)) = closure A := by
  intro hP3
  apply subset_antisymm
  ·
    have h : (interior (closure A) : Set X) ⊆ closure A := interior_subset
    have h' : closure (interior (closure A)) ⊆ closure A := by
      have h₁ := closure_mono h
      simpa [closure_closure] using h₁
    exact h'
  ·
    exact
      Topology.P3_implies_closure_subset_closure_interior_closure
        (A := A) hP3