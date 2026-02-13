

theorem Topology.closureInterior_closure_eq_closure_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 (A := A)) :
    closure (interior (closure A)) = closure A := by
  apply subset_antisymm
  ·
    -- `interior (closure A)` is contained in `closure A`, hence their closures relate likewise.
    have h_int_subset : interior (closure A) ⊆ closure A := interior_subset
    simpa [closure_closure] using closure_mono h_int_subset
  ·
    -- From `P3`, `A ⊆ interior (closure A)`, so taking closures yields the reverse inclusion.
    have h_closure_subset : closure A ⊆ closure (interior (closure A)) := by
      have hA : (A : Set X) ⊆ interior (closure A) := hP3
      simpa [closure_closure] using closure_mono hA
    exact h_closure_subset