

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P3 A := by
  intro hP2
  -- closure (interior A) ⊆ closure A, since interior A ⊆ A
  have h_closure_subset : closure (interior A) ⊆ closure A := by
    exact closure_mono (interior_subset)
  -- hence interior (closure (interior A)) ⊆ interior (closure A)
  have h_interior_subset :
      interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h_closure_subset
  -- combine the inclusions to obtain the desired result
  exact Set.Subset.trans hP2 h_interior_subset