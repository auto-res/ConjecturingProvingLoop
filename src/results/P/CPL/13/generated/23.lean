

theorem interior_closure_eq_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P2 A) : interior (closure (interior A)) = interior (closure A) := by
  -- Obtain `P1 A` from `P2 A`
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 hA
  -- Hence the closures coincide
  have h_cl : closure (interior A) = closure A :=
    Topology.closure_eq_of_P1 hP1
  -- Rewrite using this equality
  simpa [h_cl]

theorem P3_of_closure_subset {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure A ⊆ interior (closure A)) : Topology.P3 (closure A) := by
  dsimp [Topology.P3] at *
  simpa [closure_closure] using h