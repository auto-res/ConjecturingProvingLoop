

theorem P3_of_P1_and_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (A : Set X)) (hDense : Dense (A : Set X)) :
    Topology.P3 (A : Set X) := by
  dsimp [Topology.P3] at *
  intro x hxA
  -- Density gives `closure A = univ`.
  have hCl : closure (A : Set X) = (Set.univ : Set X) :=
    (Topology.dense_iff_closure_eq_univ (A := A)).1 hDense
  -- Hence `interior (closure A)` is `univ`.
  have hInt : interior (closure (A : Set X)) = (Set.univ : Set X) := by
    simpa [hCl, interior_univ]
  -- The goal now follows trivially.
  have : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [hInt] using this