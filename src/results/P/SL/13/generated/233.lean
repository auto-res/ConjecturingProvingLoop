

theorem Topology.P1_and_dense_implies_denseInterior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (X := X) A → Dense (A : Set X) → Dense (interior (A : Set X)) := by
  intro hP1 hDenseA
  dsimp [Dense] at hDenseA ⊢
  -- `P1` gives equality of closures.
  have h_cl_eq : closure (A : Set X) = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closureInterior (X := X) (A := A)).1 hP1
  -- Rewrite the density statement using `h_cl_eq`.
  simpa [h_cl_eq] using hDenseA