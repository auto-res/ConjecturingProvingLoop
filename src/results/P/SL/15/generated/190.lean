

theorem P1_and_denseInterior_implies_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Dense (interior A) → Dense A := by
  intro hP1 hDenseInt
  -- From `P1` and the density of `interior A` we know `closure A = univ`.
  have h_closure :
      closure A = (Set.univ : Set X) :=
    closure_eq_univ_of_P1_and_denseInterior
      (X := X) (A := A) hP1 hDenseInt
  -- Translate this equality into the desired `Dense A`.
  exact (dense_iff_closure_eq).2 h_closure