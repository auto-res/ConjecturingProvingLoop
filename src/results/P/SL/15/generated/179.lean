

theorem denseInterior_implies_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P3 (closure A) := by
  intro hDense
  -- First obtain `P2 (closure A)` from the density of `interior A`.
  have hP2 : Topology.P2 (closure A) :=
    Topology.denseInterior_implies_P2_closure (X := X) (A := A) hDense
  -- Use the equivalence between `P2` and `P3` for a closed set.
  have hEquiv :=
    (Topology.P2_closure_iff_P3_closure (X := X) (A := A))
  -- Convert `P2` into `P3`.
  exact hEquiv.1 hP2