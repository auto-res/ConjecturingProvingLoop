

theorem Topology.denseInterior_implies_P1_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hDense : Dense (interior (A : Set X))) :
    Topology.P1 (X := X) (closure (A : Set X)) := by
  -- First, `P1` holds for `A` because the interior of `A` is dense.
  have hP1A : Topology.P1 (X := X) A :=
    Topology.denseInterior_implies_P1 (X := X) (A := A) hDense
  -- `P1` is inherited by the closure of any set that satisfies `P1`.
  exact Topology.P1_implies_P1_closure (X := X) (A := A) hP1A