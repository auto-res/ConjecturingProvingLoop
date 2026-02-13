

theorem Topology.closure_interior_closure_eq_closure_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → closure (interior (closure A)) = closure (interior A) := by
  intro hP2
  -- `P2` implies `P1`, giving an equality between the corresponding interiors
  have hP1 : Topology.P1 (A := A) := Topology.P2_implies_P1 (A := A) hP2
  have hIntEq :=
    Topology.interior_closure_eq_interior_closure_interior_of_P1 (A := A) hP1
  -- Rewrite the goal using `hIntEq`
  have hClosEq :
      closure (interior (closure A)) =
        closure (interior (closure (interior A))) := by
    simpa [hIntEq]
  -- Conclude with the previously established equality
  calc
    closure (interior (closure A))
        = closure (interior (closure (interior A))) := hClosEq
    _ = closure (interior A) :=
      Topology.closure_interior_closure_interior_eq_closure_interior (A := A)