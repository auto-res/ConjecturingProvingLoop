

theorem Topology.closure_image_eq_closure_image_interior_of_P2
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : Continuous f) {A : Set X} (hA : Topology.P2 (X := X) A) :
    closure (f '' (A : Set X)) = closure (f '' interior A) := by
  -- First, upgrade the assumption `P2 A` to `P1 A`.
  have hP1 : Topology.P1 (X := X) A :=
    Topology.P2_implies_P1 (X := X) (A := A) hA
  -- Invoke the existing equality for sets satisfying `P1`.
  exact
    Topology.closure_image_eq_closure_image_interior_of_P1
      (X := X) (Y := Y) (f := f) hf (A := A) hP1