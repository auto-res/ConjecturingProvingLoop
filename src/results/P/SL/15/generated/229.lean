

theorem P3_prod_closure_of_isOpen
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y}
    (hA : IsOpen (closure A)) (hB : IsOpen (closure B)) :
    Topology.P3 (closure A ×ˢ closure B) := by
  -- Obtain `P3` for each factor from the openness of its closure
  have hP3A : Topology.P3 (closure A) := by
    have hEquiv := (Topology.P3_closure_iff_isOpen_closure (X := X) (A := A))
    exact hEquiv.mpr hA
  have hP3B : Topology.P3 (closure B) := by
    have hEquiv := (Topology.P3_closure_iff_isOpen_closure (X := Y) (A := B))
    exact hEquiv.mpr hB
  -- Combine the two `P3` properties using the product rule
  simpa using
    (Topology.P3_prod
      (X := X) (Y := Y)
      (A := closure A) (B := closure B) hP3A hP3B)