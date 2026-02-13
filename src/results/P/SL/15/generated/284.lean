

theorem P2_prod_closure_of_isOpen
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y}
    (hA : IsOpen (closure A)) (hB : IsOpen (closure B)) :
    Topology.P2 (closure A ×ˢ closure B) := by
  -- Each open closure separately satisfies `P2`.
  have hP2A : Topology.P2 (closure A) :=
    Topology.isOpen_implies_P2 (X := X) (A := closure A) hA
  have hP2B : Topology.P2 (closure B) :=
    Topology.isOpen_implies_P2 (X := Y) (A := closure B) hB
  -- Combine them via the product rule for `P2`.
  simpa using
    (Topology.P2_prod
      (X := X) (Y := Y)
      (A := closure A) (B := closure B) hP2A hP2B)