

theorem P1_prod_closure_of_isOpen
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y}
    (hA : IsOpen (closure A)) (hB : IsOpen (closure B)) :
    Topology.P1 (closure A ×ˢ closure B) := by
  -- The product of two open sets is open.
  have hOpen : IsOpen (closure A ×ˢ closure B) := hA.prod hB
  -- Open sets satisfy `P1`.
  exact
    Topology.isOpen_implies_P1
      (X := X × Y)
      (A := closure A ×ˢ closure B)
      hOpen