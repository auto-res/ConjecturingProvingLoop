

theorem P1_prod_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : IsOpen A) (hB : IsOpen B) :
    Topology.P1 (Set.prod A B) := by
  have hOpen : IsOpen (Set.prod A B) := hA.prod hB
  simpa using Topology.P1_of_open (A := Set.prod A B) hOpen