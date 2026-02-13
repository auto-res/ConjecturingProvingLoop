

theorem P3_inter_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    Topology.P3 (A ∩ B) := by
  -- The intersection of two open sets is open.
  have hOpen : IsOpen (A ∩ B) := hA.inter hB
  -- Every open set satisfies `P3`.
  simpa using Topology.P3_of_open (A := A ∩ B) hOpen