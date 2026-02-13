

theorem P3_inter_interior {X : Type*} [TopologicalSpace X] (A B : Set X) :
    Topology.P3 (interior (A : Set X) ∩ interior B) := by
  have hA : IsOpen (interior (A : Set X)) := isOpen_interior
  have hB : IsOpen (interior (B : Set X)) := isOpen_interior
  simpa using
    (Topology.P3_inter_of_isOpen
        (A := interior (A : Set X)) (B := interior (B : Set X)) hA hB)