

theorem P2_inter_interior {X : Type*} [TopologicalSpace X] (A B : Set X) :
    Topology.P2 (interior (A : Set X) ∩ interior B) := by
  -- Both `interior A` and `interior B` are open sets.
  have hA : IsOpen (interior (A : Set X)) := isOpen_interior
  have hB : IsOpen (interior (B : Set X)) := isOpen_interior
  -- Apply the lemma for the intersection of two open sets.
  simpa using
    (Topology.P2_inter_of_isOpen
        (A := interior (A : Set X)) (B := interior (B : Set X)) hA hB)