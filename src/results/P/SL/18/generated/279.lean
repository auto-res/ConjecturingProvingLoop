

theorem P3_inter_open_left {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hOpenA : IsOpen (A : Set X)) (hP3B : Topology.P3 B) :
    Topology.P3 (A ∩ B) := by
  -- Swap the factors and reuse the existing right‐hand variant.
  have h := Topology.P3_inter_open_right (A := B) (B := A) hP3B hOpenA
  simpa [Set.inter_comm] using h