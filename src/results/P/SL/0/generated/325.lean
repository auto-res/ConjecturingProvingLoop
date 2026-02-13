

theorem P1_inter_left_of_open {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsOpen (A : Set X) → Topology.P1 B → Topology.P1 (A ∩ B) := by
  intro hOpenA hP1B
  -- Apply the existing “right‐open” lemma after swapping the factors
  have h := Topology.P1_inter_right_of_open (X := X) (A := B) (B := A) hP1B hOpenA
  simpa [Set.inter_comm] using h