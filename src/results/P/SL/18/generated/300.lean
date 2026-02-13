

theorem P3_diff_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP3A : Topology.P3 A) (hB_closed : IsClosed B) :
    Topology.P3 (A \ B) := by
  -- The complement of a closed set is open.
  have hOpenCompl : IsOpen (Bᶜ : Set X) := hB_closed.isOpen_compl
  -- Apply the intersection lemma with the open complement.
  have hP3_inter :
      Topology.P3 (A ∩ Bᶜ : Set X) :=
    Topology.P3_inter_open_right (A := A) (B := Bᶜ) hP3A hOpenCompl
  simpa [Set.diff_eq] using hP3_inter