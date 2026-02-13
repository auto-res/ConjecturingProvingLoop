

theorem P2_diff_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP2A : Topology.P2 A) (hB_closed : IsClosed B) :
    Topology.P2 (A \ B) := by
  -- The complement of a closed set is open.
  have hOpenCompl : IsOpen (Bᶜ : Set X) := hB_closed.isOpen_compl
  -- Apply the intersection lemma with the open complement.
  have hInter : Topology.P2 (A ∩ Bᶜ) :=
    Topology.P2_inter_open_right (A := A) (B := Bᶜ) hP2A hOpenCompl
  simpa [Set.diff_eq] using hInter