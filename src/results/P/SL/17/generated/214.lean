

theorem Topology.P1_diff_isClosed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP1A : Topology.P1 A) (hClosedB : IsClosed B) :
    Topology.P1 (A \ B) := by
  -- The complement of a closed set is open.
  have hOpenBc : IsOpen (Bᶜ) := hClosedB.isOpen_compl
  -- Apply the existing intersection lemma with the open complement.
  have h := Topology.P1_inter_isOpen_right (A := A) (B := Bᶜ) hP1A hOpenBc
  -- Rewrite `A ∩ Bᶜ` as `A \ B`.
  simpa [Set.diff_eq] using h