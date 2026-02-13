

theorem Topology.P2_diff_isClosed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP2A : Topology.P2 A) (hClosedB : IsClosed B) :
    Topology.P2 (A \ B) := by
  -- The complement of a closed set is open.
  have hOpenBc : IsOpen (Bᶜ) := hClosedB.isOpen_compl
  -- Apply the existing intersection lemma for `P2` with an open set.
  have h := Topology.P2_inter_isOpen_right (A := A) (B := Bᶜ) hP2A hOpenBc
  -- Rewrite `A ∩ Bᶜ` as `A \ B`.
  simpa [Set.diff_eq] using h