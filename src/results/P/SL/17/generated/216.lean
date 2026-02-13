

theorem Topology.P3_diff_isClosed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP3A : Topology.P3 A) (hClosedB : IsClosed B) :
    Topology.P3 (A \ B) := by
  -- The complement of a closed set is open.
  have hOpenBc : IsOpen (Bᶜ) := hClosedB.isOpen_compl
  -- Apply the existing intersection lemma for `P3` with an open set.
  have h := Topology.P3_inter_isOpen_right (A := A) (B := Bᶜ) hP3A hOpenBc
  -- Rewrite `A ∩ Bᶜ` as `A \ B`.
  simpa [Set.diff_eq] using h