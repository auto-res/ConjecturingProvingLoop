

theorem Topology.P1_diff_of_isOpen_of_isClosed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsClosed B) :
    Topology.P1 (A \ B) := by
  -- The complement of a closed set is open.
  have hOpenCompl : IsOpen (Bᶜ) := by
    simpa using (isOpen_compl_iff).2 hB
  -- `A \ B` is the intersection of two open sets, hence open.
  have hOpen : IsOpen (A \ B) := by
    simpa [Set.diff_eq] using hA.inter hOpenCompl
  -- Any open set satisfies `P1`.
  exact Topology.P1_of_isOpen (A := A \ B) hOpen