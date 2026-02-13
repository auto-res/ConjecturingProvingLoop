

theorem isOpen_diff_closed_imp_P3 {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsClosed B) :
    Topology.P3 (A \ B) := by
  have hOpenDiff : IsOpen (A \ B) := by
    -- The complement of a closed set is open.
    have hOpenCompl : IsOpen (Bᶜ) := by
      simpa using (isOpen_compl_iff).2 hB
    -- `A \ B` is the intersection of two open sets.
    simpa [Set.diff_eq] using hA.inter hOpenCompl
  -- Any open set satisfies `P3`.
  simpa using
    Topology.isOpen_imp_P3 (X := X) (A := A \ B) hOpenDiff