

theorem isOpen_diff_closed_imp_P1 {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsClosed B) :
    Topology.P1 (A \ B) := by
  -- `A \ B` can be written as the intersection of the open set `A`
  -- and the open complement of the closed set `B`.
  have hOpenDiff : IsOpen (A \ B) := by
    -- The complement of a closed set is open.
    have hOpenCompl : IsOpen (Bᶜ) := by
      simpa using (isOpen_compl_iff).2 hB
    -- The intersection of two open sets is open.
    simpa [Set.diff_eq] using hA.inter hOpenCompl
  -- Any open set satisfies `P1`.
  simpa using
    Topology.isOpen_imp_P1 (X := X) (A := A \ B) hOpenDiff