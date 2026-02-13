

theorem isOpen_diff_closed_imp_P2 {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsClosed B) :
    Topology.P2 (A \ B) := by
  -- `A \ B` is the intersection of two open sets: `A` and `Bᶜ`.
  have hOpenDiff : IsOpen (A \ B) := by
    -- The complement of a closed set is open.
    have hOpenCompl : IsOpen (Bᶜ) := by
      simpa using (isOpen_compl_iff).2 hB
    -- The intersection of two open sets is open.
    simpa [Set.diff_eq] using hA.inter hOpenCompl
  -- Any open set satisfies `P2`.
  simpa using
    Topology.isOpen_imp_P2 (X := X) (A := A \ B) hOpenDiff