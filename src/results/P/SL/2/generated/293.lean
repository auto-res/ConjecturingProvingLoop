

theorem Topology.isOpen_diff_isClosed_right_implies_P2 {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    IsOpen A → IsClosed (B : Set X) → Topology.P2 (A \ B) := by
  intro hOpenA hClosedB
  -- `A \ B` is open since it is the intersection of the open set `A`
  -- with the open complement of the closed set `B`.
  have hOpenDiff : IsOpen (A \ B : Set X) := by
    have hOpenComplB : IsOpen ((Bᶜ) : Set X) := hClosedB.isOpen_compl
    simpa [Set.diff_eq] using hOpenA.inter hOpenComplB
  -- Any open set satisfies `P2`.
  exact Topology.isOpen_implies_P2 (A := A \ B) hOpenDiff