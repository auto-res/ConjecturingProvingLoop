

theorem Topology.isOpen_diff_isClosed_right_implies_P1 {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    IsOpen A → IsClosed (B : Set X) → Topology.P1 (A \ B) := by
  intro hOpenA hClosedB
  -- `A \ B` is the intersection of two open sets: `A` and `Bᶜ`.
  have hOpenDiff : IsOpen (A \ B : Set X) := by
    have hOpenComplB : IsOpen ((Bᶜ) : Set X) := hClosedB.isOpen_compl
    simpa [Set.diff_eq] using hOpenA.inter hOpenComplB
  -- Any open set satisfies `P1`.
  exact Topology.isOpen_implies_P1 (A := A \ B) hOpenDiff