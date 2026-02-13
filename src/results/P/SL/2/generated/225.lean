

theorem Topology.isClosed_P2_implies_frontier_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsClosed A → Topology.P2 A → frontier (A : Set X) = (∅ : Set X) := by
  intro hClosed hP2
  -- From the premises, `A` is both closed and open.
  have hOpen : IsOpen (A : Set X) :=
    Topology.isClosed_P2_implies_isOpen (A := A) hClosed hP2
  -- Hence `closure A = A` and `interior A = A`.
  have hCl : closure (A : Set X) = A := hClosed.closure_eq
  have hInt : interior (A : Set X) = A := hOpen.interior_eq
  -- Unfold `frontier` and simplify.
  ext x
  simp [frontier, hCl, hInt]