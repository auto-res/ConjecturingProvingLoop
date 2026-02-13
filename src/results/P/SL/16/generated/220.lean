

theorem Topology.open_and_closed_of_interior_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior A = closure A) :
    IsOpen A ∧ IsClosed A := by
  -- First, show that `A` is open.
  have hInt : interior A = A := by
    apply subset_antisymm
    · exact interior_subset
    ·
      have hSub : (A : Set X) ⊆ closure A := subset_closure
      simpa [h] using hSub
  have hOpen : IsOpen A := by
    have hOpenInt : IsOpen (interior A) := isOpen_interior
    simpa [hInt] using hOpenInt
  -- Next, show that `A` is closed.
  have hCl : closure A = A := by
    apply subset_antisymm
    ·
      intro x hx
      have hxInt : x ∈ interior A := by
        simpa [h] using hx
      exact interior_subset hxInt
    · exact subset_closure
  have hClosed : IsClosed A := by
    have : IsClosed (closure A) := isClosed_closure
    simpa [hCl] using this
  exact And.intro hOpen hClosed