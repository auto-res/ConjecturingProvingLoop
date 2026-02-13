

theorem Topology.interiorClosure_nonempty_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hA : A.Nonempty) :
    (interior (closure A)).Nonempty := by
  -- First, obtain a point in `interior A` using `P1`.
  have hIntA : (interior A).Nonempty :=
    Topology.interior_nonempty_of_P1 (A := A) hP1 hA
  -- The inclusion `interior A ⊆ interior (closure A)` moves this point into the desired set.
  have hIncl : interior A ⊆ interior (closure A) :=
    Topology.interior_subset_interiorClosure (A := A)
  rcases hIntA with ⟨x, hx⟩
  exact ⟨x, hIncl hx⟩