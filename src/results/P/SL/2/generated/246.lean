

theorem Topology.P1_nonempty_implies_interior_closure_nonempty {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → A.Nonempty → (interior (closure A)).Nonempty := by
  intro hP1 hA_nonempty
  -- Obtain a point in `interior A` using the existing lemma.
  have hIntA : (interior A).Nonempty :=
    Topology.P1_nonempty_implies_interior_nonempty (A := A) hP1 hA_nonempty
  rcases hIntA with ⟨x, hxIntA⟩
  -- Since `interior A ⊆ interior (closure A)`, the same point lies in
  -- `interior (closure A)`.
  have hsubset :
      (interior A : Set X) ⊆ interior (closure A) :=
    Topology.interior_subset_interior_closure (A := A)
  exact ⟨x, hsubset hxIntA⟩