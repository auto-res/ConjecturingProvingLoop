

theorem Topology.interior_closure_interior_nonempty_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X := X) A) (hA : A.Nonempty) :
    (interior (closure (interior A))).Nonempty := by
  -- From `P1` and the non‐emptiness of `A`, we know `interior A` is nonempty.
  have hIntA : (interior A).Nonempty :=
    Topology.interior_nonempty_of_P1 (X := X) (A := A) hP1 hA
  -- The inclusion `interior A ⊆ interior (closure (interior A))`.
  have hSubset :
      interior A ⊆ interior (closure (interior A)) :=
    Topology.interior_subset_interior_closure_interior (X := X) (A := A)
  -- Transport the witness of non‐emptiness along this inclusion.
  rcases hIntA with ⟨x, hxIntA⟩
  exact ⟨x, hSubset hxIntA⟩