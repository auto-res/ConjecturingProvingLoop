

theorem interior_closure_nonempty_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → (A : Set X).Nonempty →
      (interior (closure (A : Set X))).Nonempty := by
  intro hP2 hA
  rcases hA with ⟨x, hxA⟩
  -- From `P2` we know `A ⊆ interior (closure A)`.
  have hSub : (A : Set X) ⊆ interior (closure (A : Set X)) :=
    Topology.P2_implies_subset_interior_closure (X := X) (A := A) hP2
  -- The chosen point `x` of `A` therefore lies in `interior (closure A)`.
  exact ⟨x, hSub hxA⟩