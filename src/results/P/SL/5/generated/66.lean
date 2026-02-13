

theorem interior_nonempty_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A) (hA : A.Nonempty) :
    (interior A).Nonempty := by
  classical
  by_contra hInt
  -- `interior A` is empty by assumption.
  have hInt_empty : interior (A : Set X) = (∅ : Set X) := by
    simpa using (Set.not_nonempty_iff_eq_empty).1 hInt
  -- Hence `interior (closure (interior A))` is also empty.
  have hInt_closure_empty :
      interior (closure (interior (A : Set X))) = (∅ : Set X) := by
    simp [hInt_empty]
  -- Pick a point of `A`.
  rcases hA with ⟨x, hxA⟩
  -- `P2` says this point lies in `interior (closure (interior A))`,
  -- which we have just shown to be empty: contradiction.
  have hx : x ∈ interior (closure (interior (A : Set X))) := hP2 hxA
  have : x ∈ (∅ : Set X) := by
    simpa [hInt_closure_empty] using hx
  exact this