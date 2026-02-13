

theorem Topology.interior_nonempty_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X := X) A) (hA : A.Nonempty) :
    (interior A).Nonempty := by
  classical
  -- Choose a point `x ∈ A`.
  rcases hA with ⟨x, hxA⟩
  -- By `P1`, this point lies in the closure of `interior A`.
  have hx_cl : x ∈ closure (interior A) := hP1 hxA
  -- Either `interior A` is nonempty or it is empty; handle the two cases.
  by_cases hInt : (interior A).Nonempty
  · exact hInt
  · -- If `interior A = ∅`, then its closure is also `∅`, contradicting `hx_cl`.
    have h_int_empty : interior A = (∅ : Set X) := by
      -- `interior A` has no elements, hence equals `∅`.
      by_contra hNe
      have : (interior A).Nonempty := (Set.nonempty_iff_ne_empty).2 hNe
      exact (hInt this)
    -- From this, the closure is also empty.
    have h_cl_empty : closure (interior A) = (∅ : Set X) := by
      simpa [h_int_empty, closure_empty]
    -- Derive the contradiction.
    have : x ∈ (∅ : Set X) := by
      simpa [h_cl_empty] using hx_cl
    exact this.elim