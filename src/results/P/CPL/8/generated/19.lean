

theorem P2_iff_P1_of_closed_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : IsClosed (interior A)) : P2 A ↔ P1 A := by
  refine ⟨?forward, ?backward⟩
  · intro hP2
    exact P2_to_P1 (A := A) hP2
  · intro hP1
    intro x hxA
    -- Since `interior A` is closed, its closure is itself.
    have h_cl : closure (interior A : Set X) = interior A := h.closure_eq
    -- From `P1`, we obtain `A ⊆ interior A`.
    have h_sub : (A : Set X) ⊆ interior A := by
      intro y hy
      have : y ∈ closure (interior A) := hP1 hy
      simpa [h_cl] using this
    have hx_int : x ∈ interior A := h_sub hxA
    -- Rewriting with `h_cl` finishes the goal.
    simpa [h_cl, interior_interior] using hx_int

theorem P2_sigma {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] {A : ∀ i, Set (X i)} : (∀ i, P2 (A i)) → P2 {p : Σ i, X i | P2 (A p.1)} := by
  intro hAll
  -- The set in question is actually the whole space.
  have h_eq :
      ({p : Sigma X | P2 (A p.1)} : Set (Sigma X)) = Set.univ := by
    ext p
    constructor
    · intro _
      exact Set.mem_univ _
    · intro _
      exact hAll p.1
  -- `P2` holds for `Set.univ`, hence for our set.
  simpa [h_eq.symm] using (P2_univ (X := Sigma X))