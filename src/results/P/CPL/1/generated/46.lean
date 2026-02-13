

theorem P1_of_P3_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (h : P3 A) : P1 A := by
  intro x hx
  -- From `P3`, `x` lies in the interior of `closure A`, which equals `interior A`
  -- because `A` is closed.
  have hx_int : x ∈ interior A := by
    have : x ∈ interior (closure A) := h hx
    simpa [hA.closure_eq] using this
  -- The closure of `interior A` contains `x`.
  exact subset_closure hx_int

theorem P1_of_P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : P1 (interior A) := by
  -- First, obtain `P2` for `interior A` from the given hypothesis.
  have hP2 : P2 (interior A) := P2_interior (A := A) h
  -- Convert this `P2` statement to `P1`.
  exact P1_of_P2 (A := interior A) hP2

theorem P2_Union_homeomorph_fibers {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) : P2 (⋃ y, e ⁻¹' {y}) := by
  -- The union of all fibres of `e` is the whole space.
  have h_eq : (⋃ y : Y, e ⁻¹' ({y} : Set Y)) = (Set.univ : Set X) := by
    ext x
    constructor
    · intro _; simp
    · intro _; 
      have hx : x ∈ e ⁻¹' ({e x} : Set Y) := by
        simp
      exact Set.mem_iUnion.2 ⟨e x, hx⟩
  -- Conclude using the fact that `P2` holds for `Set.univ`.
  simpa [h_eq] using (P2_univ (X := X))