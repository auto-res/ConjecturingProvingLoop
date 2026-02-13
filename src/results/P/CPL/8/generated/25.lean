

theorem P3_iff_P1_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P3 A ↔ P1 A := by
  refine ⟨?forward, ?backward⟩
  · intro hP3
    intro x hxA
    -- From `P3` we get `x ∈ interior (closure A)`.
    have hx_int : x ∈ interior (closure A) := hP3 hxA
    -- Hence `x ∈ closure A`.
    have hx_cl : x ∈ closure A := interior_subset hx_int
    -- Since `A` is open, `interior A = A`, so
    -- `closure (interior A) = closure A`.
    simpa [hA.interior_eq] using hx_cl
  · intro _hP1
    intro x hxA
    -- Because `A` is open and contained in its closure,
    -- every point of `A` lies in `interior (closure A)`.
    have h_sub : (A : Set X) ⊆ interior (closure A) :=
      interior_maximal subset_closure hA
    exact h_sub hxA