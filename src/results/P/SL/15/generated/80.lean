

theorem P3_subset_interior_closure_of_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (hP3 : Topology.P3 A) :
    A ⊆ interior (closure B) := by
  intro x hxA
  -- From `P3`, the point `x` belongs to `interior (closure A)`.
  have hx_intA : x ∈ interior (closure A) := hP3 hxA
  -- Since `A ⊆ B`, we have `closure A ⊆ closure B`.
  have h_closure_mono : closure A ⊆ closure B := closure_mono hAB
  -- Taking interiors preserves inclusion.
  have h_int_mono : interior (closure A) ⊆ interior (closure B) :=
    interior_mono h_closure_mono
  exact h_int_mono hx_intA