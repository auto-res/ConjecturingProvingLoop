

theorem P2_subset_interior_closure_of_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) (hP2 : Topology.P2 A) :
    A ⊆ interior (closure B) := by
  intro x hxA
  -- From `P2`, the point `x` lies in `interior (closure (interior A))`.
  have hx_int : x ∈ interior (closure (interior A)) := hP2 hxA
  -- Since `A ⊆ B`, the interior of `A` is included in `B`.
  have h_int_subset : interior A ⊆ B := by
    intro y hyInt
    have : y ∈ A := interior_subset hyInt
    exact hAB this
  -- Taking closures preserves inclusion.
  have h_closure_subset : closure (interior A) ⊆ closure B :=
    closure_mono h_int_subset
  -- Taking interiors preserves inclusion as well.
  have h_int_mono : interior (closure (interior A)) ⊆ interior (closure B) :=
    interior_mono h_closure_subset
  -- Conclude the desired membership.
  exact h_int_mono hx_int