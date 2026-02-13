

theorem P2_open_iff_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A ↔ P3 A := by
  -- Since `A` is open, its interior is itself.
  have hInt : interior A = A := hA.interior_eq
  -- Consequently, the two closures that appear in the definitions coincide.
  have hCl : closure (interior A) = closure A := by
    simpa [hInt]
  constructor
  · intro hP2
    exact P2_subset_P3 (A := A) hP2
  · intro hP3
    intro x hxA
    -- From `P3` we get that `x` lies in `interior (closure A)`.
    have hx_int : x ∈ interior (closure A) := hP3 hxA
    -- Rewrite with `hCl` to obtain the required conclusion.
    simpa [hCl] using hx_int

theorem P3_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = Set.univ) : P3 (closure A) := by
  -- First, prove that `closure (interior (closure A)) = univ`.
  have h_dense' : closure (interior (closure (A : Set X))) = (Set.univ : Set X) := by
    -- `interior A ⊆ interior (closure A)`, hence the corresponding closures satisfy the same inclusion.
    have h_sub :
        (closure (interior A) : Set X) ⊆ closure (interior (closure A)) :=
      closure_mono
        (interior_mono (subset_closure : (A : Set X) ⊆ closure A))
    -- Replace `closure (interior A)` with `univ` using the hypothesis.
    have h_univ_sub : (Set.univ : Set X) ⊆ closure (interior (closure A)) := by
      simpa [h] using h_sub
    -- Use subset antisymmetry to get the equality.
    apply Set.Subset.antisymm
    · intro _ _
      simp
    · exact h_univ_sub
  -- Conclude with the lemma giving `P3` from the denseness of the interior.
  exact P3_of_dense_interior (A := closure A) h_dense'