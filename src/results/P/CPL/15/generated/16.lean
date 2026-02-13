

theorem closure_eq_univ_of_P1_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h : P1 A) (h_dense : closure (interior A) = Set.univ) : closure A = Set.univ := by
  apply Set.Subset.antisymm
  · intro x _; simp
  ·
    have : (closure (interior A) : Set X) ⊆ closure A :=
      closure_mono (interior_subset : (interior A : Set X) ⊆ A)
    simpa [h_dense] using this

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P1 A) (hB : P1 B) : P1 (A ×ˢ B) := by
  intro p hp
  rcases p with ⟨x, y⟩
  -- `x` and `y` belong to `A` and `B`
  have hxA : x ∈ A := hp.1
  have hyB : y ∈ B := hp.2
  -- use the `P1` hypotheses
  have hx_cl : x ∈ closure (interior A) := hA hxA
  have hy_cl : y ∈ closure (interior B) := hB hyB
  -- `(x, y)` is in the closure of `interior A × interior B`
  have hxy_cl_prod :
      ((x, y) : X × Y) ∈ closure (interior A ×ˢ interior B) := by
    -- thanks to `closure_prod_eq`
    have : ((x, y) : X × Y) ∈ closure (interior A) ×ˢ closure (interior B) :=
      And.intro hx_cl hy_cl
    simpa [closure_prod_eq] using this
  -- relate the two closures
  have h_subset :
      (closure (interior A ×ˢ interior B) : Set (X × Y)) ⊆
        closure (interior (A ×ˢ B)) := by
    -- first, an inclusion at the level of interiors
    have h_inner_subset :
        (interior A ×ˢ interior B : Set (X × Y)) ⊆ interior (A ×ˢ B) := by
      intro w hw
      have h_open : IsOpen (interior A ×ˢ interior B) :=
        isOpen_interior.prod isOpen_interior
      have h_sub : (interior A ×ˢ interior B : Set (X × Y)) ⊆ A ×ˢ B :=
        Set.prod_mono interior_subset interior_subset
      exact mem_interior.2 ⟨_, h_sub, h_open, hw⟩
    -- take closures on both sides
    exact closure_mono h_inner_subset
  -- conclude that `(x, y)` is in the desired closure
  exact h_subset hxy_cl_prod