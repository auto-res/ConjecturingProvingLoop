

theorem P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P3 A := by
  intro x hxA
  -- Since `A` is open, its interior equals itself
  have hxInt : x ∈ interior A := by
    simpa [hA.interior_eq] using hxA
  -- The interior of `A` is contained in the interior of its closure
  have hsubset : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  exact hsubset hxInt

theorem P2_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : Topology.P2 A → Topology.P2 B → Topology.P2 (Set.prod A B) := by
  intro hP2A hP2B
  intro p hp
  rcases p with ⟨x, y⟩
  have hxA : x ∈ A := hp.1
  have hyB : y ∈ B := hp.2
  have hx_int : x ∈ interior (closure (interior A)) := hP2A hxA
  have hy_int : y ∈ interior (closure (interior B)) := hP2B hyB
  -- Define the open rectangle containing `(x, y)`
  let R : Set (X × Y) :=
      (interior (closure (interior A))) ×ˢ
        (interior (closure (interior B)))
  have h_mem_R : (x, y) ∈ R := by
    dsimp [R]
    exact ⟨hx_int, hy_int⟩
  -- `R` is open
  have hR_open : IsOpen R := by
    dsimp [R]
    exact (isOpen_interior).prod isOpen_interior
  -- We will show `R ⊆ closure (interior (A ×ˢ B))`
  have hR_subset : R ⊆ closure (interior (A ×ˢ B)) := by
    intro q hqR
    dsimp [R] at hqR
    -- Put `q` in `closure ((interior A) ×ˢ (interior B))`
    have hq_prod :
        q ∈ (closure (interior A)) ×ˢ (closure (interior B)) := by
      exact
        ⟨ (interior_subset :
              interior (closure (interior A)) ⊆
                closure (interior A)) hqR.1,
          (interior_subset :
              interior (closure (interior B)) ⊆
                closure (interior B)) hqR.2 ⟩
    -- Identify this product with the closure of a product
    have h_closure_prod :
        closure ((interior A) ×ˢ (interior B)) =
          (closure (interior A)) ×ˢ (closure (interior B)) := by
      simpa using
        (closure_prod_eq :
          closure ((interior A) ×ˢ (interior B)) =
            (closure (interior A)) ×ˢ (closure (interior B)))
    have hq_in_closure_prod :
        q ∈ closure ((interior A) ×ˢ (interior B)) := by
      simpa [h_closure_prod] using hq_prod
    -- Show that this closure is contained in `closure (interior (A ×ˢ B))`
    have h_int_subset :
        (interior A) ×ˢ (interior B) ⊆ interior (A ×ˢ B) := by
      intro r hr
      -- The rectangle is open and contained in `A ×ˢ B`
      have h_open_rect : IsOpen ((interior A) ×ˢ (interior B)) :=
        (isOpen_interior).prod isOpen_interior
      have h_rect_subset :
          ((interior A) ×ˢ (interior B)) ⊆ A ×ˢ B := by
        intro s hs
        exact ⟨ (interior_subset : interior A ⊆ A) hs.1,
                (interior_subset : interior B ⊆ B) hs.2 ⟩
      have h_to_int :
          ((interior A) ×ˢ (interior B)) ⊆ interior (A ×ˢ B) :=
        interior_maximal h_rect_subset h_open_rect
      exact h_to_int hr
    have h_closure_mono :
        closure ((interior A) ×ˢ (interior B)) ⊆
          closure (interior (A ×ˢ B)) :=
      closure_mono h_int_subset
    exact h_closure_mono hq_in_closure_prod
  -- An open set contained in a closure lies inside its interior
  have hR_interior :
      R ⊆ interior (closure (interior (A ×ˢ B))) :=
    interior_maximal hR_subset hR_open
  exact hR_interior h_mem_R

theorem P3_iUnion {ι : Sort*} {X : Type*} [TopologicalSpace X] {f : ι → Set X} : (∀ i, Topology.P3 (f i)) → Topology.P3 (⋃ i, f i) := by
  intro hP3
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hx_int : x ∈ interior (closure (f i)) := hP3 i hxi
  have hsubset : interior (closure (f i)) ⊆ interior (closure (⋃ j, f j)) := by
    have h_closure_subset : closure (f i) ⊆ closure (⋃ j, f j) := by
      have h_subset : (f i : Set X) ⊆ ⋃ j, f j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact closure_mono h_subset
    exact interior_mono h_closure_subset
  exact hsubset hx_int

theorem P1_existence_of_dense_open {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → ∃ U, IsOpen U ∧ closure U = closure A := by
  intro hP1
  refine ⟨interior A, isOpen_interior, ?_⟩
  apply subset_antisymm
  ·
    exact closure_mono (interior_subset : (interior A) ⊆ A)
  ·
    have h_closed : IsClosed (closure (interior A)) := isClosed_closure
    exact closure_minimal hP1 h_closed