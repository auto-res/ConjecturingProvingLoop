

theorem exists_P2_superset_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → ∃ B, A ⊆ B ∧ Topology.P2 B := by
  intro _hP1
  refine ⟨(Set.univ : Set X), Set.subset_univ _, ?_⟩
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P1_iUnion {ι : Sort*} {X : Type*} [TopologicalSpace X] {f : ι → Set X} : (∀ i, Topology.P1 (f i)) → Topology.P1 (⋃ i, f i) := by
  intro hP1
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hx_closure : x ∈ closure (interior (f i)) := hP1 i hxi
  have hsubset : closure (interior (f i)) ⊆ closure (interior (⋃ j, f j)) := by
    have h_int_subset : interior (f i) ⊆ interior (⋃ j, f j) := by
      have h_subset : (f i : Set X) ⊆ ⋃ j, f j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono h_subset
    exact closure_mono h_int_subset
  exact hsubset hx_closure

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : Topology.P3 A → Topology.P3 B → Topology.P3 (Set.prod A B) := by
  intro hP3A hP3B
  intro p hp
  -- Split the point into its coordinates
  rcases p with ⟨x, y⟩
  -- Membership of the coordinates in `A` and `B`
  have hxA : x ∈ A := hp.1
  have hyB : y ∈ B := hp.2
  -- Apply `P3` to get interior points of the closures
  have hx_int : x ∈ interior (closure A) := hP3A hxA
  have hy_int : y ∈ interior (closure B) := hP3B hyB
  -- The open rectangle that contains `(x, y)`
  have h_mem_rect :
      (x, y) ∈ (interior (closure A)) ×ˢ (interior (closure B)) :=
    ⟨hx_int, hy_int⟩
  have h_rect_open :
      IsOpen ((interior (closure A)) ×ˢ (interior (closure B))) :=
    isOpen_interior.prod isOpen_interior
  -- Show the rectangle is contained in `closure (A ×ˢ B)`
  have h_rect_subset :
      (interior (closure A)) ×ˢ (interior (closure B)) ⊆
        closure (A ×ˢ B) := by
    intro q hq
    rcases hq with ⟨hq1, hq2⟩
    -- Each coordinate is in the respective closure
    have hq1_cl : q.1 ∈ closure A :=
      (interior_subset : interior (closure A) ⊆ closure A) hq1
    have hq2_cl : q.2 ∈ closure B :=
      (interior_subset : interior (closure B) ⊆ closure B) hq2
    -- Hence the point is in `closure A ×ˢ closure B`
    have hq_in : q ∈ (closure A) ×ˢ (closure B) := ⟨hq1_cl, hq2_cl⟩
    -- And `closure (A ×ˢ B)` coincides with that product
    have h_eq :
        closure (A ×ˢ B) = (closure A) ×ˢ (closure B) := by
      simpa using
        (closure_prod_eq :
          closure (A ×ˢ B) = (closure A) ×ˢ (closure B))
    simpa [h_eq] using hq_in
  -- An open set contained in a closure lies in the interior
  have h_rect_interior :
      (interior (closure A)) ×ˢ (interior (closure B)) ⊆
        interior (closure (A ×ˢ B)) :=
    interior_maximal h_rect_subset h_rect_open
  -- Finish
  exact h_rect_interior h_mem_rect