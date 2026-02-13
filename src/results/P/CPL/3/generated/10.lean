

theorem P2_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P2 A) (hB : P2 B) : P2 (Set.prod A B) := by
  intro p hp
  -- Decompose the point `p` and the hypothesis that it lies in `A ×ˢ B`.
  rcases hp with ⟨hA_mem, hB_mem⟩
  ----------------------------------------------------------------
  -- 1.  Apply `P2` to both coordinates.
  ----------------------------------------------------------------
  have hA_int : p.1 ∈ interior (closure (interior A)) := hA hA_mem
  have hB_int : p.2 ∈ interior (closure (interior B)) := hB hB_mem
  have hp_small :
      p ∈ (interior (closure (interior A)) ×ˢ
             interior (closure (interior B))) := by
    exact ⟨hA_int, hB_int⟩
  ----------------------------------------------------------------
  -- 2.  The rectangle above is contained in the interior of
  --     `closure (interior A ×ˢ interior B)`.
  ----------------------------------------------------------------
  have h_small_subset_closure :
      (interior (closure (interior A)) ×ˢ
        interior (closure (interior B))) ⊆
        closure (Set.prod (interior A) (interior B)) := by
    intro q hq
    rcases hq with ⟨hqA, hqB⟩
    have hqA_cl : q.1 ∈ closure (interior A) := interior_subset hqA
    have hqB_cl : q.2 ∈ closure (interior B) := interior_subset hqB
    have hq_mem : q ∈ closure (interior A) ×ˢ closure (interior B) :=
      ⟨hqA_cl, hqB_cl⟩
    have h_eq :
        closure (Set.prod (interior A) (interior B)) =
          closure (interior A) ×ˢ closure (interior B) := by
      simpa using closure_prod_eq
    simpa [h_eq] using hq_mem
  have h_small_subset_int_closure :
      (interior (closure (interior A)) ×ˢ
        interior (closure (interior B))) ⊆
        interior (closure (Set.prod (interior A) (interior B))) := by
    apply interior_maximal h_small_subset_closure
    exact (isOpen_interior).prod isOpen_interior
  ----------------------------------------------------------------
  -- 3.  Relate the two closures through monotonicity.
  ----------------------------------------------------------------
  have h_inner_subset :
      Set.prod (interior A) (interior B) ⊆ interior (Set.prod A B) := by
    apply interior_maximal
    · intro q hq
      rcases hq with ⟨hqA, hqB⟩
      exact ⟨interior_subset hqA, interior_subset hqB⟩
    · exact (isOpen_interior).prod isOpen_interior
  have h_closure_subset :
      closure (Set.prod (interior A) (interior B)) ⊆
        closure (interior (Set.prod A B)) :=
    closure_mono h_inner_subset
  have h_int_closure_subset :
      interior (closure (Set.prod (interior A) (interior B))) ⊆
        interior (closure (interior (Set.prod A B))) := by
    apply interior_mono
    exact h_closure_subset
  ----------------------------------------------------------------
  -- 4.  Combine the inclusions and finish.
  ----------------------------------------------------------------
  have h_big :
      (interior (closure (interior A)) ×ˢ
        interior (closure (interior B))) ⊆
        interior (closure (interior (Set.prod A B))) :=
    Set.Subset.trans h_small_subset_int_closure h_int_closure_subset
  exact h_big hp_small