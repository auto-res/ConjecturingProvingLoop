

theorem P1_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A := by
  intro x hxA
  simpa [hA.interior_eq] using (subset_closure hxA)

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P1 A) (hB : P1 B) : P1 (Set.prod A B) := by
  intro p hp
  rcases hp with ⟨hA_mem, hB_mem⟩
  -- `p.1` and `p.2` are in the closures of the interiors.
  have hA_cl : p.1 ∈ closure (interior A) := hA hA_mem
  have hB_cl : p.2 ∈ closure (interior B) := hB hB_mem
  -- Hence `p` is in the closure of `interior A ×ˢ interior B`.
  have h_small : p ∈ closure ((interior A) ×ˢ (interior B)) := by
    have h_prod : p ∈ (closure (interior A)) ×ˢ (closure (interior B)) :=
      ⟨hA_cl, hB_cl⟩
    simpa [closure_prod_eq] using h_prod
  -- Show that `interior A ×ˢ interior B` is contained in `interior (A.prod B)`.
  have h_subset : (interior A ×ˢ interior B) ⊆ interior (Set.prod A B) := by
    apply interior_maximal
    · intro q hq
      rcases hq with ⟨hqA, hqB⟩
      exact ⟨interior_subset hqA, interior_subset hqB⟩
    · exact (isOpen_interior).prod isOpen_interior
  -- Use monotonicity of closure to obtain the desired membership.
  have h_big : p ∈ closure (interior (Set.prod A B)) :=
    (closure_mono h_subset) h_small
  simpa using h_big

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P3 A) (hB : P3 B) : P3 (Set.prod A B) := by
  intro p hp
  -- `p` belongs to `A ×ˢ B`, break the hypothesis.
  rcases hp with ⟨hA_mem, hB_mem⟩
  -- Apply `P3` to each coordinate.
  have hA_int : p.1 ∈ interior (closure A) := hA hA_mem
  have hB_int : p.2 ∈ interior (closure B) := hB hB_mem
  -- `p` lies in the open rectangle below.
  have hp_small : p ∈ (interior (closure A) ×ˢ interior (closure B)) :=
    ⟨hA_int, hB_int⟩
  ----------------------------------------------------------------
  -- 1.  The rectangle is contained in `closure (A ×ˢ B)`.
  ----------------------------------------------------------------
  have h_small_subset_closure :
      (interior (closure A) ×ˢ interior (closure B)) ⊆
        closure (Set.prod A B) := by
    intro q hq
    rcases hq with ⟨hqA_int, hqB_int⟩
    have hqA_cl : q.1 ∈ closure A := interior_subset hqA_int
    have hqB_cl : q.2 ∈ closure B := interior_subset hqB_int
    have hq_mem_prod_closures : q ∈ (closure A) ×ˢ (closure B) :=
      ⟨hqA_cl, hqB_cl⟩
    -- Rewrite using `closure_prod_eq`.
    have h_eq : closure (Set.prod A B) = closure A ×ˢ closure B := by
      simpa using closure_prod_eq
    simpa [h_eq] using hq_mem_prod_closures
  ----------------------------------------------------------------
  -- 2.  Since the rectangle is open, it is contained in the interior
  --     of that closure.
  ----------------------------------------------------------------
  have h_small_subset_interior :
      (interior (closure A) ×ˢ interior (closure B)) ⊆
        interior (closure (Set.prod A B)) := by
    apply interior_maximal h_small_subset_closure
    exact (isOpen_interior).prod isOpen_interior
  ----------------------------------------------------------------
  -- 3.  Conclude that `p` lies in the required interior.
  ----------------------------------------------------------------
  exact h_small_subset_interior hp_small