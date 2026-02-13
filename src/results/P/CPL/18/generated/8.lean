

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P1 A) (hB : Topology.P1 B) : Topology.P1 (Set.prod A B) := by
  dsimp [Topology.P1] at hA hB ⊢
  intro p hp
  rcases p with ⟨x, y⟩
  rcases hp with ⟨hx, hy⟩
  -- apply the hypotheses to each coordinate
  have hx' : x ∈ closure (interior A) := hA hx
  have hy' : y ∈ closure (interior B) := hB hy
  -- point belongs to the product of the two closures
  have hxy_prod : (x, y) ∈ (closure (interior A)).prod (closure (interior B)) :=
    ⟨hx', hy'⟩
  -- rewrite using `closure_prod_eq`
  have hxy_closure : (x, y) ∈ closure ((interior A).prod (interior B)) := by
    -- `closure_prod_eq` is `closure (s.prod t) = (closure s).prod (closure t)`
    -- so we use its symmetric form
    have hEq :=
      (closure_prod_eq (s := interior A) (t := interior B)).symm
    simpa using (hEq ▸ hxy_prod)
  -- identify the interior of the product
  have hInt :
      interior (A.prod B) = (interior A).prod (interior B) := by
    simpa using interior_prod_eq (s := A) (t := B)
  -- final rewriting to reach the desired set
  simpa [hInt] using hxy_closure

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P3 A) (hB : Topology.P3 B) : Topology.P3 (Set.prod A B) := by
  -- Unfold the definition of `P3` in the hypotheses and in the goal.
  dsimp [Topology.P3] at hA hB ⊢
  -- Take an arbitrary point of `A × B`.
  intro p hp
  -- Split that point into its two coordinates.
  rcases p with ⟨x, y⟩
  rcases hp with ⟨hx, hy⟩
  -- Apply the hypotheses to each coordinate.
  have hx' : x ∈ interior (closure A) := hA hx
  have hy' : y ∈ interior (closure B) := hB hy
  -- The point lies in the product of the two interior‐closures.
  have hxy :
      (x, y) ∈ (interior (closure A)).prod (interior (closure B)) := by
    exact ⟨hx', hy'⟩
  -- This product set is open.
  have h_open :
      IsOpen ((interior (closure A)).prod (interior (closure B))) :=
    (isOpen_interior).prod isOpen_interior
  -- Show that this open set is contained in the closure of `A × B`.
  have hsubset_to_closure :
      (interior (closure A)).prod (interior (closure B))
        ⊆ closure (A.prod B) := by
    intro q hq
    -- First enlarge to the product of the closures.
    have hq_in :
        q ∈ (closure A).prod (closure B) := by
      rcases hq with ⟨hq1, hq2⟩
      exact ⟨interior_subset hq1, interior_subset hq2⟩
    -- Identify the latter set with a closure of a product.
    have hEq :
        (closure A).prod (closure B) = closure (A.prod B) := by
      simpa using (closure_prod_eq (s := A) (t := B)).symm
    simpa [hEq] using hq_in
  -- Use `interior_maximal` to pass from the closure to its interior.
  have hsubset :
      (interior (closure A)).prod (interior (closure B))
        ⊆ interior (closure (A.prod B)) :=
    interior_maximal hsubset_to_closure h_open
  -- Conclude by applying the inclusion to the point `hxy`.
  exact hsubset hxy

theorem P1_Union {X : Type*} [TopologicalSpace X] {ι : Type*} {A : ι → Set X} (hA : ∀ i, Topology.P1 (A i)) : Topology.P1 (⋃ i, A i) := by
  -- Unfold the definition of `P1` in the hypotheses and goal.
  dsimp [Topology.P1] at hA ⊢
  -- Take an arbitrary point of the union.
  intro x hx
  -- Extract the index witnessing that `x` belongs to one of the sets.
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  -- Apply the hypothesis for this index.
  have hx' : x ∈ closure (interior (A i)) := hA i hxAi
  -- Relate the two closures that appear.
  have hsubset : closure (interior (A i)) ⊆ closure (interior (⋃ i, A i)) := by
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  -- Conclude by the inclusion.
  exact hsubset hx'

theorem P3_bUnion {X ι : Type*} [TopologicalSpace X] {s : Set ι} {A : ι → Set X} (hA : ∀ i ∈ s, Topology.P3 (A i)) : Topology.P3 (⋃ i ∈ s, A i) := by
  dsimp [Topology.P3] at hA ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx⟩
  rcases Set.mem_iUnion.1 hx with ⟨his, hxAi⟩
  have hP3i : Topology.P3 (A i) := hA i his
  have hx' : x ∈ interior (closure (A i)) := hP3i hxAi
  have hsubset : interior (closure (A i)) ⊆ interior (closure (⋃ j ∈ s, A j)) := by
    apply interior_mono
    apply closure_mono
    intro y hy
    -- show `y` belongs to the big union
    have : y ∈ ⋃ j ∈ s, A j := by
      apply Set.mem_iUnion.2
      exact ⟨i, Set.mem_iUnion.2 ⟨his, hy⟩⟩
    exact this
  exact hsubset hx'