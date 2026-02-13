

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → Topology.P3 A := by
  intro hP2
  have hmono : interior (closure (interior A)) ⊆ interior (closure A) := by
    apply interior_mono
    apply closure_mono
    exact interior_subset
  exact Set.Subset.trans hP2 hmono

theorem P1_iff_P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) : Topology.P1 A ↔ Topology.P3 A := by
  -- From the density hypothesis we have `P2 A`.
  have hP2 : Topology.P2 A := P2_of_dense_interior (X := X) h
  -- Hence `P3 A` and `P1 A` follow.
  have hP3 : Topology.P3 A := P2_implies_P3 (X := X) hP2
  have hP1 : Topology.P1 A := P2_implies_P1 hP2
  -- Establish the desired equivalence.
  exact ⟨fun _ => hP3, fun _ => hP1⟩

theorem exists_closed_superset_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ F : Set X, IsClosed F ∧ A ⊆ F ∧ Topology.P2 F := by
  refine ⟨(Set.univ : Set X), isClosed_univ, ?_, ?_⟩
  · intro _ _
    simp
  · dsimp [Topology.P2]
    intro x hx
    simpa [interior_univ, closure_univ] using hx

theorem P2_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P2 A) (hB : Topology.P2 B) : Topology.P2 (Set.prod A B) := by
  -- Unfold the definition of `P2` in the hypotheses and in the goal.
  dsimp [Topology.P2] at hA hB ⊢
  -- Take an arbitrary point of `A × B`.
  intro p hp
  -- Split that point into its two coordinates.
  rcases p with ⟨x, y⟩
  rcases hp with ⟨hx, hy⟩
  -- Apply the hypotheses to each coordinate.
  have hx' : x ∈ interior (closure (interior A)) := hA hx
  have hy' : y ∈ interior (closure (interior B)) := hB hy
  -- The point lies in the product of the two interior‐closures.
  have hxy :
      (x, y) ∈
        (interior (closure (interior A))).prod
        (interior (closure (interior B))) :=
    ⟨hx', hy'⟩
  -- This product set is open.
  have h_open :
      IsOpen ((interior (closure (interior A))).prod
              (interior (closure (interior B)))) :=
    (isOpen_interior).prod isOpen_interior
  -- Show that this open set is contained in the closure of
  -- `interior (A × B)`.
  have hsubset_to_closure :
      (interior (closure (interior A))).prod
        (interior (closure (interior B)))
        ⊆ closure (interior (A.prod B)) := by
    -- First enlarge to the product of the closures.
    have h1 :
        (interior (closure (interior A))).prod
          (interior (closure (interior B))) ⊆
        (closure (interior A)).prod (closure (interior B)) := by
      intro p hp
      rcases hp with ⟨hp1, hp2⟩
      exact And.intro (interior_subset hp1) (interior_subset hp2)
    -- Identify the latter set with a closure of a product.
    have h2 :
        (closure (interior A)).prod (closure (interior B)) =
          closure ((interior A).prod (interior B)) := by
      simpa using
        (closure_prod_eq (s := interior A) (t := interior B)).symm
    -- Relate the interior of a product.
    have h3 :
        interior (A.prod B) = (interior A).prod (interior B) := by
      simpa using interior_prod_eq (s := A) (t := B)
    -- Combine the inclusions.
    intro p hp
    have hp₁ : p ∈ (closure (interior A)).prod (closure (interior B)) :=
      h1 hp
    have hp₂ : p ∈ closure ((interior A).prod (interior B)) := by
      simpa [h2] using hp₁
    simpa [h3] using hp₂
  -- Use `interior_maximal` to pass from the closure to its interior.
  have hsubset :
      (interior (closure (interior A))).prod
        (interior (closure (interior B)))
        ⊆ interior (closure (interior (A.prod B))) :=
    interior_maximal hsubset_to_closure h_open
  -- Conclude by applying the inclusion to the point `hxy`.
  exact hsubset hxy