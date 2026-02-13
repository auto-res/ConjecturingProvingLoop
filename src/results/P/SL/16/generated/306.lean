

theorem Topology.closure_interior_diff_subset_closure_interior_diff
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A \ B)) ⊆ closure (interior A) \ interior B := by
  classical
  intro x hx
  -- `interior (A \ B) ⊆ interior A`
  have hInt : interior (A \ B) ⊆ interior A := by
    have : (A \ B : Set X) ⊆ A := by
      intro y hy; exact hy.1
    exact interior_mono this
  -- Hence `x ∈ closure (interior A)`
  have hx₁ : x ∈ closure (interior A) :=
    (closure_mono hInt) hx
  -- Show that `x ∉ interior B`
  have hx₂ : x ∉ interior B := by
    intro hxIntB
    -- Use the characterization of points in the closure
    have hOpen : IsOpen (interior B) := isOpen_interior
    have hNonempty :
        ((interior B) ∩ interior (A \ B) : Set X).Nonempty :=
      (mem_closure_iff.1 hx) (interior B) hOpen hxIntB
    rcases hNonempty with ⟨y, ⟨hyIntB, hyIntDiff⟩⟩
    -- Contradiction: `y ∈ B` and `y ∉ B`
    have hInB : (y : X) ∈ B := interior_subset hyIntB
    have hInDiff : (y : X) ∈ A \ B := interior_subset hyIntDiff
    exact (hInDiff.2 hInB)
  exact And.intro hx₁ hx₂